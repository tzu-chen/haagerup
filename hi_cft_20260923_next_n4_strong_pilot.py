"""Bounded split-prime normal-span/strong-closure pilot; root launches only.

Imports frozen characteristic-zero S2/S3, constructs N4 using normal
products only, and tests S2_0 P3. SQLite transactions bind rows to cursors.
No all-weight, upper-rank, or characteristic-zero containment claim.
"""
import argparse
from collections import OrderedDict
from functools import lru_cache
import gzip
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic
import zlib

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_c8_exact_grade3 as g3
import hi_cft_20260923_proof_exact4 as e4
import hi_cft_20260923_next_grade4_disk as frozen

PRIME = 1000003
AMBIENT = 71052
FORMAT = 'n4-normal-span-prime-v1'
MIB = 1024**2
ROW_BYTES = 8*MIB
ROW_TERMS = 20000
DISK_TERMS = 16000000
CACHE_TERMS = 500000


class Stop(Exception):
    pass


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(MIB), b''):
            h.update(block)
    return h.hexdigest()


def compact(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def pack(value):
    text = compact(value).encode()
    if len(text) > ROW_BYTES:
        raise Stop('8 MiB serialized-record bound')
    return zlib.compress(text, 1)


def unpack(blob):
    decoder = zlib.decompressobj()
    text = decoder.decompress(blob, ROW_BYTES+1)
    assert len(text) <= ROW_BYTES and decoder.eof and not decoder.unconsumed_tail
    return json.loads(text)


def clear_caches():
    x.creation.cache_clear()
    x.vertex.cache_clear()
    x.basis_mode.cache_clear()


def read_inputs(args):
    directory = Path(args.checkpoint)
    manifest = directory/'manifest.json'
    assert manifest.stat().st_size < 8*MIB
    meta = json.loads(manifest.read_text())
    assert meta['format'] == 'exact-cartan-span-v1'
    assert meta['completed_grade3'] and meta['dimensions']['3'] == 956
    assert meta['dimensions']['2'] == 120
    assert any(h['stage'] == 'grade3 translation descendants' and
               h['dimensions']['3'] == 634 for h in meta['history'])
    for path, digest in meta['sources'].items():
        assert sha(path) == digest, ('frozen source changed', path)
    hashes = {str(manifest): sha(manifest)}
    hashes.update(meta['sources'])
    for module in (__file__, g3.__file__, frozen.__file__):
        hashes[str(module)] = sha(module)
    rows, terms = {}, 0
    order3 = meta['order']['3']
    positions = {name: i for i, name in enumerate(order3)}
    assert len(positions) == 956
    for filename in meta['block_files']:
        if not filename.startswith(('grade2_', 'grade3_')):
            continue
        path = directory/filename
        assert sha(path) == meta['files_sha256'][filename]
        hashes[str(path)] = sha(path)
        for row in frozen.row_stream(path):
            vector = {(tuple(a), tuple(o)): x.A(c) for a, o, c in row['vector']}
            vector = {s: c for s, c in vector.items() if c}
            assert vector
            assert all(x.grade(s) == row['grade'] for s in vector)
            assert {x.weight(s) for s in vector} == {tuple(row['weight'])}
            assert vector[min(vector)] == 1
            rows[row['id']] = vector
            terms += len(vector)
            assert terms <= 300000, 'Frozen input sparse-term cap'
            if row['grade'] == 3:
                pos = positions[row['id']]
                recipe = row['recipe']
                assert recipe['op'] == 'mode'
                if recipe['left'] in ('current2', 'current5') and recipe['n'] == 0:
                    assert positions[recipe['right']] < pos
                elif pos < 634:
                    assert ((recipe['left'].startswith('current') and recipe['n'] == -1)
                            or (recipe['left'] == 'omega' and recipe['n'] == 0))
                    assert recipe['right'] in meta['s2_inputs']
                else:
                    assert recipe['left'] in meta['charged_fields'] and recipe['n'] == 0
                    assert recipe['right'] in meta['s2_inputs']
    assert set(rows) == set(meta['order']['2']+order3)
    # Authenticate the definitions referenced by saved row recipes, without
    # materializing the (unused) field array or any grade-four checkpoint.
    field_file = directory/meta['field_file']
    assert sha(field_file) == meta['files_sha256'][meta['field_file']]
    hashes[str(field_file)] = sha(field_file)
    source = Path('hi_cft_20260923_c8_exact_fields.json')
    hashes[str(source)] = sha(source)
    fields = json.loads(source.read_text())['fields']
    operators = [(x.read_field(row), {'kind': 'charged_highest', 'source_index': i,
                                     'dimensions': row['dimensions']})
                 for i, row in enumerate(fields[:-1])]
    neutral = x.read_field(fields[-1])
    complement = x.vadd((1, x.omega()), (-1, x.sugawara(x.LEFT, 1)),
                       (-1, x.sugawara(x.RIGHT, 39)), (-1, neutral))
    operators += [(neutral, {'kind': 'neutral_source_stress', 'source_index': len(fields)-1}),
                  (complement, {'kind': 'omega_minus_two_Sugawaras_minus_neutral'})]
    assert len(operators) == 10
    assert all(all(x.grade(s) == 2 for s in v) for v, _ in operators)
    # The saved order is an exact basis, with its first634 the normal span.
    return meta, rows, operators, hashes, terms


class Database:
    def __init__(self, args, inputs):
        self.args = args
        self.source, self.inputs, self.ops, self.hashes, self.input_terms = inputs
        self.started = self.last_save = monotonic()
        self.output = Path(args.output)
        self.path = self.output.with_suffix('.sqlite')
        self.conn = sqlite3.connect(self.path)
        self.conn.execute('PRAGMA journal_mode=DELETE')
        self.conn.execute('PRAGMA synchronous=FULL')
        self.conn.execute('PRAGMA cache_size=-8192')
        self.conn.execute('PRAGMA temp_store=FILE')
        self.conn.execute('PRAGMA mmap_size=0')
        assert self.conn.execute('PRAGMA page_size').fetchone()[0] == 4096
        self.conn.execute('PRAGMA max_page_count=131072')  #512MiB with default4KiB pages
        self.conn.execute('CREATE TABLE IF NOT EXISTS meta (id INTEGER PRIMARY KEY, value TEXT)')
        self.conn.execute('CREATE TABLE IF NOT EXISTS states (id INTEGER PRIMARY KEY, value TEXT)')
        self.conn.execute('CREATE TABLE IF NOT EXISTS rows (id INTEGER PRIMARY KEY, w0 INTEGER, w1 INTEGER, pivot INTEGER, nnz INTEGER, raw BLOB, reduced BLOB, word TEXT, digest TEXT)')
        self.conn.execute('CREATE TABLE IF NOT EXISTS tests (id INTEGER PRIMARY KEY, stage INTEGER, word TEXT, raw BLOB, residual BLOB, digest TEXT)')
        self.conn.execute('CREATE TABLE IF NOT EXISTS extras (id INTEGER PRIMARY KEY, w0 INTEGER, w1 INTEGER, pivot INTEGER, nnz INTEGER, raw BLOB, reduced BLOB, word TEXT, digest TEXT)')
        self.conn.commit()
        self.states, self.ids, self.weights, self.blocks, self.info = [], {}, [], {}, []
        self.extra_blocks, self.extra_info = {}, []
        self.cache, self.cache_terms = OrderedDict(), 0
        self.requested_stop = None
        saved = self.conn.execute('SELECT value FROM meta WHERE id=1').fetchone()
        if saved:
            self.meta = json.loads(saved[0])
            assert self.meta['format'] == FORMAT and self.meta['source_sha256'] == self.hashes
            assert self.meta['prime'] == PRIME and self.meta['status'] != 'complete'
            for idx, text in self.conn.execute('SELECT id,value FROM states ORDER BY id'):
                assert idx == len(self.states)
                a, o = json.loads(text)
                state = (tuple(a), tuple(o))
                assert x.grade(state) == 4
                self.ids[state] = idx
                self.states.append(state)
                self.weights.append(x.weight(state))
            for idx, w0, w1, pivot, nnz in self.conn.execute('SELECT id,w0,w1,pivot,nnz FROM rows ORDER BY id'):
                assert idx == len(self.info)
                self.info.append(((w0, w1), pivot, nnz))
                assert pivot not in self.blocks.setdefault((w0, w1), {})
                self.blocks[(w0, w1)][pivot] = idx
            assert len(self.info) == self.meta['normal_rank']
            for idx, w0, w1, pivot, nnz in self.conn.execute('SELECT id,w0,w1,pivot,nnz FROM extras ORDER BY id'):
                assert idx == len(self.extra_info)
                self.extra_info.append(((w0, w1), pivot, nnz))
                assert pivot not in self.extra_blocks.setdefault((w0, w1), {})
                self.extra_blocks[(w0, w1)][pivot] = -1-idx
            assert len(self.extra_info) == self.meta['extra_rank']
        else:
            assert not self.conn.execute('SELECT 1 FROM rows LIMIT 1').fetchone()
            assert not self.conn.execute('SELECT 1 FROM states LIMIT 1').fetchone()
            self.meta = {'format': FORMAT, 'source_sha256': self.hashes, 'prime': PRIME,
                         'stage': 0, 'cursor': 0, 'closure_cursor': 0, 'normal_rank': 0,
                         'saved_terms': 0, 'extra_rank': 0, 'candidates': 0, 'tests': 0, 'failures': 0,
                         'failure_witnesses': 0, 'status': 'running', 'history': [],
                         'elapsed_seconds': 0, 'normal_span_complete': False}
        self.small = {}
        for grade, vectors in ((0, [x.VAC]), (1, x.LEFT+x.RIGHT),
                               (2, [self.inputs[i] for i in self.source['order']['2']]),
                               (3, [self.inputs[i] for i in self.source['order']['3']])):
            blocks = {}
            for vector in vectors:
                weight = x.weight(next(iter(vector)))
                out = {s: int(c) for s, c in vector.items()}
                rows = blocks.setdefault(weight, {})
                for pivot in sorted(rows):
                    self.subtract(out, out.get(pivot, 0), rows[pivot])
                assert out
                pivot = min(out)
                inv = pow(out[pivot], -1, PRIME)
                rows[pivot] = {s: c*inv % PRIME for s, c in out.items()}
            self.small[grade] = blocks

    @staticmethod
    def subtract(out, factor, row):
        if factor:
            for i, c in row.items():
                value = (out.get(i, 0)-factor*c) % PRIME
                if value:
                    out[i] = value
                else:
                    out.pop(i, None)

    def intern(self, state):
        idx = self.ids.get(state)
        if idx is None:
            assert x.grade(state) == 4
            idx = len(self.states)
            assert idx < AMBIENT
            self.ids[state] = idx
            self.states.append(state)
            self.weights.append(x.weight(state))
            self.conn.execute('INSERT INTO states VALUES (?,?)', (idx, compact(state)))
        return idx

    def row(self, idx):
        if idx in self.cache:
            self.cache.move_to_end(idx)
            return self.cache[idx]
        table, key, info = ('rows', idx, self.info) if idx >= 0 else ('extras', -1-idx, self.extra_info)
        blob = self.conn.execute(f'SELECT reduced FROM {table} WHERE id=?', (key,)).fetchone()[0]
        vector = dict(unpack(blob))
        assert len(vector) == info[key][2] <= ROW_TERMS
        while self.cache and self.cache_terms+len(vector) > CACHE_TERMS:
            _, evicted = self.cache.popitem(last=False)
            self.cache_terms -= len(evicted)
        if len(vector) <= CACHE_TERMS:
            self.cache[idx] = vector
            self.cache_terms += len(vector)
        return vector

    def raw_row(self, idx):
        blob, digest = self.conn.execute('SELECT raw,digest FROM rows WHERE id=?', (idx,)).fetchone()
        pairs = unpack(blob)
        assert hashlib.sha256(compact(pairs).encode()).hexdigest() == digest
        assert len(pairs) <= ROW_TERMS
        return dict(pairs)

    def reduce(self, raw, weight):
        out = dict(raw)
        block = self.blocks.get(weight, {})
        for pivot in sorted(block, key=lambda i: self.states[i]):
            if pivot in out:
                self.subtract(out, out[pivot], self.row(block[pivot]))
        return out

    def consume(self, vector, word, test=False):
        assert len(vector) <= ROW_TERMS
        raw = {self.intern(s): int(c) for s, c in vector.items() if c}
        weights = {self.weights[i] for i in raw}
        assert len(weights) <= 1
        weight = next(iter(weights)) if weights else (0, 0)
        reduced = self.reduce(raw, weight)
        if test:
            self.meta['tests'] += 1
            if reduced:
                self.meta['failures'] += 1
                if self.meta['failure_witnesses'] < 20:
                    idx = self.meta['failure_witnesses']
                    self.conn.execute('INSERT INTO tests VALUES (?,?,?,?,?,?)',
                                      (idx, self.meta['stage'], compact(word),
                                       pack(sorted(raw.items())), pack(sorted(reduced.items())),
                                       hashlib.sha256(compact(sorted(raw.items())).encode()).hexdigest()))
                    self.meta['failure_witnesses'] += 1
                union_residual = dict(reduced)
                for pivot, key in sorted(self.extra_blocks.get(weight, {}).items(), key=lambda item: self.states[item[0]]):
                    self.subtract(union_residual, union_residual.get(pivot, 0), self.row(key))
                if union_residual:
                    pivot = min(union_residual, key=lambda i: self.states[i])
                    inv = pow(union_residual[pivot], -1, PRIME)
                    union_residual = {i: c*inv % PRIME for i, c in union_residual.items()}
                    if len(union_residual) > ROW_TERMS or self.meta['saved_terms']+len(raw)+len(union_residual) > DISK_TERMS:
                        raise Stop('Reviewed union sparse-row/disk-term cap before insertion')
                    idx = len(self.extra_info)
                    self.conn.execute('INSERT INTO extras VALUES (?,?,?,?,?,?,?,?,?)',
                                      (idx, *weight, pivot, len(union_residual), pack(sorted(raw.items())),
                                       pack(sorted(union_residual.items())), compact(word),
                                       hashlib.sha256(compact(sorted(raw.items())).encode()).hexdigest()))
                    self.extra_info.append((weight, pivot, len(union_residual)))
                    self.extra_blocks.setdefault(weight, {})[pivot] = -1-idx
                    self.meta['extra_rank'] += 1
                    self.meta['saved_terms'] += len(raw)+len(union_residual)
                if len(self.info)+len(self.extra_info) >= 6011:
                    self.meta['contradiction_rank_lower_bound'] = len(self.info)+len(self.extra_info)
                    self.requested_stop = 'Union of normal words and singular-product words exceeds conditional dimension6010'
                elif self.args.stop_on_first_residual:
                    self.requested_stop = 'First finite-prime normal-span residual; upper rank not certified'
            return
        if reduced:
            pivot = min(reduced, key=lambda i: self.states[i])
            inv = pow(reduced[pivot], -1, PRIME)
            reduced = {i: c*inv % PRIME for i, c in reduced.items()}
            if len(reduced) > ROW_TERMS or self.meta['saved_terms']+len(raw)+len(reduced) > DISK_TERMS:
                raise Stop('Reviewed sparse row/disk-term cap before insertion')
            idx = len(self.info)
            self.conn.execute('INSERT INTO rows VALUES (?,?,?,?,?,?,?,?,?)',
                              (idx, *weight, pivot, len(reduced), pack(sorted(raw.items())),
                               pack(sorted(reduced.items())), compact(word),
                               hashlib.sha256(compact(sorted(raw.items())).encode()).hexdigest()))
            self.blocks.setdefault(weight, {})[pivot] = idx
            self.info.append((weight, pivot, len(reduced)))
            self.meta['normal_rank'] += 1
            self.meta['saved_terms'] += len(raw)+len(reduced)
            if len(self.info) > 6010:
                self.meta['contradiction_rank_lower_bound'] = len(self.info)
                self.requested_stop = 'Normal words alone exceed conditional dimension6010'
        self.meta['candidates'] += 1

    def lower_test(self, vector, grade, word):
        raw = {s: int(c) for s, c in vector.items() if c}
        assert all(x.grade(s) == grade for s in raw)
        weights = {x.weight(s) for s in raw}
        assert len(weights) <= 1
        rows = self.small[grade].get(next(iter(weights)), {}) if weights else {}
        out = dict(raw)
        for pivot in sorted(rows):
            self.subtract(out, out.get(pivot, 0), rows[pivot])
        self.meta['tests'] += 1
        if out:
            self.meta['failures'] += 1
            if self.meta['failure_witnesses'] < 20:
                idx = self.meta['failure_witnesses']
                self.conn.execute('INSERT INTO tests VALUES (?,?,?,?,?,?)',
                                  (idx, self.meta['stage'], compact(word),
                                   pack([[list(s[0]), list(s[1]), c] for s, c in sorted(raw.items())]),
                                   pack([[list(s[0]), list(s[1]), c] for s, c in sorted(out.items())]),
                                   hashlib.sha256(compact(sorted(raw.items())).encode()).hexdigest()))
                self.meta['failure_witnesses'] += 1
            if self.args.stop_on_first_residual:
                self.requested_stop = 'First lower-grade finite-prime residual'

    def boundary(self):
        if self.requested_stop:
            raise Stop(self.requested_stop)
        if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss > 768*1024:
            raise Stop('768 MiB RSS review boundary')
        if monotonic()-self.started > self.args.seconds:
            raise Stop('Requested time boundary')
        if monotonic()-self.last_save >= 20:
            self.save('periodic candidate boundary')

    def save(self, reason, status='running'):
        now = monotonic()
        self.meta['elapsed_seconds'] += now-self.last_save
        self.last_save = now
        self.meta.update({'status': status, 'input_terms': self.input_terms,
                          'known_B4_states': len(self.states),
                          'union_rank_lower_bound': len(self.info)+len(self.extra_info),
                          'Cartan_ranks': {str(w): len(b) for w, b in sorted(self.blocks.items())},
                          'operators': [word for _, word in self.ops],
                          'P3_rows': self.source['order']['3'][634:],
                          'checkpoint_manifest': str(Path(self.args.checkpoint)/'manifest.json'),
                          'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                          'arithmetic': 'One good split prime; lower ranks and residuals only. No characteristic-zero containment or upper-rank claim.',
                          'provenance': 'Imported exact row references are bound to the frozen checkpoint and its word DAG. Every accepted normal row stores its raw vector, echelon row and mode word; normal_row always means its RAW vector, never its echelon vector. Every source row has a prior id. Extras record independent singular-product words for a union-rank certificate. SQLite atomically commits all rows, states, tests and cursor.',
                          'scope': 'Normal words only during rank construction. Tests do not augment that normal span. Properness is never assumed.'})
        self.meta['history'].append({'reason': reason, 'rank': len(self.info),
                                     'stage': self.meta['stage'], 'cursor': self.meta['cursor'],
                                     'tests': self.meta['tests'], 'failures': self.meta['failures'],
                                     'seconds': self.meta['elapsed_seconds']})
        self.conn.execute('INSERT OR REPLACE INTO meta VALUES (1,?)', (compact(self.meta),))
        self.conn.commit()
        temporary = self.output.with_suffix('.json.tmp')
        with temporary.open('w') as stream:
            json.dump({**self.meta, 'sqlite_file': str(self.path)}, stream, indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(self.output)
        clear_caches()
        print({'status': status, 'rank': len(self.info), 'stage': self.meta['stage'],
               'cursor': self.meta['cursor'], 'tests': self.meta['tests'],
               'failures': self.meta['failures'], 'union_rank': len(self.info)+len(self.extra_info), 'reason': reason,
               'seconds_this_call': now-self.started}, flush=True)


def run(db):
    s2 = db.source['order']['2']
    s3 = db.source['order']['3']
    p3 = s3[634:]
    currents = x.LEFT+x.RIGHT
    omega = x.omega()
    while db.meta['stage'] < 5:
        stage = db.meta['stage']
        if stage == 0:
            total = 7*len(s3)
            while db.meta['cursor'] < total:
                op, idx = divmod(db.meta['cursor'], len(s3))
                left, n = (currents[op], -1) if op < 6 else (omega, 0)
                db.consume(x.mode(left, n, db.inputs[s3[idx]]),
                           {'kind': 'normal_descendant', 'operator': op,
                            'mode': n, 'exact_input': s3[idx]})
                db.meta['cursor'] += 1
                db.boundary()
        elif stage == 1:
            while db.meta['cursor'] < len(db.ops)*len(s2):
                op, idx = divmod(db.meta['cursor'], len(s2))
                db.consume(x.mode(db.ops[op][0], -1, db.inputs[s2[idx]]),
                           {'kind': 'normal_S2_product', 'operator': op,
                            'mode': -1, 'exact_input': s2[idx]})
                db.meta['cursor'] += 1
                db.boundary()
        elif stage == 2:
            while db.meta['closure_cursor'] < 2*len(db.info):
                idx, j = divmod(db.meta['closure_cursor'], 2)
                cur = (2, 5)[j]
                # Lower actual normal words, keeping a short characteristic-zero DAG.
                source = {db.states[i]: x.A(c) for i, c in db.raw_row(idx).items()}
                db.consume(x.mode(currents[cur], 0, source),
                           {'kind': 'current_lowering', 'current': cur,
                            'mode': 0, 'normal_row': idx})
                db.meta['closure_cursor'] += 1
                db.boundary()
            db.meta['normal_span_complete'] = True
        elif stage == 3:
            while db.meta['cursor'] < len(db.ops)*len(p3):
                op, idx = divmod(db.meta['cursor'], len(p3))
                db.consume(x.mode(db.ops[op][0], 0, db.inputs[p3[idx]]),
                           {'kind': 'S2_zero_P3', 'operator': op,
                            'mode': 0, 'exact_input': p3[idx]}, test=True)
                db.meta['cursor'] += 1
                db.boundary()
        else:
            # All ten S2 copies, including the two neutral stresses, are
            # checked. The earlier S3 construction alone did not do this.
            tasks = []
            for op in range(len(db.ops)):
                tasks.extend((op, name, n, 3-n) for name in s2 for n in range(4))
                tasks.extend((op, name, n, 4-n) for name in p3 for n in range(1, 5))
            for cur in range(6):
                tasks.extend((10+cur, name, n, 2-n) for name in s2 for n in range(1, 3))
                tasks.extend((10+cur, name, n, 3-n) for name in p3 for n in range(1, 4))
            while db.meta['cursor'] < len(tasks):
                op, name, n, grade = tasks[db.meta['cursor']]
                left = db.ops[op][0] if op < 10 else currents[op-10]
                db.lower_test(x.mode(left, n, db.inputs[name]), grade,
                              {'kind': 'lower_singular_check', 'operator': op,
                               'mode': n, 'exact_input': name, 'target_grade': grade})
                db.meta['cursor'] += 1
                db.boundary()
        db.meta['stage'] += 1
        db.meta['cursor'] = 0
        db.save('stage complete')
    db.save('All normal seeds, current closure and listed singular checks exhausted', 'complete')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--output', default='hi_cft_20260923_next_n4_strong_pilot.json')
    parser.add_argument('--seconds', type=int, default=600)
    parser.add_argument('--stop-on-first-residual', action='store_true')
    args = parser.parse_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('hard call alarm')))
    signal.alarm(args.seconds)
    db = None
    try:
        assert g3.install_prime(PRIME) == [231543, 1000]
        x.creation = lru_cache(maxsize=128)(e4.creation.__wrapped__)
        # e4.vertex refers to its own module's creation global, so bind both.
        e4.creation = x.creation
        x.vertex = lru_cache(maxsize=512)(e4.vertex.__wrapped__)
        x.basis_mode = lru_cache(maxsize=512)(e4.basis_mode.__wrapped__)
        inputs = read_inputs(args)
        db = Database(args, inputs)
        db.save('initialized or resumed from atomic SQLite checkpoint')
        run(db)
    except Stop as error:
        signal.alarm(0)
        if db is None:
            raise
        db.save(str(error), 'bounded_stop')
    except (TimeoutError, MemoryError):
        signal.alarm(0)
        if db is not None:
            db.conn.rollback()
            print({'status': 'interrupted', 'action': 'Uncommitted transaction rolled back; prior SQLite metadata is authoritative.'}, flush=True)
        else:
            raise
    finally:
        signal.alarm(0)
        if db is not None:
            db.conn.close()


if __name__ == '__main__':
    main()
