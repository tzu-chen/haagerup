"""Resumable bounded grade-three lower rank from frozen X2 word vectors.

Root-only safe_run job, <=3 GiB AS, internal600s alarm,1 GiB RSS boundary
watch,2,000,000 combined input/raw/echelon-term cap. Stop at rank10630:
if U is proper, dimB3=11586 and certified dimS3=956 then force U3=S3.
No full ambient grade-three basis is generated. Primitive actions use
the already audited grade-three engine, with4096-entry mode caches.
"""
import argparse
from fractions import Fraction as Q
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
from time import monotonic

import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_c8_exact_grade3 as g3


PRIME = 1000003
TARGET = 10630
AMBIENT = 11586
TERM_CAP = 2000000
FORMAT = 'x3-word-span-v1'


class BudgetStop(Exception):
    pass


class Saturated(Exception):
    pass


def file_hash(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024**2), b''):
            h.update(chunk)
    return h.hexdigest()


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                    separators=(',', ':')).encode()).hexdigest()


def actual_u():
    return {((0, 0, 0, 0, 0, -1, 1, 1), ()): x.ONE,
            ((0, 0, 0, 1, 1, -1, 0, 0), ()): x.A((0, Q(1, 20), Q(3, 20), 0)),
            ((1, 1, 0, 0, 0, -1, 0, 0), ()): x.A((0, Q(1, 20), -Q(3, 20), 0))}


def frozen_inputs():
    certificate = Path('hi_cft_20260923_next_x2_conditional_rank.json')
    replay = Path('hi_cft_20260923_next_x2_replay.json')
    fields = Path('hi_cft_20260923_c8_exact_fields.json')
    grade3 = Path('hi_cft_20260923_c8_grade3_exact_v2.json')
    for path in (certificate, replay, fields, grade3):
        assert path.stat().st_size < 8*1024**2
    data = json.loads(certificate.read_text())
    checked = json.loads(replay.read_text())
    assert data['status'] == 'complete' and data['prime'] == PRIME
    assert data['rank_lower_bound'] == data['independent_vectors'] == 1250
    assert checked['rank_independently_verified'] == 1250
    assert checked['exact_X1_orthogonality_verified']
    for path, expected in checked['source_sha256'].items():
        assert file_hash(path) == expected
    for path, expected in data['source_sha256'].items():
        assert file_hash(path) == expected
    dimension_certificate = json.loads(grade3.read_text())
    assert dimension_certificate['grade_three_span_dimension'] == 956
    assert dimension_certificate['characteristic_zero_span_dimension_certified']
    for path, expected in dimension_certificate['source_sha256'].items():
        assert file_hash(path) == expected
    vectors_file = Path(data['independent_vectors_file'])
    assert vectors_file.stat().st_size < 32*1024**2
    assert file_hash(vectors_file) == data['independent_vectors_sha256']
    states = [(tuple(a), tuple(o)) for a, o in data['B2_basis']]
    assert len(states) == 1370 and all(x.grade(s) == 2 for s in states)
    vectors = []
    with vectors_file.open() as stream:
        for i, line in enumerate(stream):
            row = json.loads(line)
            assert row['id'] == i
            vector = {states[j]: x.A(c) for j, c in row['vector']}
            assert len(vector) == len(row['vector'])
            assert {x.weight(s) for s in vector} == {tuple(row['Cartan_weight'])}
            vectors.append(vector)
    assert len(vectors) == 1250
    field_data = json.loads(fields.read_text())
    charged = sorted(enumerate(field_data['fields'][:-1]),
                     key=lambda item: (len(item[1]['coefficients']), item[0]))
    operators = [(x.read_field(row), {'kind': 'certified_S2_highest',
                                    'field_index': i, 'dimensions': row['dimensions']})
                 for i, row in charged]
    paths = [Path(__file__), Path(x.__file__), Path(g3.__file__), certificate,
             vectors_file, replay, fields, grade3,
             Path('hi_cft_20260923_next_grade4_exact.py')]
    hashes = {str(path): file_hash(path) for path in paths}
    return vectors, operators, hashes


class Database:
    def __init__(self, args, inputs, operators, source_hashes):
        self.args = args
        self.output = Path(args.output)
        self.records_path = self.output.with_suffix('.vectors.jsonl')
        self.inputs = inputs
        self.operators = operators
        self.source_hashes = source_hashes
        self.started = monotonic()
        self.last_save = self.started
        self.states = []
        self.ids = {}
        self.weights = []
        self.rows = {}
        self.raw = []
        self.raw_terms = 0
        self.row_terms = 0
        self.input_terms = sum(map(len, inputs))
        self.hash = hashlib.sha256()
        self.meta = {'format': FORMAT, 'stage': 0, 'cursor': 0,
                     'closure_cursor': 0, 'candidate_count': 0, 'history': [],
                     'generation': 0, 'status': 'running', 'elapsed_seconds': 0}
        if self.output.exists():
            self.load()
        else:
            assert not self.records_path.exists(), 'Refusing orphan vector file'
            self.records = self.records_path.open('x+b')

    def intern(self, state):
        idx = self.ids.get(state)
        if idx is None:
            assert x.grade(state) == 3
            idx = len(self.states)
            assert idx < AMBIENT
            # Retain each full state tuple exactly once in the rank storage.
            self.states.append(state)
            self.ids[state] = idx
            self.weights.append(x.weight(state))
        return idx

    def encode_engine_vector(self, vector):
        return {self.intern(s): int(c) for s, c in vector.items() if c}

    def decode_source(self, idx):
        return {self.states[i]: x.A(c) for i, c in self.raw[idx].items()}

    def reduce(self, raw, weight):
        out = dict(raw)
        rows = self.rows.get(weight, {})
        for pivot in sorted(rows, key=lambda i: self.states[i]):
            factor = out.get(pivot, 0)
            if factor:
                for i, c in rows[pivot].items():
                    value = (out.get(i, 0)-factor*c) % PRIME
                    if value:
                        out[i] = value
                    else:
                        out.pop(i, None)
        if not out:
            return None, {}
        pivot = min(out, key=lambda i: self.states[i])
        inverse = pow(out[pivot], -1, PRIME)
        return pivot, {i: c*inverse % PRIME for i, c in out.items()}

    def consume(self, vector, word):
        raw = self.encode_engine_vector(vector)
        if not raw:
            self.meta['candidate_count'] += 1
            return
        weights = {self.weights[i] for i in raw}
        assert len(weights) == 1
        weight = weights.pop()
        pivot, reduced = self.reduce(raw, weight)
        if reduced:
            prospective = (self.input_terms+self.raw_terms+self.row_terms
                           +len(raw)+len(reduced))
            if prospective > TERM_CAP:
                raise BudgetStop('combined sparse-term cap before insertion')
            idx = len(self.raw)
            row = {'id': idx, 'word': word, 'Cartan_weight': list(weight),
                   'vector': sorted(raw.items()), 'echelon_row': sorted(reduced.items()),
                   'pivot_state_id': pivot,
                   'vector_sha256': digest(sorted(raw.items())),
                   'echelon_row_sha256': digest(sorted(reduced.items()))}
            line = (json.dumps(row, sort_keys=True, separators=(',', ':'))+'\n').encode()
            # An external kill or alarm can interrupt this transaction. Only
            # the last atomic summary's prefix is loadable, never this tail.
            self.records.write(line)
            self.hash.update(line)
            self.raw.append(raw)
            self.rows.setdefault(weight, {})[pivot] = reduced
            self.raw_terms += len(raw)
            self.row_terms += len(reduced)
            assert len(self.raw) <= AMBIENT
        self.meta['candidate_count'] += 1

    def boundary(self):
        if len(self.raw) >= TARGET:
            raise Saturated()
        if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss > 1024**2:
            raise BudgetStop('1 GiB RSS review budget reached')
        if monotonic()-self.started >= self.args.seconds:
            raise BudgetStop('time boundary reached')
        if monotonic()-self.last_save >= 30:
            self.save('periodic candidate boundary')

    def save(self, reason, status='running'):
        self.records.flush()
        os.fsync(self.records.fileno())
        now = monotonic()
        self.meta['elapsed_seconds'] += now-self.last_save
        self.last_save = now
        self.meta['generation'] += 1
        self.meta['status'] = status
        self.meta['history'].append({'reason': reason, 'rank': len(self.raw),
                                     'stage': self.meta['stage'], 'cursor': self.meta['cursor'],
                                     'closure_cursor': self.meta['closure_cursor'],
                                     'seconds_total': self.meta['elapsed_seconds']})
        if len(self.raw) > TARGET:
            consequence = 'Rank exceeds10630, contradicting U proper under the established fork.'
        elif len(self.raw) == TARGET:
            consequence = 'If U is proper then dimX3=10630 and U3=S3 has dimension956.'
        else:
            consequence = 'Conditional lower bound on dimX3 only; no properness conclusion.'
        result = dict(self.meta)
        result.update({'source_sha256': self.source_hashes, 'prime': PRIME,
                       'square_roots_mod_prime': [231543, 1000],
                       'rank_lower_bound': len(self.raw), 'target': TARGET,
                       'ambient_B3_dimension': AMBIENT, 'certified_S3_dimension': 956,
                       'properness_assumed_by_calculation': False,
                       'logical_consequence': consequence,
                       'arithmetic': 'split-prime lower bound, not a characteristic-zero upper rank',
                       'records_file': str(self.records_path),
                       'records_bytes': self.records.tell(), 'records_sha256': self.hash.hexdigest(),
                       'records_hash_scope': 'Only the committed prefix ending at records_bytes',
                       'states': [[list(a), list(o)] for a, o in self.states],
                       'known_state_count': len(self.states),
                       'Cartan_block_ranks': {str(w): len(rows) for w, rows in sorted(self.rows.items())},
                       'input_X2_terms': self.input_terms, 'raw_X3_terms': self.raw_terms,
                       'echelon_X3_terms': self.row_terms,
                       'combined_terms': self.input_terms+self.raw_terms+self.row_terms,
                       'combined_term_cap': TERM_CAP,
                       'charged_S2_operators': [word for _, word in self.operators],
                       'actual_u_recipe': 'Exactly the three-vertex op=u recipe in source-hashed next_grade4_exact.py',
                       'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                       'provenance': 'Each vector is an explicit current/stress/certified-S2/actual-u mode word on a frozen independent X2 vector, or a previous accepted X3 vector. Both raw and normalized echelon vectors are saved.',
                       'resume': 'This frozen producer verifies source hashes, loads the committed JSONL prefix, and discards only uncommitted tail bytes. No source edits are permitted between checkpoints.'})
        temporary = self.output.with_suffix(self.output.suffix+'.tmp')
        with temporary.open('w') as stream:
            json.dump(result, stream, indent=2)
            stream.write('\n')
            stream.flush()
            os.fsync(stream.fileno())
        temporary.replace(self.output)
        print({'status': status, 'rank': len(self.raw), 'stage': self.meta['stage'],
               'cursor': self.meta['cursor'], 'terms': result['combined_terms'],
               'seconds_this_call': now-self.started, 'reason': reason}, flush=True)

    def load(self):
        assert self.output.stat().st_size < 16*1024**2
        saved = json.loads(self.output.read_text())
        assert saved['format'] == FORMAT and saved['source_sha256'] == self.source_hashes
        assert saved['prime'] == PRIME and saved['combined_terms'] <= TERM_CAP
        assert Path(saved['records_file']) == self.records_path
        assert saved['status'] not in ('saturated', 'complete'), 'Certificate already finished'
        self.states = [(tuple(a), tuple(o)) for a, o in saved['states']]
        self.ids = {s: i for i, s in enumerate(self.states)}
        assert len(self.ids) == len(self.states) <= AMBIENT
        assert all(x.grade(s) == 3 for s in self.states)
        self.weights = [x.weight(s) for s in self.states]
        self.records = self.records_path.open('r+b')
        while self.records.tell() < saved['records_bytes']:
            line = self.records.readline()
            assert line.endswith(b'\n') and self.records.tell() <= saved['records_bytes']
            self.hash.update(line)
            row = json.loads(line)
            assert row['id'] == len(self.raw)
            assert digest(row['vector']) == row['vector_sha256']
            assert digest(row['echelon_row']) == row['echelon_row_sha256']
            raw, reduced = dict(row['vector']), dict(row['echelon_row'])
            weight, pivot = tuple(row['Cartan_weight']), row['pivot_state_id']
            assert reduced[pivot] == 1 and all(self.weights[i] == weight for i in raw)
            assert pivot not in self.rows.setdefault(weight, {})
            self.raw.append(raw)
            self.rows[weight][pivot] = reduced
            self.raw_terms += len(raw)
            self.row_terms += len(reduced)
        assert self.hash.hexdigest() == saved['records_sha256']
        assert len(self.raw) == saved['rank_lower_bound']
        assert self.input_terms+self.raw_terms+self.row_terms == saved['combined_terms']
        self.records.truncate(saved['records_bytes'])
        self.records.seek(saved['records_bytes'])
        self.meta = {key: saved[key] for key in self.meta}
        self.meta['status'] = 'running'


def run(db):
    currents = x.LEFT+x.RIGHT
    omega, u = x.omega(), actual_u()
    # stage0: all affine/translation seeds; stage1: closure. Each next
    # even stage seeds one certified charged highest field; odd stage closes.
    number_stages = 2+2*len(db.operators)
    while db.meta['stage'] < number_stages:
        stage = db.meta['stage']
        if stage % 2 == 0:
            total = len(db.inputs)*(7 if stage == 0 else 1)
            while db.meta['cursor'] < total:
                cursor = db.meta['cursor']
                if stage == 0:
                    op_index, source = divmod(cursor, len(db.inputs))
                    op, mode = (currents[op_index], -1) if op_index < 6 else (omega, 0)
                    label = ['current', op_index] if op_index < 6 else ['omega']
                else:
                    op_index = (stage-2)//2
                    op, _ = db.operators[op_index]
                    source, mode, label = cursor, 0, ['charged_S2', op_index]
                db.consume(x.mode(op, mode, db.inputs[source]),
                           {'kind': 'X2_mode', 'operator': label, 'mode': mode, 'X2': source})
                db.meta['cursor'] += 1
                db.boundary()
        else:
            closure_operators = [(currents[j], 0, ['current', j]) for j in (1, 2, 4, 5)]
            closure_operators.append((u, 1, ['u']))
            while db.meta['closure_cursor'] < 5*len(db.raw):
                idx, j = divmod(db.meta['closure_cursor'], 5)
                op, mode, label = closure_operators[j]
                source_vector = db.decode_source(idx)
                db.consume(x.mode(op, mode, source_vector),
                           {'kind': 'accepted_X3_mode', 'operator': label,
                            'mode': mode, 'source': idx})
                del source_vector
                db.meta['closure_cursor'] += 1
                db.boundary()
        db.meta['stage'] += 1
        db.meta['cursor'] = 0
        db.save('stage complete')
    db.save('all listed words and tested closure exhausted', 'complete')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', default='hi_cft_20260923_next_x3_conditional_rank.json')
    ap.add_argument('--seconds', type=int, default=600)
    args = ap.parse_args()
    assert 0 < args.seconds <= 600
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 3*1024**3
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('600-second hard alarm')))
    signal.alarm(args.seconds)
    assert g3.install_prime(PRIME) == [231543, 1000]
    x.creation = g3.creation
    x.vertex = lru_cache(maxsize=4096)(g3.vertex.__wrapped__)
    x.basis_mode = lru_cache(maxsize=4096)(g3.basis_mode.__wrapped__)
    inputs, operators, source_hashes = frozen_inputs()
    db = Database(args, inputs, operators, source_hashes)
    try:
        db.save('initialization or committed-prefix reload')
        run(db)
    except Saturated:
        signal.alarm(0)
        db.save('threshold reached; no upper-rank claim', 'saturated')
    except BudgetStop as error:
        signal.alarm(0)
        # BudgetStop is raised only before a mutation or after a complete
        # candidate. Its cursor is therefore resumable without row loss.
        db.save(str(error), 'bounded_stop')
    except (TimeoutError, MemoryError) as error:
        signal.alarm(0)
        # Asynchronous interruption might bisect a record or row update.
        # Preserve the prior atomic checkpoint and ignore any JSONL tail.
        if db.output.exists():
            saved = json.loads(db.output.read_text())
            saved['status'] = 'bounded_stop'
            saved['last_interruption'] = str(error)
            temporary = db.output.with_suffix(db.output.suffix+'.tmp')
            temporary.write_text(json.dumps(saved, indent=2)+'\n')
            temporary.replace(db.output)
            print({'status': 'bounded_stop', 'committed_rank': saved['rank_lower_bound'],
                   'reason': str(error)}, flush=True)
        else:
            raise
    finally:
        signal.alarm(0)
        db.records.close()


if __name__ == '__main__':
    main()
