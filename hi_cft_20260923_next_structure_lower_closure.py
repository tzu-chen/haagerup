"""Root-only bounded exact S2 singular-closure consumer with GMP coefficients.

No numerical launch is authorized by this file. Run through hi_cft_safe_run.py.
The frozen mode engines and exact checkpoint are read-only. Each successful
membership stores an exact linear relation in an atomic SQLite transaction.
This is a finite certificate, not by itself an all-weight properness proof.
"""
import argparse
from functools import lru_cache
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
import hi_cft_20260923_next_grade4_disk as frozen
import hi_cft_20260923_next_fast_field as fast

FORMAT = 'exact-gmp-lower-closure-v1'
MIB = 1024**2
MAX_TERMS = 300000
MAX_ROW_TERMS = 20000
MAX_BITS = 4096


class Stop(Exception):
    pass


def sha(path):
    out = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda: stream.read(MIB), b''):
            out.update(chunk)
    return out.hexdigest()


def text(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def coefficient(value):
    return [str(q) for q in value]


def bits(value):
    return max(max(abs(q.numerator).bit_length(), q.denominator.bit_length())
               for q in value)


def packed(vector):
    return [[list(a), list(o), coefficient(c)]
            for (a, o), c in sorted(vector.items())]


def subtract(out, factor, row):
    if not factor:
        return
    for state, value in row.items():
        product = value if factor == x.ONE else factor*value
        result = out.get(state, x.ZERO_A)-product
        if result:
            out[state] = result
        else:
            out.pop(state, None)


def load(args):
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
    hashes = {str(manifest): sha(manifest), **meta['sources']}
    for path in (__file__, x.__file__, g3.__file__, frozen.__file__, fast.__file__):
        hashes[str(path)] = sha(path)
    control = Path('hi_cft_20260923_next_fast_field_check.json')
    checked = json.loads(control.read_text())
    assert checked['status'] == 'exact_field_and_mode_equivalence_passed'
    adapter_hashes = {Path(path).name: digest
                      for path, digest in checked['source_sha256'].items()}
    assert adapter_hashes[Path(fast.__file__).name] == sha(fast.__file__)
    assert adapter_hashes[Path(x.__file__).name] == sha(x.__file__)
    hashes[str(control)] = sha(control)

    rows, blocks, terms = {}, {1: {}, 2: {}, 3: {}}, 0
    for filename in meta['block_files']:
        if not filename.startswith(('grade2_', 'grade3_')):
            continue
        path = directory/filename
        assert sha(path) == meta['files_sha256'][filename]
        hashes[str(path)] = sha(path)
        for saved in frozen.row_stream(path):
            assert len(saved['vector']) <= MAX_ROW_TERMS
            vector = {(tuple(a), tuple(o)): x.A(c)
                      for a, o, c in saved['vector']}
            assert vector and all(vector.values())
            grade, weight = saved['grade'], tuple(saved['weight'])
            assert all(x.grade(s) == grade and x.weight(s) == weight for s in vector)
            pivot = min(vector)
            assert vector[pivot] == x.ONE
            assert saved['id'] not in rows
            block = blocks[grade].setdefault(weight, {})
            assert pivot not in block
            rows[saved['id']] = vector
            block[pivot] = saved['id']
            terms += len(vector)
            assert terms <= MAX_TERMS
    assert set(rows) == set(meta['order']['2']+meta['order']['3'])

    # Six tiny current-space echelon rows are reconstructed deterministically.
    # Their full coordinates are included in the certificate metadata.
    current_basis = {}
    for i, current in enumerate(x.LEFT+x.RIGHT):
        out = current.copy()
        weight = x.weight(next(iter(out)))
        block = blocks[1].setdefault(weight, {})
        for pivot, name in sorted(block.items()):
            subtract(out, out.get(pivot, x.ZERO_A), rows[name])
        assert out
        pivot = min(out)
        inverse = out[pivot].inv()
        out = {s: c*inverse for s, c in out.items()}
        name = 'current_basis_%d' % i
        rows[name] = out
        block[pivot] = name
        current_basis[name] = packed(out)

    source = Path('hi_cft_20260923_c8_exact_fields.json')
    data = json.loads(source.read_text())['fields']
    operators = [x.read_field(row) for row in data[:-1]]
    neutral = x.read_field(data[-1])
    operators += [neutral, x.vadd((1, x.omega()),
                                  (-1, x.sugawara(x.LEFT, 1)),
                                  (-1, x.sugawara(x.RIGHT, 39)), (-1, neutral))]
    assert len(operators) == 10
    assert all(all(x.grade(s) == 2 for s in a) for a in operators)
    return meta, hashes, rows, blocks, operators, current_basis, terms


def tasks(meta):
    order2 = meta['order']['2']
    result = [('quasiprimary', op, None, 2, 1) for op in range(10)]
    # The two neutral mode-zero families were not seeds in the old S3 run.
    for op in (8, 9, 0, 1, 2, 3, 4, 5, 6, 7):
        for mode in (0, 1):
            result.extend(('weight_two', op, name, mode, 3-mode) for name in order2)
    for cur in range(6):
        for mode in (0, 1):
            result.extend(('current', cur, name, mode, 2-mode) for name in order2)
    result.extend(('L1_S2', 0, name, 2, 1) for name in order2)
    assert len(result) == 3970
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', default='hi_cft_20260923_next_grade4_checkpoint/checkpoint_000024')
    parser.add_argument('--output', default='hi_cft_20260923_next_structure_lower_closure.json')
    parser.add_argument('--seconds', type=int, default=300)
    args = parser.parse_args()
    assert 0 < args.seconds <= 900
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('hard alarm')))
    signal.alarm(args.seconds+15)
    started = last_save = monotonic()
    conn = None
    try:
        fast.install(x)
        x.creation = lru_cache(maxsize=128)(g3.creation.__wrapped__)
        g3.creation = x.creation
        x.vertex = lru_cache(maxsize=512)(g3.vertex.__wrapped__)
        x.basis_mode = lru_cache(maxsize=512)(g3.basis_mode.__wrapped__)
        source, hashes, rows, blocks, operators, currents, input_terms = load(args)
        work = tasks(source)
        output = Path(args.output)
        database = output.with_suffix('.sqlite')
        conn = sqlite3.connect(database)
        conn.execute('PRAGMA journal_mode=DELETE')
        conn.execute('PRAGMA synchronous=FULL')
        conn.execute('PRAGMA cache_size=-8192')
        conn.execute('PRAGMA temp_store=FILE')
        conn.execute('PRAGMA mmap_size=0')
        assert conn.execute('PRAGMA page_size').fetchone()[0] == 4096
        conn.execute('PRAGMA max_page_count=65536')  # 256 MiB total database.
        conn.execute('CREATE TABLE IF NOT EXISTS meta (id INTEGER PRIMARY KEY, value TEXT)')
        conn.execute('CREATE TABLE IF NOT EXISTS identities (id INTEGER PRIMARY KEY, recipe TEXT, target_sha256 TEXT, relation BLOB, residual BLOB)')
        conn.commit()
        saved = conn.execute('SELECT value FROM meta WHERE id=1').fetchone()
        if saved:
            status = json.loads(saved[0])
            assert status['format'] == FORMAT and status['source_sha256'] == hashes
            assert status['status'] == 'bounded_stop'
            assert conn.execute('SELECT count(*) FROM identities').fetchone()[0] == status['cursor']
        else:
            assert not conn.execute('SELECT 1 FROM identities LIMIT 1').fetchone()
            status = {'format': FORMAT, 'source_sha256': hashes, 'cursor': 0,
                      'status': 'running', 'seconds': 0, 'history': [],
                      'current_basis': currents, 'total_tasks': len(work),
                      'input_sparse_terms': input_terms, 'largest_coefficient_bits': 0,
                      'arithmetic': 'Exact Q(sqrt(13),sqrt(-3)); GMP mpq components',
                      'scope': 'Exact finite S2/current closure relations. No standalone properness claim.'}

        def save(reason, state):
            nonlocal last_save
            now = monotonic()
            status['seconds'] += now-last_save
            last_save = now
            status.update(status=state, reason=reason,
                          peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                          sqlite_file=str(database))
            status['history'].append({'cursor': status['cursor'], 'seconds': status['seconds'],
                                      'reason': reason})
            conn.execute('INSERT OR REPLACE INTO meta VALUES (1,?)', (text(status),))
            conn.commit()
            temporary = output.with_suffix('.json.tmp')
            with temporary.open('w') as stream:
                json.dump(status, stream, indent=2)
                stream.write('\n')
                stream.flush()
                os.fsync(stream.fileno())
            temporary.replace(output)
            for fun in (x.creation, x.vertex, x.basis_mode):
                fun.cache_clear()
            print({'status': state, 'cursor': status['cursor'], 'total': len(work),
                   'seconds': status['seconds'], 'reason': reason}, flush=True)

        save('initialized or resumed', 'bounded_stop')
        omega = x.omega()
        while status['cursor'] < len(work):
            index = status['cursor']
            kind, op, name, mode, grade = work[index]
            if kind == 'quasiprimary':
                left, right = omega, operators[op]
            elif kind == 'weight_two':
                left, right = operators[op], rows[name]
            elif kind == 'current':
                left, right = (x.LEFT+x.RIGHT)[op], rows[name]
            else:
                left, right = omega, rows[name]
            target = x.mode(left, mode, right)
            assert len(target) <= MAX_ROW_TERMS
            assert all(x.grade(s) == grade for s in target)
            residual, relation = target.copy(), []
            if kind != 'quasiprimary' and target:
                weights = {x.weight(s) for s in target}
                assert len(weights) == 1
                for pivot, basis in sorted(blocks[grade].get(next(iter(weights)), {}).items()):
                    factor = residual.get(pivot, x.ZERO_A)
                    if factor:
                        height = bits(factor)
                        if height > MAX_BITS:
                            raise Stop('4096-bit coefficient review boundary')
                        status['largest_coefficient_bits'] = max(status['largest_coefficient_bits'], height)
                        relation.append([basis, coefficient(factor)])
                        subtract(residual, factor, rows[basis])
            # Storing this exact reduction relation makes every PASS replayable.
            relation_text, residual_text = text(relation), text(packed(residual))
            assert len(relation_text)+len(residual_text) < 8*MIB
            conn.execute('INSERT INTO identities VALUES (?,?,?,?,?)',
                         (index, text(work[index]), hashlib.sha256(text(packed(target)).encode()).hexdigest(),
                          zlib.compress(relation_text.encode(), 1), zlib.compress(residual_text.encode(), 1)))
            status['cursor'] += 1
            if residual:
                status['failure'] = {'task': list(work[index]), 'residual_terms': len(residual)}
                save('Exact nonzero residual', 'failed')
                return
            if resource.getrusage(resource.RUSAGE_SELF).ru_maxrss > 768*1024:
                raise Stop('768 MiB RSS review boundary')
            if monotonic()-started >= args.seconds:
                raise Stop('requested time boundary')
            if monotonic()-last_save >= 20:
                save('periodic exact boundary', 'bounded_stop')
        save('All exact lower closure and quasiprimary identities passed', 'complete')
    except Stop as error:
        signal.alarm(0)
        if conn is None:
            raise
        save(str(error), 'bounded_stop')
    except (TimeoutError, MemoryError):
        signal.alarm(0)
        if conn is None:
            raise
        conn.rollback()
        print({'status': 'interrupted', 'action': 'Uncommitted identities rolled back; SQLite metadata is authoritative.'}, flush=True)
    finally:
        signal.alarm(0)
        if conn is not None:
            conn.close()


if __name__ == '__main__':
    main()
