"""Independent integer replay of the charged-bracket quotient certificate."""
import argparse
import json
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic
import zlib

import hi_cft_20260923_c8two_gate4_verify as arithmetic

auth = arithmetic.source
P = arithmetic.P
MIB = 1024**2


def unpack(blob):
    decoder = zlib.decompressobj()
    raw = decoder.decompress(blob, 8*MIB+1)
    assert len(raw) <= 8*MIB and decoder.eof and not decoder.unconsumed_tail
    return json.loads(raw)


def add(out, vector, scalar=1):
    for index, value in vector.items():
        new = (out.get(index, 0)+scalar*value) % P
        if new:
            out[index] = new
        else:
            out.pop(index, None)


def action(matrix, vector):
    out = {}
    for index, value in vector.items():
        add(out, matrix[index], value)
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', default='hi_cft_20260923_c8two_structure_charged_span.json')
    parser.add_argument('--output', default='hi_cft_20260923_c8two_charged_span_verified.json')
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(180)
    started = monotonic()
    path, output = Path(args.certificate).resolve(), Path(args.output).resolve()
    assert path.stat().st_size <= 32*MIB and not output.exists()
    assert not output.with_suffix(output.suffix+'.tmp').exists()
    cert = json.loads(path.read_text())
    assert cert['format'] == 'charged-zero-product-quotient-span-v1'
    assert cert['status'] == 'charged_zero_products_span_exact_quotient'
    assert cert['prime'] == P and cert['split_roots'] == [231543, 1000]
    assert cert['S3_dimension'] == 956 and cert['N3_dimension'] == 634
    assert cert['quotient_dimension'] == cert['combined_rank'] == 322
    bindings = {}
    auth.verify_graph(cert['source_sha256'], bindings)
    bindings[str(path)] = auth.sha(path)
    for filename in (__file__, arithmetic.__file__, auth.__file__):
        bindings[str(Path(filename).resolve())] = auth.sha(filename)
    names, weights = cert['quotient_order'], cert['quotient_weights']
    assert len(names) == len(set(names)) == len(weights) == 322
    indices = {name: index for index, name in enumerate(names)}
    raising_path = Path('hi_cft_20260923_c8two_structure_saturation.json').resolve()
    assert str(raising_path) in bindings
    raising = json.loads(raising_path.read_text())
    assert raising['arithmetic'] == 'exact' and raising['status'] == 'complete'
    assert raising['quotient_order'] == names and raising['quotient_weights'] == weights
    matrices = {key: {} for key in ('EL', 'ER', 'FL', 'FR')}
    rank = {}
    for records, is_lower in ((raising['raising_images'], False), (cert['lowering_images'], True)):
        assert len(records) == 644
        seen = set()
        for row in records:
            axis, name = row['axis'], row['input']
            assert axis in ('LEFT', 'RIGHT') and name in indices
            assert (axis, name) not in seen
            seen.add((axis, name))
            j = 0 if axis == 'LEFT' else 1
            expected_weight = list(weights[indices[name]])
            expected_weight[j] += -2 if is_lower else 2
            assert row['weight'] == expected_weight
            vector, coordinates = {}, set()
            for index, value in row['coordinates']:
                assert isinstance(index, int) and 0 <= index < 322 and index not in coordinates
                coordinates.add(index)
                assert weights[index] == expected_weight
                if is_lower:
                    assert isinstance(value, int) and 0 < value < P
                    reduced = value
                else:
                    reduced = arithmetic.coefficient(value)
                if reduced:
                    vector[index] = reduced
            key = ('F' if is_lower else 'E')+('L' if j == 0 else 'R')
            matrices[key][indices[name]] = vector
            if is_lower:
                arithmetic.insert(rank, vector)
    assert len(rank) == cert['lowering_image_rank'] == 294
    assert all(len(matrix) == 322 for matrix in matrices.values())
    # Independent representation controls combine exact raising coordinates
    # with the new prime lowering coordinates; they do not replace provenance.
    for i in range(322):
        for axis, j in (('L', 0), ('R', 1)):
            out = action(matrices['E'+axis], matrices['F'+axis][i])
            add(out, action(matrices['F'+axis], matrices['E'+axis][i]), -1)
            expected = {i: weights[i][j] % P} if weights[i][j] % P else {}
            assert out == expected
        for left, right in (('EL', 'ER'), ('EL', 'FR'), ('FL', 'ER'), ('FL', 'FR')):
            out = action(matrices[left], matrices[right][i])
            add(out, action(matrices[right], matrices[left][i]), -1)
            assert not out

    lower_path = Path('hi_cft_20260923_next_structure_lower_closure.json').resolve()
    assert str(lower_path) in bindings
    lower = json.loads(lower_path.read_text())
    database = Path(lower['sqlite_file']).resolve()
    assert str(database) in bindings and not Path(str(database)+'-journal').exists()
    assert not Path(str(database)+'-wal').exists() and database.stat().st_size <= 256*MIB
    B, K = {}, {}
    db = sqlite3.connect(database.as_uri()+'?mode=ro&immutable=1', uri=True)
    try:
        db.execute('PRAGMA cache_size=-2048')
        db.execute('PRAGMA mmap_size=0')
        assert json.loads(db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0]) == lower
        count = 0
        for idx, recipe, target_sha, relation, residual in db.execute('SELECT * FROM identities ORDER BY id'):
            assert idx == count
            count += 1
            assert unpack(residual) == []
            kind, op, name, mode, grade = json.loads(recipe)
            if mode != 0 or not (kind == 'current' or kind == 'weight_two' and op < 8):
                continue
            record = unpack(relation)
            assert len(record) == len({row[0] for row in record})
            if kind == 'weight_two':
                assert grade == 3 and 0 <= op < 8 and (op, name) not in B
                B[op, name] = {indices[n]: v for n, c in record
                              if n in indices and (v := arithmetic.coefficient(c))}
            else:
                assert grade == 2 and 0 <= op < 6 and (op, name) not in K
                K[op, name] = {n: v for n, c in record if (v := arithmetic.coefficient(c))}
        assert count == 3970 and len(B) == 960 and len(K) == 720
    finally:
        db.close()
    for seed in cert['independent_seeds']:
        op, current, name = seed['operator'], seed['right_current'], seed['right_input']
        assert 0 <= op < 8 and 0 <= current < 6 and (current, name) in K
        vector = {}
        for right, value in K[current, name].items():
            add(vector, B[op, right], value)
        record = seed['coordinates']
        assert len(record) == len({i for i, _ in record})
        assert all(isinstance(i, int) and 0 <= i < 322 and isinstance(v, int) and 0 < v < P
                   for i, v in record)
        assert vector == dict(record)
        before = len(rank)
        arithmetic.insert(rank, vector)
        assert len(rank) == before+1
    assert len(cert['independent_seeds']) == cert['charged_seed_rank_increment'] == 28
    assert len(rank) == 322
    assert str(output) not in bindings and str(output.with_suffix(output.suffix+'.tmp')) not in bindings
    result = {'format': 'independently-verified-charged-quotient-span-v1',
              'status': 'charged_pair_current_span_is_exact_P3_quotient',
              'source_sha256': bindings, 'prime': P, 'exact_quotient_dimension': 322,
              'lowering_image_rank': 294, 'independent_charged_seed_count': 28,
              'combined_rank': 322, 'sl2_and_cross_commutators_verified': True,
              'scope': 'Positive spanning plus the audited lowering-Nakayama lemma. Current modes remain source-bound; Gate4 and properness are not asserted.',
              'seconds': monotonic()-started,
              'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    auth.atomic(output, result)
    signal.alarm(0)
    print({key: result[key] for key in ('status', 'combined_rank', 'seconds', 'peak_rss_KiB')}, flush=True)


if __name__ == '__main__':
    main()
