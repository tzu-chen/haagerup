"""Combine exact raised controls, singlet residuals and raising saturation."""
import argparse
from collections import OrderedDict, defaultdict
from contextlib import closing
import json
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic

import hi_cft_20260923_c8two_gate4_verify as old
import hi_cft_20260923_next_fast_field as fast
import hi_cft_20260923_next_integer_residual as integer
import hi_cft_20260923_next_n5_exact_selected as records
import hi_cft_20260923_c8two_h4_singlet_common as projector

auth = old.source
MIB = 1024**2


def database(path, limit=512*MIB):
    path = Path(path).resolve()
    assert path.stat().st_size <= limit
    assert not Path(str(path)+'-journal').exists() and not Path(str(path)+'-wal').exists()
    db = sqlite3.connect(path.as_uri()+'?mode=ro&immutable=1', uri=True)
    db.execute('PRAGMA cache_size=-2048')
    db.execute('PRAGMA mmap_size=0')
    return db


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--saturation', default='hi_cft_20260923_c8two_structure_saturation.json')
    parser.add_argument('--targeted-directory', default='hi_cft_20260923_c8two_targeted_h4_trimmed_v2')
    parser.add_argument('--premise', default='hi_cft_20260923_c8two_h4_singlet_premise_verified.json')
    parser.add_argument('--exact', default='hi_cft_20260923_c8two_h4_singlet_exact.json')
    parser.add_argument('--prime', default='hi_cft_20260923_c8two_h4_singlet_prime.json')
    parser.add_argument('--output', default='hi_cft_20260923_c8two_gate4_verified.json')
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(240)
    started = monotonic()
    bindings = {}
    output = Path(args.output).resolve()
    assert not output.exists() and not output.with_suffix(output.suffix+'.tmp').exists()

    def boundary():
        assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss <= 768*1024
        if monotonic()-started > 240:
            raise TimeoutError('Final Gate4 verification deadline')

    def read(path):
        path = Path(path).resolve()
        assert path.stat().st_size <= 32*MIB
        value = json.loads(path.read_text())
        auth.nested_graphs(value, bindings)
        bindings[str(path)] = auth.sha(path)
        return value

    for path in (__file__, old.__file__, auth.__file__, fast.__file__, integer.__file__,
                 records.__file__, projector.__file__):
        bindings[str(Path(path).resolve())] = auth.sha(path)
    cert = read(args.saturation)
    assert cert['format'] == auth.FORMAT and cert['status'] == 'complete'
    assert cert['arithmetic'] == 'exact' and cert['S3_dimension'] == 956
    assert cert['N3_dimension'] == 634 and cert['Q_dimension'] == 322
    assert len(cert['left_highest_checks']) == 9 and all(r['passed'] for r in cert['left_highest_checks'])
    names, weights = cert['quotient_order'], cert['quotient_weights']
    assert len(names) == len(set(names)) == len(weights) == 322
    indices = {name: index for index, name in enumerate(names)}
    requested = {(r['operator'], r['exact_input']) for r in cert['additional_tests']}
    assert len(requested) == len(cert['additional_tests']) == 130
    seeds = {op: set() for op in range(9)}
    grouped = defaultdict(list)
    for op_text, group in cert['seed_records'].items():
        op = int(op_text)
        assert op in seeds
        for name, ref in group.items():
            grouped[ref['file']].append((op, name, ref))
    for filename, group in grouped.items():
        assert str(Path(filename).resolve()) in bindings
        with closing(database(filename)) as db:
            for op, name, ref in group:
                pair, _ = old.exact_record(db, ref['table'], ref['name'], ref['record_sha256'])
                assert pair == (op, name) and name in indices and name not in seeds[op]
                seeds[op].add(name)
    assert sum(map(len, seeds.values())) == 2145
    directory = Path(args.targeted_directory).resolve()
    policy = read(directory/'targeted_policy.json')
    assert policy['format'] == 'targeted-H4-integer-residual-v1'
    assert {tuple(pair) for pair in policy['requested_targets']} == requested
    additions = {}
    files = sorted(directory.glob('block_*.sqlite'))
    assert 0 < len(files) <= 100
    for path in files:
        with closing(database(path)) as db:
            meta = json.loads(db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
            assert meta['targeted_selection']['policy'] == policy and meta['failed_targets'] == 0
            auth.nested_graphs(meta, bindings)
            keys = [row[0] for row in db.execute('SELECT name FROM relations ORDER BY name')]
            assert len(keys) == meta['verified_targets']
            for key in keys:
                pair, digest = old.exact_record(db, 'relations', key)
                assert pair in requested and pair not in additions and pair[1] not in seeds[pair[0]]
                additions[pair] = {'database': str(path), 'name': key, 'digest': digest}
        bindings[str(path)] = auth.sha(path)
    assert len(additions) == 118
    pending = requested-set(additions)
    premise = read(args.premise)
    assert premise['format'] == 'verified-H4-singlet-raising-premise-v1'
    assert premise['status'] == 'all_pending_H4_classes_are_K_singlets'
    assert {(r['operator'], r['exact_input']) for r in premise['pending_targets']} == pending
    assert len(pending) == len(premise['pending_targets']) == 12
    exact, prime = read(args.exact), read(args.prime)
    assert exact['format'] == 'exact-H4-singlet-normal-relations-v1'
    assert exact['status'] == 'complete' and exact['all_source_targets_verified']
    assert exact['target_count'] == exact['verified_targets'] == 12 and exact['failed_targets'] == 0
    assert exact['factors'] == projector.factors() and not exact['unprojected_H4_membership_claimed']
    assert prime['format'] == 'H4-singlet-normal-prime-v1' and prime['prime'] == old.P
    assert prime['factors'] == projector.factors() and prime['bounds'] == [4, 24]
    assert prime['weight'] == [0, 0] and prime['target_count'] == prime['contained'] == 12
    primepath = Path(prime['sqlite_file']).resolve()
    exactpath = Path(exact['sqlite_file']).resolve()
    assert str(primepath) in bindings
    projected = {}
    with closing(database(primepath, 256*MIB)) as pdb, closing(database(exactpath, 256*MIB)) as db:
        pm = json.loads(pdb.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        em = json.loads(db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
        assert {k: v for k, v in prime.items() if k != 'sqlite_file'} == pm
        assert {k: v for k, v in exact.items() if k != 'sqlite_file'} == em
        auth.nested_graphs(em, bindings)
        column_ids = set()
        for idx, word_json in pdb.execute('SELECT id,word FROM rows ORDER BY id'):
            assert idx == len(column_ids)
            word = json.loads(word_json)
            assert word['factors'] == projector.factors()
            assert word['recipe']['kind'] == 'normal' and word['recipe']['column'] >= 0
            column_ids.add(idx)
        assert len(column_ids) == prime['rank'] <= 100
        cache, cache_bytes = OrderedDict(), 0

        def vector(name):
            nonlocal cache_bytes
            if name in cache:
                cache.move_to_end(name)
                return cache[name][0]
            blob, digest, terms, bits = db.execute(
                'SELECT record,digest,terms,bits FROM vectors WHERE name=?', (name,)).fetchone()
            value = records.unpack(blob, digest)
            assert len(value) == terms <= 5000 and bits <= 2048
            out = {(tuple(a), tuple(o)): fast.FastField(c) for a, o, c in value}
            assert len(out) == terms and all(out.values())
            assert all(auth.x.grade(s) == 4 and auth.x.weight(s) == (0, 0) for s in out)
            cost = 4096+terms*(1024+8*((bits+7)//8))
            while cache and cache_bytes+cost > 16*MIB:
                _, (_, old_cost) = cache.popitem(last=False)
                cache_bytes -= old_cost
            if cost <= 16*MIB:
                cache[name] = out, cost
                cache_bytes += cost
            boundary()
            return out

        controls = integer.controls(fast.FastField)
        engine = integer.Residual(fast.FastField, lambda idx: vector('grade5:'+str(idx)),
                                  boundary, max_bytes=32*MIB)
        count = 0
        for idx, blob, digest, passed in db.execute('SELECT id,record,digest,passed FROM relations ORDER BY id'):
            assert idx == count and passed == 1
            count += 1
            relation = records.unpack(blob, digest)
            assert relation['source_target_id'] == idx and relation['weight'] == [0, 0]
            assert relation['exact_residual_zero'] and relation['residual'] == []
            word_json, = pdb.execute('SELECT word FROM targets WHERE id=?', (idx,)).fetchone()
            word = json.loads(word_json)
            assert relation['word'] == word and word['factors'] == projector.factors()
            recipe = word['recipe']
            assert recipe['kind'] == 'target'
            pair = recipe['operator'], recipe['input']
            assert pair in pending and pair not in projected
            coefficients = relation['normal_column_coefficients']
            assert len(coefficients) == len({j for j, _ in coefficients}) <= 100
            assert all(j in column_ids for j, _ in coefficients)
            fields = [fast.FastField(c) for _, c in coefficients]
            assert max((records.b.height(c) for c in fields), default=0) <= 4096
            target = vector('target:'+str(idx))
            assert len(target) == relation['target_terms']
            assert not engine.residual(target, [j for j, _ in coefficients], fields)
            projected[pair] = {'database': str(exactpath), 'id': idx, 'record_sha256': digest,
                               'independent_integer_residual_zero': True}
        assert count == 12 and set(projected) == pending
    bindings[str(exactpath)] = auth.sha(exactpath)
    # The quotient is a K singlet by the exact raising premise. The same
    # projector is identity on this quotient, so the projected identity
    # implies the unprojected target is in the full current-stable W4.
    image = {}
    seen = set()
    for row in cert['raising_images']:
        axis, name = row['axis'], row['input']
        assert axis in ('LEFT', 'RIGHT') and name in indices and (axis, name) not in seen
        seen.add((axis, name))
        shift = (2, 0) if axis == 'LEFT' else (0, 2)
        weight = [a+b for a, b in zip(weights[indices[name]], shift)]
        assert row['weight'] == weight
        coordinates, visited = {}, set()
        for index, coefficient in row['coordinates']:
            assert isinstance(index, int) and 0 <= index < 322 and index not in visited
            visited.add(index)
            assert weights[index] == weight
            value = old.coefficient(coefficient)
            if value:
                coordinates[index] = value
        old.insert(image, coordinates)
    assert len(seen) == 644 and len(image) == 294
    ranks = []
    for op in range(9):
        basis = {pivot: dict(row) for pivot, row in image.items()}
        for name in seeds[op]:
            old.insert(basis, {indices[name]: 1})
        for operator, name in requested:
            if operator == op:
                old.insert(basis, {indices[name]: 1})
        assert len(basis) == 322
        ranks.append({'operator': op, 'augmented_prime_rank': 322})
    boundary()
    assert str(output) not in bindings and str(output.with_suffix(output.suffix+'.tmp')) not in bindings
    result = {'format': 'verified-H4-raising-certificate-v1',
              'derivation_method': 'exact-raised-controls-and-joint-singlet-recovery',
              'status': 'all_Gate4_identities_proved_by_exact_seeds_and_raising',
              'source_sha256': bindings, 'old_exact_seed_count': 2145,
              'additional_direct_exact_count': 118, 'additional_singlet_exact_count': 12,
              'singlet_premise_authenticated': True,
              'independent_projected_integer_residuals_zero': 12,
              'integer_controls': controls, 'operators': ranks,
              'implied_A0P3_identity_count': 2898,
              'projected_records': [{'operator': op, 'input': name, **ref}
                                    for (op, name), ref in sorted(projected.items())],
              'scope': 'Gate4 proved using exact raised controls, singlet recovery, independent projected residuals and raising Nakayama. Gate5 and properness are separate deductions.',
              'seconds': monotonic()-started,
              'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    auth.atomic(output, result)
    signal.alarm(0)
    print({k: result[k] for k in ('status', 'implied_A0P3_identity_count', 'seconds', 'peak_rss_KiB')}, flush=True)


if __name__ == '__main__':
    main()
