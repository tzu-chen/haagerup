"""Independent prime-rank replay combining exact H4 seeds and additions.

This verifies the finite raising-coinvariant certificate. Actual current
mode reconstruction remains source-bound to the exact saturation producer.
"""
import argparse
from collections import defaultdict
from contextlib import closing
from fractions import Fraction
import json
from pathlib import Path
import resource
import signal
import sqlite3
from time import monotonic

import hi_cft_20260923_c8two_structure_saturation as source

P = 1000003
ROOTS = (1, 231543, 1000, 231543*1000 % P)


def coefficient(record):
    assert len(record) == 4
    out = 0
    for text, root in zip(record, ROOTS):
        q = Fraction(text)
        assert q.denominator % P
        out += (q.numerator % P)*pow(q.denominator, -1, P)*root
    return out % P


def insert(basis, vector):
    out = dict(vector)
    for pivot, row in sorted(basis.items()):
        c = out.get(pivot, 0)
        if c:
            for index, value in row.items():
                new = (out.get(index, 0)-c*value) % P
                if new:
                    out[index] = new
                else:
                    out.pop(index, None)
    if not out:
        return
    pivot = min(out)
    inverse = pow(out[pivot], -1, P)
    basis[pivot] = {index: value*inverse % P for index, value in out.items()}


def exact_record(connection, table, name, expected_digest=None):
    assert table in ('relations', 'zero_relations')
    blob, digest, passed = connection.execute(
        'SELECT record,digest,passed FROM '+table+' WHERE name=?', (name,)).fetchone()
    assert passed == 1 and (expected_digest is None or digest == expected_digest)
    record = source.unpack(blob, digest)
    assert record['word']['mode'] == 0
    if table == 'relations':
        assert record['exact_residual_zero'] and record['residual'] == []
    else:
        assert record['exact_target_zero'] and record['normal_columns'] == []
    pair = (record['word']['operator'], record['word']['exact_input'])
    assert name == 'A%d_zero_%s' % pair
    return pair, digest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--saturation', default='hi_cft_20260923_c8two_structure_saturation.json')
    parser.add_argument('--targeted-directory', default='hi_cft_20260923_c8two_targeted_h4_bulk')
    parser.add_argument('--output', default='hi_cft_20260923_c8two_gate4_verified.json')
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 2*1024**3
    signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError()))
    signal.alarm(180)
    started = monotonic()
    path, directory, output = Path(args.saturation).resolve(), Path(args.targeted_directory).resolve(), Path(args.output).resolve()
    temporary = output.with_suffix(output.suffix+'.tmp')
    assert not output.exists() and not temporary.exists() and path.stat().st_size <= 32*1024**2
    cert = json.loads(path.read_text())
    assert cert['format'] == source.FORMAT and cert['status'] == 'complete'
    assert cert['arithmetic'] == 'exact' and cert['S3_dimension'] == 956
    assert cert['N3_dimension'] == 634 and cert['Q_dimension'] == 322
    assert len(cert['operators']) == 9
    assert len(cert['left_highest_checks']) == 9 and all(row['passed'] for row in cert['left_highest_checks'])
    bindings = {}
    source.verify_graph(cert['source_sha256'], bindings)
    bindings[str(path)] = source.sha(path)
    for filename in (__file__, source.__file__):
        bindings[str(Path(filename).resolve())] = source.sha(filename)
    order, weights = cert['quotient_order'], cert['quotient_weights']
    assert len(order) == len(set(order)) == len(weights) == 322
    indices = {name: index for index, name in enumerate(order)}

    # Independently authenticate all old seed records rather than trusting counts.
    grouped = defaultdict(list)
    seeds = {op: set() for op in range(9)}
    for op_text, records in cert['seed_records'].items():
        op = int(op_text)
        assert op in seeds
        for name, ref in records.items():
            assert name in indices
            grouped[ref['file']].append((op, name, ref))
    for filename, records in grouped.items():
        dbpath = Path(filename).resolve()
        assert str(dbpath) in bindings and not Path(str(dbpath)+'-journal').exists()
        with closing(sqlite3.connect(dbpath.as_uri()+'?mode=ro&immutable=1', uri=True)) as db:
            db.execute('PRAGMA cache_size=-2048')
            db.execute('PRAGMA mmap_size=0')
            for op, name, ref in records:
                pair, _ = exact_record(db, ref['table'], ref['name'], ref['record_sha256'])
                assert pair == (op, name) and name not in seeds[op]
                seeds[op].add(name)
    assert sum(map(len, seeds.values())) == cert['seed_count'] == 2145

    requested = {(row['operator'], row['exact_input']) for row in cert['additional_tests']}
    assert len(requested) == len(cert['additional_tests'])
    assert not directory.joinpath('summary.json-journal').exists()
    assert not list(directory.glob('*-journal'))
    policy_path, summary_path = directory/'targeted_policy.json', directory/'summary.json'
    policy, summary = json.loads(policy_path.read_text()), json.loads(summary_path.read_text())
    assert policy['format'] == 'targeted-H4-integer-residual-v1'
    source.nested_graphs(policy, bindings)
    assert policy['source_sha256'][str(path)] == source.sha(path)
    assert {tuple(pair) for pair in policy['requested_targets']} == requested
    assert summary['policy'] == policy and summary['status'] == 'all_requested_exact_H4_targets_passed'
    bindings[str(policy_path)], bindings[str(summary_path)] = source.sha(policy_path), source.sha(summary_path)
    additions = {}
    for block in summary['blocks']:
        dbpath = Path(block['output']).with_suffix('.sqlite').resolve()
        assert dbpath.parent == directory and dbpath.stat().st_size <= 512*1024**2
        with closing(sqlite3.connect(dbpath.as_uri()+'?mode=ro&immutable=1', uri=True)) as db:
            db.execute('PRAGMA cache_size=-2048')
            db.execute('PRAGMA mmap_size=0')
            meta = json.loads(db.execute('SELECT value FROM meta WHERE id=1').fetchone()[0])
            assert meta['targeted_selection']['policy'] == policy
            assert meta['all_requested_targets_verified'] and meta['failed_targets'] == 0
            source.nested_graphs(meta, bindings)
            names = [row[0] for row in db.execute('SELECT name FROM relations ORDER BY name')]
            assert len(names) == meta['verified_targets'] == block['verified_targets']
            for name in names:
                pair, digest = exact_record(db, 'relations', name)
                assert pair in requested and pair not in additions
                assert pair[1] not in seeds[pair[0]]
                additions[pair] = {'file': str(dbpath), 'name': name, 'digest': digest}
        bindings[str(dbpath)] = source.sha(dbpath)
    assert set(additions) == requested

    # This independent arithmetic only uses Python integers and Fraction parsing.
    assert ROOTS[1]**2 % P == 13 and ROOTS[2]**2 % P == P-3
    image = {}
    assert len(cert['raising_images']) == 644
    image_keys = set()
    for row in cert['raising_images']:
        axis, name = row['axis'], row['input']
        assert axis in ('LEFT', 'RIGHT') and name in indices
        assert (axis, name) not in image_keys
        image_keys.add((axis, name))
        shift = (2, 0) if axis == 'LEFT' else (0, 2)
        weight = [a+b for a, b in zip(weights[indices[name]], shift)]
        assert row['weight'] == weight
        vector, seen = {}, set()
        for index, value in row['coordinates']:
            assert isinstance(index, int) and 0 <= index < 322 and index not in seen
            seen.add(index)
            assert weights[index] == weight
            reduced = coefficient(value)
            if reduced:
                vector[index] = reduced
        insert(image, vector)
    assert len(image) == cert['raising_image_rank'] == 294
    verified = []
    for op in range(9):
        basis = {pivot: dict(row) for pivot, row in image.items()}
        for name in seeds[op]:
            insert(basis, {indices[name]: 1})
        before = len(basis)
        extra = sorted(name for operator, name in additions if operator == op)
        for name in extra:
            insert(basis, {indices[name]: 1})
        assert len(basis) == 322
        verified.append({'operator': op, 'prime_rank_with_old_seeds': before,
                         'additional_exact_identities': len(extra), 'augmented_prime_rank': 322})
    assert str(output) not in bindings and str(temporary) not in bindings
    result = {'format': 'verified-H4-raising-certificate-v1',
              'status': 'all_Gate4_identities_proved_by_exact_seeds_and_raising',
              'source_sha256': bindings, 'old_exact_seed_count': 2145,
              'additional_exact_count': len(additions), 'operators': verified,
              'prime': P, 'raising_image_prime_rank': len(image),
              'implied_A0P3_identity_count': 2898,
              'scope': 'Gate4 only. Uses the audited raising-kernel/nilpotent-Nakayama lemma, exact S3 dimension and source-bound current-mode reconstruction. Gate5 and properness are not asserted.',
              'seconds': monotonic()-started,
              'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
    source.atomic(output, result)
    signal.alarm(0)
    print({key: result[key] for key in ('status', 'additional_exact_count', 'seconds', 'peak_rss_KiB')}, flush=True)


if __name__ == '__main__':
    main()
