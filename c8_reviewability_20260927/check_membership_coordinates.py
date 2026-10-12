"""Independently check exported membership coordinate sums; stdlib only.

Run through hi_cft_safe_run.py, with AS<=1GiB. This does not import a
research engine or verify source mode-product provenance. It verifies
literal exact vector sums and the grade/Cartan labels of their states.
Input <=30MiB, each vector <=12000 states, <=58 S3 sources, <=120 S2
sources, <=250000 total decoded states. Estimated peak <0.3GiB.
"""

import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import resource
import signal


ZERO = (Q(0),) * 4
G = [[2 * (i == j) for j in range(8)] for i in range(8)]
for i, j in ((0, 1), (1, 2), (2, 3), (3, 4), (2, 5), (6, 7)):
    G[i][j] = G[j][i] = -1
LEFT_H = (-1, -2, -3, -2, -1, -2, 0, 0)
RIGHT_H = (5, 8, 9, 8, 5, 0, 2, 2)


def plus(a, b):
    return tuple(x + y for x, y in zip(a, b))


def times(a, b):
    c = [Q(0)] * 4
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i ^ j] += x * y * (13 if i & j & 1 else 1) * (
                -3 if i & j & 2 else 1)
    return tuple(c)


def pairing(a, b):
    return sum(a[i] * G[i][j] * b[j] for i in range(8) for j in range(8))


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        assert key not in out, 'duplicate JSON object key'
        out[key] = value
    return out


def coefficient(values):
    assert len(values) == 4 and all(type(q) is str for q in values)
    answer = tuple(Q(q) for q in values)
    assert max(max(abs(q.numerator).bit_length(), q.denominator.bit_length())
               for q in answer) <= 4096
    return answer


def field(rows, grade, neutral=False):
    assert len(rows) <= 12000
    out = {}
    for row in rows:
        a, osc = tuple(row['momentum']), tuple(row['oscillators'])
        assert len(a) == 8 and all(type(i) is int for i in a)
        assert all(type(i) is int and i >= 0 for i in osc)
        assert osc == tuple(sorted(osc))
        assert pairing(a, a) + 2 * sum(1 + i // 8 for i in osc) == 2 * grade
        if neutral:
            assert pairing(LEFT_H, a) == pairing(RIGHT_H, a) == 0
        c = coefficient(row['coefficient'])
        assert len(c) == 4 and c != ZERO
        assert (a, osc) not in out, 'duplicate basis state'
        out[a, osc] = c
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert 0 < resource.getrlimit(resource.RLIMIT_AS)[0] <= 1024**3
    assert args.certificate.stat().st_size <= 30 * 1024**2
    assert not args.output.exists()
    signal.signal(signal.SIGALRM,
                  lambda *_: (_ for _ in ()).throw(TimeoutError('180s cap')))
    signal.alarm(180)
    doc = json.loads(args.certificate.read_text(), object_pairs_hook=unique_object)
    assert doc['format'] == 'explicit-grade-three-membership-v1'
    assert len(doc['S2_sources']) == 120
    assert len(doc['S3_sources']) <= 58
    assert set(doc['targets']) == {'Potts_w', 'PF13_w'}
    count = sum(len(r['vector']) for r in doc['S2_sources'] + doc['S3_sources'])
    count += sum(len(r['target']) for r in doc['targets'].values())
    assert count <= 250000
    for i, row in enumerate(doc['S2_sources']):
        assert row['index'] == i
        field(row['vector'], 2)
    sources = {}
    for i, row in enumerate(doc['S3_sources']):
        assert row['index'] == i
        sources[i] = field(row['vector'], 3, neutral=True)
    verified = {}
    for name, item in doc['targets'].items():
        target = field(item['target'], 3, neutral=True)
        total, seen = {}, set()
        for term in item['expression']:
            i = term['source_index']
            assert i not in seen and i in sources
            seen.add(i)
            scalar = coefficient(term['coefficient'])
            assert scalar != ZERO
            for basis, c in sources[i].items():
                value = plus(total.get(basis, ZERO), times(scalar, c))
                if value == ZERO:
                    total.pop(basis, None)
                else:
                    total[basis] = value
        assert total == target, name + ': coordinate sum mismatch'
        verified[name] = {'target_terms': len(target),
                          'selected_source_words': len(seen),
                          'exact_coordinate_sum': True}
    output = {
        'status': 'pass',
        'arithmetic': 'independent stdlib Fraction arithmetic in Q(sqrt13,sqrt-3)',
        'certificate_sha256': hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
        'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'targets': verified,
        'all_stored_states_have_claimed_grade': True,
        'all_S3_sources_and_targets_have_Cartan_weight_zero': True,
        'decoded_basis_rows': count,
        'peak_rss_KiB': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'scope': ('Exact exported coordinate sums and state labels only; '
                  'source mode-product provenance, source authentication, '
                  'S2 generation and VOA structure are not checked here.')}
    with args.output.open('x') as f:
        json.dump(output, f, indent=2)
        f.write('\n')
    print(json.dumps(output), flush=True)


if __name__ == '__main__':
    main()
