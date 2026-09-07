"""Replay Laurent certificates and separating functionals without elimination."""

import gzip
import json
from pathlib import Path
import resource
import time

from hi_laurent_q_certificate import MUL, add_term, cubic_polynomial, q_polynomial, shell


def replay(path):
    with (gzip.open(path, 'rt') if path.suffix == '.gz' else path.open()) as source:
        data = json.load(source)
    if 'certificates' in data:
        from hi_beta_reductions import beta_representatives
        representatives, count = beta_representatives(data['n'])
        expected = set(representatives)
        assert expected == set(map(tuple, data['representatives']))
        assert count == data['covered_count']
        actual = set()
        for certificate in data['certificates']:
            assert certificate['n'] == data['n']
            quad = tuple(certificate['quad'])
            assert quad in expected and quad not in actual
            actual.add(quad)
            replay_data(certificate)
        assert set(map(tuple, data['pending'])) == expected-actual
        if data['complete_degree_bound']:
            assert actual == expected and 'obstruction' not in data
            assert data['maximum_used_bound'] == max(
                c['multiplier_bound'] for c in data['certificates'])
        if 'obstruction' in data:
            assert data['obstruction']['n'] == data['n']
            assert tuple(data['obstruction']['quad']) in expected-actual
            replay_data(data['obstruction'])
        print(f'REPLAYED BUNDLE n={data["n"]}; '
              f'certificates={len(actual)}/{len(expected)}; '
              f'complete_degree_bound={data["complete_degree_bound"]}', flush=True)
        return
    replay_data(data)


def replay_data(data):
    n, level = data['n'], data['multiplier_bound']
    r = (n-1)//2
    target = cubic_polynomial(n, data['quad'])
    weight = lambda exponent: sum((a+1)*value for a, value in enumerate(exponent)) % n
    if 'terms' in data:
        result = {}
        for term in data['terms']:
            shift, coefficient = tuple(term['shift']), term['coefficient']
            assert len(shift) == r and sum(abs(a) for a in shift) <= level
            assert coefficient in (1, 2, 3) and weight(shift) == 0
            g, h = term['q']
            assert 1 <= g <= h <= r
            for exponent, value in q_polynomial(n, g, h).items():
                add_term(result, tuple(a+b for a, b in zip(exponent, shift)), MUL[coefficient][value])
        assert result == target
        print(f'REPLAYED identity n={n}; multiplier_bound={level}; terms={len(data["terms"])}', flush=True)
    else:
        functional = {tuple(term['exponent']): term['coefficient'] for term in data['functional']}
        assert all(weight(exponent) == 0 for exponent in functional)

        def value(poly, shift):
            result = 0
            for exponent, coefficient in poly.items():
                result ^= MUL[coefficient][functional.get(tuple(a+b for a, b in zip(exponent, shift)), 0)]
            return result

        assert value(target, (0,)*r) == 1
        generators = [q_polynomial(n, g, h) for g in range(1, r+1) for h in range(g, r+1)]
        assert all(weight(exponent) == 0 for poly in generators for exponent in poly)
        rows = 0
        for degree in range(level+1):
            for shift in shell(r, degree):
                if weight(shift):
                    continue
                for poly in generators:
                    assert value(poly, shift) == 0
                    rows += 1
        print(f'REPLAYED separating functional n={n}; multiplier_bound={level}; rows={rows}', flush=True)


def main():
    started = time.monotonic()
    paths = sorted(Path('.').glob('hi_laurent_q_*_certificate.json'))
    paths += sorted(Path('.').glob('hi_laurent_q_*_obstruction.json'))
    paths += sorted(Path('.').glob('hi_laurent_q_batch*_certificates.json'))
    paths += sorted(Path('.').glob('hi_laurent_q_batch*_certificates.json.gz'))
    for path in paths:
        replay(path)
    print(f'elapsed_seconds={time.monotonic()-started:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)


if __name__ == '__main__':
    main()
