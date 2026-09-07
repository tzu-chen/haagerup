"""Replay Q-to-cubic identities in the full norm/Frobenius coordinate algebra.

This verifier does no row reduction and constructs Q and cubic polynomials
in the old free Laurent coordinates before substituting the phase images.
"""

import argparse
from functools import cache
import gzip
import json
from pathlib import Path
import resource
import time

from hi_beta_reductions import beta_representatives
from hi_frobenius_q_batch import MODEL, PhaseRing
from hi_laurent_q_certificate import MUL, add_term, cubic_polynomial, q_polynomial, shell
from hi_lift_q_polynomials import lift_polynomial


def replay(path):
    with gzip.open(path, 'rt') as handle:
        data = json.load(handle)
    n, ring = data['n'], PhaseRing(data['n'])
    r = (n-1)//2
    assert data['model'] == MODEL and data['omega'] == 2
    assert tuple(data['periods']) == ring.periods

    def substitute(poly):
        result = {}
        for word, coefficient in poly.items():
            exponent, scalar = ring.word(word)
            add_term(result, exponent, MUL[coefficient][scalar])
        return result

    @cache
    def q(g, h):
        result = substitute(q_polynomial(n, g, h))
        assert result == ring.q(g, h)
        return result

    @cache
    def lift(g, h):
        result = substitute(lift_polynomial(n, g, h))
        assert result == ring.lift_error(g, h)
        return result

    def target(quad):
        result = substitute(cubic_polynomial(n, quad))
        assert result == ring.cubic(quad)
        return result

    representatives, covered = beta_representatives(n)
    expected = set(representatives)
    assert set(map(tuple, data['representatives'])) == expected
    assert data['covered_count'] == covered
    actual = set()
    for cert in data['certificates']:
        assert cert['model'] == MODEL and cert['n'] == n and cert['omega'] == 2
        quad, result = tuple(cert['quad']), {}
        assert quad in expected and quad not in actual
        actual.add(quad)
        for term in cert['terms']:
            word, coefficient = tuple(term['shift']), term['coefficient']
            assert len(word) == r and sum(map(abs, word)) <= cert['multiplier_bound']
            assert coefficient in (1, 2, 3)
            shift, scalar = ring.word(word)
            coefficient = MUL[coefficient][scalar]
            assert ('q' in term) != ('lift' in term)
            if 'lift' in term:
                assert data.get('lift_errors', False)
            g, h = term['q'] if 'q' in term else term['lift']
            assert 1 <= g <= h <= r
            poly = q(g, h) if 'q' in term else lift(g, h)
            for exponent, value in poly.items():
                add_term(result, ring.plus(exponent, shift), MUL[coefficient][value])
        assert result == target(quad)
        print(f'REPLAYED identity n={n}; quad={quad}; L={cert["multiplier_bound"]}; '
              f'terms={len(cert["terms"])}', flush=True)

    assert set(map(tuple, data['pending'])) == expected-actual
    if data['complete_degree_bound']:
        assert actual == expected and 'obstruction' not in data
        assert data['maximum_used_bound'] == max(c['multiplier_bound'] for c in data['certificates'])
    if 'obstruction' in data:
        obstruction = data['obstruction']
        assert obstruction['model'] == MODEL and obstruction['n'] == n and obstruction['omega'] == 2
        assert obstruction.get('lift_errors', False) == data.get('lift_errors', False)
        quad, level = tuple(obstruction['quad']), obstruction['multiplier_bound']
        assert quad in expected-actual
        functional = {tuple(term['exponent']): term['coefficient']
                      for term in obstruction['functional']}
        assert len(functional) == len(obstruction['functional'])
        assert all(v in (1, 2, 3) and len(e) == len(ring.periods) and
                   all(0 <= a < m for a, m in zip(e, ring.periods))
                   for e, v in functional.items())

        def value(poly, shift):
            result = 0
            for exponent, coefficient in poly.items():
                result ^= MUL[coefficient][functional.get(ring.plus(exponent, shift), 0)]
            return result

        assert value(target(quad), ring.zero) == 1
        # Enumerate every original Laurent word, including all character weights.
        # Scalar factors are nonzero, so checking the normalized root word suffices.
        rows = 0
        for degree in range(level+1):
            for word in shell(r, degree):
                shift, _ = ring.word(word)
                for g in range(1, r+1):
                    for h in range(g, r+1):
                        assert value(q(g, h), shift) == 0
                        rows += 1
                        if data.get('lift_errors', False):
                            assert value(lift(g, h), shift) == 0
                            rows += 1
        print(f'REPLAYED separating functional n={n}; quad={quad}; '
              f'L={level}; original_rows={rows}', flush=True)
    print(f'REPLAYED BUNDLE n={n}; certificates={len(actual)}/{len(expected)}; '
          f'complete_degree_bound={data["complete_degree_bound"]}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='+', type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    for path in args.paths:
        replay(path)
    print(f'elapsed_seconds={time.monotonic()-start:.3f}; '
          f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)


if __name__ == '__main__':
    main()
