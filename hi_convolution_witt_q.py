"""Residue-field formulas for the first Q errors of the convolution lift.

Use length-two 2-typical Witt coordinates (a,b), representing
[a]+2[sqrt(b)]. Compute the unique quartic lift modulo 4 directly
from a canonical residue tuple, then its polynomial Q residuals.
Compare with independent arithmetic in an unramified ring modulo 4.
"""

from functools import lru_cache
import json
from pathlib import Path
import random
import resource
import time

from hi_convolution_hensel import UnramifiedRing, lift_convolution
from hi_convolution_norm_obstruction import all_phases


def witt_data(ring, n, omega, phases):
    mul = ring.ff_mul
    square = lambda a: mul(a, a)
    c = omega ^ 1
    epsilon = ((n-1)//2) % 2
    pair_sums = [0]*n
    for a in range(n):
        for b in range(a+1, n):
            pair_sums[(a+b) % n] ^= mul(phases[a], phases[b])
    second = [mul(1 ^ (c if epsilon else 0), square(phases[a])) ^
              mul(phases[a], square(pair_sums[a])) for a in range(n)]
    assert second[0] == 1
    d, e = [[0]*n for _ in range(n)], [[0]*n for _ in range(n)]
    for g in range(n):
        for h in range(n):
            if g == h == 0:
                d[g][h] = e[g][h] = c
            elif not g or not h or g == h:
                d[g][h] = omega
                e[g][h] = omega ^ (c if not epsilon else 0)
            else:
                a, b, f = g, (h-g) % n, -h % n
                d[g][h] = mul(mul(phases[a], phases[b]), phases[f])
                e[g][h] = (mul(square(mul(phases[a], phases[b])), second[f]) ^
                           mul(square(mul(phases[a], phases[f])), second[b]) ^
                           mul(square(mul(phases[b], phases[f])), second[a]))
    return second, d, e


def q_witt(ring, d, e, g, h):
    n = len(d)
    mul = ring.ff_mul
    first = second = 0
    for m in range(n):
        a, b = d[(g+m) % n][h], d[h][m]
        product = mul(a, b)
        second ^= (mul(mul(a, a), e[h][m]) ^
                   mul(mul(b, b), e[(g+m) % n][h]) ^ mul(first, product))
        first ^= product
    return first, second


def check_tuple(ring, n, omega, residues, full_q=False):
    delta, phases, _ = lift_convolution(ring, n, omega, residues)
    second, d, e = witt_data(ring, n, omega, residues)

    @lru_cache(None)
    def teich(value):
        lifted = ring.lift(value)
        for _ in range(ring.degree):
            lifted = ring.mul(lifted, lifted)
        return lifted

    def coordinates(value):
        first = ring.residue(value)
        difference = ring.sub(value, teich(first))
        assert all(coefficient % 2 == 0 for coefficient in difference)
        eta = sum(((coefficient >> 1) & 1) << i for i, coefficient in enumerate(difference))
        return first, ring.ff_mul(eta, eta)

    epsilon = ((n-1)//2) % 2
    assert coordinates(delta) == (omega, omega ^ ((omega ^ 1) if epsilon else 0))
    assert all(coordinates(phases[a]) == (residues[a], second[a]) for a in range(n))

    @lru_cache(None)
    def core(g, h):
        if g == h == 0:
            return ring.mul(delta, ring.sub(delta, ring.scalar(2)))
        if not g or not h or g == h:
            return ring.scale(delta, -1)
        return ring.mul(ring.mul(phases[g], phases[(h-g) % n]), phases[-h])

    pairs = [(g, h) for g in range(1, n) for h in range(1, n)] if full_q else [(1, 1), (1, 2)]
    for g, h in pairs:
        actual = ring.zero
        for m in range(n):
            actual = ring.add(actual, ring.mul(core((g+m) % n, h), core(h, m)))
        expected = q_witt(ring, d, e, g, h)
        assert coordinates(actual) == expected
        if full_q:
            assert expected == (0, 0)
    return len(pairs)


def main():
    started = time.monotonic()
    total = 0
    for n in (3, 5, 7, 9):
        data = json.loads(Path(f'hi_convolution_native_{n}_certificates.json').read_text())
        modulus = data['modulus']
        ring = UnramifiedRing([(modulus >> i) & 1 for i in range(modulus.bit_length())], 2)
        choices = list(all_phases(n, ring, data['delta']))
        rng = random.Random(10250+n)
        chosen = choices if n == 3 else rng.sample(choices, 8)
        for phases in chosen:
            total += check_tuple(ring, n, data['delta'], phases)
        print(f'EXACT off-solution Witt formulas n={n}; tuples={len(chosen)}', flush=True)
    for n in (3, 9, 27):
        data = json.loads(Path(f'hi_convolution_native_{n}_certificates.json').read_text())
        modulus = data['modulus']
        ring = UnramifiedRing([(modulus >> i) & 1 for i in range(modulus.bit_length())], 2)
        for record in data['records']:
            if record['q']:
                total += check_tuple(ring, n, data['delta'], record['phases'], full_q=True)
        print(f'EXACT all first-Q lift errors vanish on saved Q orbits n={n}', flush=True)
    print(f'checked_Q_coordinates={total}', flush=True)
    print(f'elapsed_seconds={time.monotonic()-started:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: explicit Witt/Q obstruction formulas; uniform completion remains unproved.')


if __name__ == '__main__':
    main()
