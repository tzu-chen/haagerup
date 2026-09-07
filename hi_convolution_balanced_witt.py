"""Degree-eleven balanced formulas for the first Q lift obstruction.

Check the explicit comparison with the degree-fifteen matrix formula,
including its nonzero error terms away from Q, and compare with actual
balanced quartics in the unramified integer ring modulo 4.
"""

from functools import lru_cache
import json
from pathlib import Path
import random
import resource
import time

from hi_convolution_hensel import UnramifiedRing, lift_convolution
from hi_convolution_norm_obstruction import all_phases
from hi_convolution_witt_q import witt_data, q_witt


def pair_sums(ring, phases):
    n = len(phases)
    result = [0]*n
    for a in range(n):
        for b in range(a+1, n):
            result[(a+b) % n] ^= ring.ff_mul(phases[a], phases[b])
    return result


def balanced_lift_error(ring, phases, U, g, h):
    n = len(phases)
    mul = ring.ff_mul
    first = second = 0
    for m in range(n):
        indices = [m, (h-m) % n, (-m-g) % n, (m+g-h) % n]
        term = 1
        for a in indices:
            term = mul(term, phases[a])
        second ^= mul(first, term)
        first ^= term
        for slot, a in enumerate(indices):
            other = 1
            for position, b in enumerate(indices):
                if position != slot:
                    other = mul(other, phases[b])
            second ^= mul(phases[a], mul(mul(other, other), mul(U[a], U[a])))
    return first, second


def check(n):
    data = json.loads(Path(f'hi_convolution_native_{n}_certificates.json').read_text())
    modulus, omega = data['modulus'], data['delta']
    ring = UnramifiedRing([(modulus >> i) & 1 for i in range(modulus.bit_length())], 2)
    mul = ring.ff_mul
    square = lambda a: mul(a, a)
    c = omega ^ 1
    epsilon = ((n-1)//2) % 2
    choices = list(all_phases(n, ring, omega))
    if len(choices) > 20:
        choices = random.Random(10300+n).sample(choices, 20)
    checks = actual_checks = 0
    for number, phases in enumerate(choices):
        U = pair_sums(ring, phases)
        _, d, e = witt_data(ring, n, omega, phases)
        if number < 2:
            delta, lifted, _ = lift_convolution(ring, n, omega, phases)

            @lru_cache(None)
            def teich(value):
                result = ring.lift(value)
                for _ in range(ring.degree):
                    result = ring.mul(result, result)
                return result

        for g in range(1, n):
            for h in range(1, n):
                f, L = balanced_lift_error(ring, phases, U, g, h)
                q, K = q_witt(ring, d, e, g, h)
                assert q == mul(omega, f)
                r = h*pow(2, -1, n) % n
                O = c ^ (omega if epsilon else 0) ^ mul(c,
                    mul(square(phases[r]), U[-h]) ^ mul(square(phases[-r]), U[h]))
                E = 0
                for indices in ((h, -g-h, g), (h, -g, g-h),
                                (g, h-g, -h), (g+h, -g, -h)):
                    term = 1
                    for a in indices:
                        term = mul(term, phases[a % n])
                    E ^= term
                expected = mul(c, L) ^ mul(omega ^ (c if epsilon else 0), square(f))
                expected ^= mul(square(O), square(f ^ E))
                assert K == expected
                checks += 1
                if number < 2 and g == 1:
                    value = ring.zero
                    for m in range(n):
                        term = ring.one
                        for a in (m, h-m, -m-g, m+g-h):
                            term = ring.mul(term, lifted[a % n])
                        value = ring.add(value, term)
                    assert ring.residue(value) == f
                    difference = ring.sub(value, teich(f))
                    assert all(coefficient % 2 == 0 for coefficient in difference)
                    eta = sum(((coefficient >> 1) & 1) << i for i, coefficient in enumerate(difference))
                    assert square(eta) == L
                    actual_checks += 1
    print(f'EXACT n={n}; tuples={len(choices)}; comparison_identities={checks}; '
          f'direct_integer_ring_checks={actual_checks}', flush=True)


def main():
    start = time.monotonic()
    for n in (3, 5, 7, 9):
        check(n)
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: degree-eleven obstruction and exact Q-ideal comparison; no uniform cubic certificate.')


if __name__ == '__main__':
    main()
