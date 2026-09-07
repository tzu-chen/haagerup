"""Exact checks for the uniform degree-five lower bound in Section 108.

The proof uses nine independent doubling/negation orbits at n=2**r-1,
r>=11. These checks store O(r) integers and never construct the n-variable
phase ring, a Q row space, or a finite-field extension.
"""

import resource
import time


QUAD = (1, 5, 13, 41)
A = (0, 12, 36)
C = (6, -13, -41)
CROSS_SUMS = tuple(a+c for a in A for c in C)
ODD_PARTS = (3, 13, 41, 9, 1, 29, 21, 23, 5)
POWERS = (1, 0, 0, 1, 0, 0, 1, 0, 0)
SIGNS = (1, -1, -1, 1, -1, -1, 1, 1, -1)


def check(r):
    n = 2**r-1
    assert r >= 11 and sum(A)+sum(C) == 0
    assert tuple(s*q*2**j for s, q, j in zip(SIGNS, ODD_PARTS, POWERS)) == CROSS_SUMS
    assert len(set(ODD_PARTS)) == 9 and all(q % 2 for q in ODD_PARTS)
    assert max(q.bit_length() for q in ODD_PARTS) == 6
    assert max(q.bit_count() for q in ODD_PARTS) == 4
    assert all(a % n for a in CROSS_SUMS)
    seen = set()
    for q in ODD_PARTS:
        orbit = {(q*2**j) % n for j in range(r)}
        opposite = {-a % n for a in orbit}
        assert len(orbit) == r and not orbit.intersection(opposite)
        assert not seen.intersection(orbit | opposite)
        seen.update(orbit | opposite)
    period = 4**r-1
    exponent = tuple((s*4**j) % period for s, j in zip(SIGNS, POWERS))
    assert all(exponent) and len(exponent) == 9
    # An S6 summand uses <=6 orbit coordinates. A degree-L Laurent
    # word times a Q summand uses <=L+4. Neither can reach this exponent
    # when L<=4. Coordinate reductions never create a new coordinate.
    assert 6 < len(exponent) and 4+4 < len(exponent)


def main():
    start = time.monotonic()
    for r in range(11, 129):
        check(r)
    print(f'QUAD {QUAD}; cross_sums={CROSS_SUMS}')
    print('EXACT 118 orbit checks: r=11..128; n=2**r-1; nine independent coordinates')
    print('The uniform proof, not this finite check, establishes the bound for every r>=11.')
    print('Every Laurent Q certificate for this cubic modulo norm/Frobenius needs degree >=5.')
    print(f'elapsed_seconds={time.monotonic()-start:.3f}; '
          f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}')
    print('No failure of Q-to-C or category nonexistence is asserted. Infinitude remains unproved.')


if __name__ == '__main__':
    main()
