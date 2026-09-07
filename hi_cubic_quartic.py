"""Exact indexing checks for the uniform cubic-to-quartic identity (Section 52).

Tests use rational matrices deliberately NOT satisfying Q or C. Thus they
verify the residual decomposition, not just vanishing on known solutions.
"""

from fractions import Fraction as F
from itertools import product
import random


def symmetric_matrix(n, delta, axes):
    rng = random.Random(5200 + n)
    A = [[None] * n for _ in range(n)]
    special = -1 / (delta - 1)
    for g, h in product(range(n), repeat=2):
        if A[g][h] is not None:
            continue
        orbit = {(g, h), (-h % n, (g - h) % n), ((h - g) % n, -g % n)}
        value = F(rng.randrange(-9, 10), rng.randrange(1, 8))
        if axes and (g == 0 or h == 0 or g == h):
            value = special + int(g == h == 0)
        for i, j in orbit:
            A[i][j] = value
    return A


def check(n, delta, axes):
    A = symmetric_matrix(n, delta, axes)
    t = 1 / delta
    Q = {(g, h): sum(A[(g + m) % n][h] * A[h][m] for m in range(n))
         - int(g == 0) + t * int(h == 0)
         for g, h in product(range(n), repeat=2)}
    C = {(g, h, k, l): sum(A[m][(g + h) % n] * A[g][(m + k) % n]
                           * A[h][(m + l) % n] for m in range(n))
         - A[(g + l) % n][k] * A[(h + k) % n][l] + t * int(g == h == 0)
         for g, h, k, l in product(range(n), repeat=4)}
    assert any(Q.values()) and any(C.values())
    for g, h, i, k in product(range(n), repeat=4):
        quartic = sum(A[l][m] * A[(l + g) % n][h] * A[(h + m) % n][(l + i) % n]
                      * A[i][(k + m) % n] for l, m in product(range(n), repeat=2))
        quartic -= A[(h - g) % n][(i - g) % n] * int(k == g)
        quartic += t * int(h == 0) * A[i][k] + t * A[g][h] * int(i == 0)
        decomposition = sum(A[i][(k + m) % n] * C[-h % n, (h + m) % n, (g - h) % n, i]
                            for m in range(n))
        decomposition += A[(i - h) % n][(g - h) % n] * Q[(g - k) % n, i]
        assert quartic == decomposition, (n, g, h, i, k)
    if axes:
        a = -1 / (delta - 1)
        for g, k in product(range(n), repeat=2):
            assert C[g, 0, k, 0] == a * Q[-k % n, g]
    print(f"EXACT off-solution residual identity: n={n}, delta={delta}, axes={axes}; "
          f"all {n**4} quartic positions passed", flush=True)


if __name__ == "__main__":
    for n, delta in [(3, F(2)), (5, F(-3, 7)), (7, F(11, 4))]:
        check(n, delta, False)
        check(n, delta, True)
    print("ALL EXACT CUBIC-TO-QUARTIC INDEXING CHECKS PASSED")
