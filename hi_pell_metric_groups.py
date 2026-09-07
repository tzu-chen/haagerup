#!/usr/bin/env python3
"""Small checks of the uniform proofs in Sections 105--106 of the notes.

No category or associator is constructed. All lattice and twist comparisons
use exact rational arithmetic; Gauss sums and modular matrices are numerical
cross-checks of the separate written proofs.
"""

from fractions import Fraction as F
from math import cos, sin, pi, sqrt, gcd, fsum
from random import Random
from functools import reduce
import resource
import time


I = ((1, 0), (0, 1))
J = ((0, -1), (1, 0))


def mul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))


def tr(a):
    return tuple(zip(*a))


def add(a, b, sign=1):
    return tuple(tuple(x + sign * y for x, y in zip(r, s))
                 for r, s in zip(a, b))


def scale(a, c):
    return tuple(tuple(c * x for x in r) for r in a)


def det(a):
    return a[0][0] * a[1][1] - a[0][1] * a[1][0]


def inv(a):
    return scale(((a[1][1], -a[0][1]), (-a[1][0], a[0][0])),
                 F(1, det(a)))


def pairing(b, v, w):
    return sum(v[i] * b[i][j] * w[j] for i in range(2) for j in range(2)) % 1


def odd_half(x):
    x %= 1
    assert x.denominator % 2
    return F(x.numerator * pow(2, -1, x.denominator), x.denominator) % 1


def exp_turn(a, modulus):
    angle = 2 * pi * (a % modulus) / modulus
    return complex(cos(angle), sin(angle))


def gauss(coefficient, modulus):
    values = [exp_turn(coefficient * u * u, modulus) for u in range(modulus)]
    return complex(fsum(z.real for z in values), fsum(z.imag for z in values)) / sqrt(modulus)


def modular_check(n):
    """The Grossman--Izumi blocks, without any assumed categorification."""
    D = n * n + 4
    t = pow(2, -1, D)
    # Use hyperbolic coordinates q_A(x,y)=xy/n.
    A = [(x, y) for x in range(n) for y in range(n)
         if (x, y) < ((-x) % n, (-y) % n)]
    G = list(range(1, (D + 1) // 2))
    rank = 2 + len(A) + len(G)
    assert rank == n * n + 3
    a, b = 1 / n, 1 / sqrt(D)
    S = [[0j] * rank for _ in range(rank)]
    S[0][0] = S[1][1] = (a - b) / 2
    S[0][1] = S[1][0] = (a + b) / 2
    for i, v in enumerate(A, 2):
        S[0][i] = S[i][0] = S[1][i] = S[i][1] = a
        for j, w in enumerate(A, 2):
            z = exp_turn(v[0] * w[1] + v[1] * w[0], n)
            S[i][j] = 2 * a * z.real
    offset = 2 + len(A)
    for i, u in enumerate(G, offset):
        S[0][i] = S[i][0] = b
        S[1][i] = S[i][1] = -b
        for j, v in enumerate(G, offset):
            z = exp_turn(-n * u * v, D)
            S[i][j] = -2 * b * z.real
    T = [1, 1] + [exp_turn(x * y, n) for x, y in A]
    T += [exp_turn(-n * t * u * u, D) for u in G]
    v = [1, 1] + [2 * (y == 0) for x, y in A] + [0] * len(G)
    # Adjunction Gram matrix from S alone. Compare to the full proposed
    # branching matrix, including all cross terms, not just dimensions.
    active = [k for k in range(rank) if v[k]]
    gram = [[sum(S[i][k] * S[j][k] * v[k] / S[0][k] for k in active)
             for j in range(rank)] for i in range(rank)]
    rows = [[0] * (2 * n) for _ in range(rank)]
    rows[0][0] = rows[1][0] = 1
    rows[1][n:] = [1] * n
    for i, (x, y) in enumerate(A, 2):
        rows[i][y] += 1
        rows[i][(-y) % n] += 1
        rows[i][n:] = [1] * n
    for i in range(offset, rank):
        rows[i][n:] = [1] * n
    expected_gram = mul(rows, tr(rows))
    gram_error = max(abs(gram[i][j] - expected_gram[i][j])
                     for i in range(rank) for j in range(rank))
    assert gram_error < 1e-10
    S2 = mul(S, S)
    ST = tuple(tuple(S[i][j] * T[j] for j in range(rank)) for i in range(rank))
    ST3 = mul(mul(ST, ST), ST)
    s_error = max(abs(S2[i][j] - (i == j))
                  for i in range(rank) for j in range(rank))
    st_error = max(abs(ST3[i][j] - (i == j))
                   for i in range(rank) for j in range(rank))
    # Isotropic line L={(x,0)}; this is a vector, not an algebra structure.
    sv_error = max(abs(sum(S[i][j] * v[j] for j in range(rank)) - v[i])
                   for i in range(rank))
    tv_error = max(abs(T[i] * v[i] - v[i]) for i in range(rank))
    assert max(s_error, st_error, sv_error, tv_error) < 1e-11
    return rank, s_error, st_error, sv_error, tv_error, gram_error


def main():
    start = time.monotonic()
    rng = Random(105)
    exact_checks = 0
    max_gauss_error = 0
    for n in range(3, 102, 2):
        D = n * n + 4
        M = ((n, 1), (1, 0))
        P = mul(M, M)
        L = ((1, n), (0, 1))
        R = ((1, 0), (n, 1))
        source_S = ((0, 1), (-1, 0))
        source_T_minus_n = ((1, 0), (-n, 1))
        phi = mul(mul(mul(source_S, source_T_minus_n), source_S), R)
        assert P == mul(L, R)
        assert phi == scale(P, -1)
        assert mul(mul(tr(P), J), P) == J
        assert add(P, I, -1) == scale(M, n)
        assert reduce(gcd, (abs(x) for r in add(P, I) for x in r)) == 1
        assert det(add(P, I)) == D
        # Trace Gram matrix in the order basis (d,1).
        assert add(P, I) == ((n * n + 2, n), (n, 2))
        assert gcd(n, D) == 1
        t_n, t_D = pow(2, -1, n), pow(2, -1, D)
        for sign in (-1, 1):
            K = add(P, I, sign)
            B = mul(J, inv(K))
            assert add(B, tr(B), -1) == scale(J, sign)
            assert mul(tr(K), B) == scale(mul(J, inv(P)), sign)
            expected = ((F(-1, n), 1), (0, F(1, n))) if sign == -1 else (
                (F(n, D), F(-n * n - 2, D)), (F(2, D), F(-n, D)))
            assert B == expected
            for _ in range(60):
                v = tuple(rng.randrange(-2 * D, 2 * D) for _ in range(2))
                w = tuple(rng.randrange(-2 * D, 2 * D) for _ in range(2))
                z = tuple(rng.randrange(-5, 6) for _ in range(2))
                vz = tuple(v[i] + sum(K[i][j] * z[j] for j in range(2))
                           for i in range(2))
                assert pairing(B, vz, w) == pairing(B, v, w)
                assert pairing(B, w, vz) == pairing(B, w, v)
                q = odd_half(pairing(B, v, v))
                if sign == -1:
                    x, y = v
                    target = F(t_n * (-x * x + y * y), n) % 1
                    norm_z = -x * x + n * x * y + y * y
                    assert target == F(t_n * norm_z, n) % 1
                    U, V = (y - x) % n, (t_n * (y + x)) % n
                    assert target == F(U * V, n) % 1
                    pre_galois = F(-x * x + y * y, n)
                    assert (pow(2, -1, n * D) * pre_galois) % 1 == target
                else:
                    x, y = v
                    u = (y + n * t_D * x) % D
                    uz = (vz[1] + n * t_D * vz[0]) % D
                    assert u == uz
                    target = F(-n * t_D * u * u, D) % 1
                    trace_d_z_squared = ((n ** 3 + 3 * n) * x * x
                                         + 2 * (n * n + 2) * x * y + n * y * y)
                    assert target == odd_half(F(-trace_d_z_squared, D))
                    pre_galois = F(-n * u * u, D)
                    assert (pow(2, -1, n * D) * pre_galois) % 1 == target
                assert q == target
                dv = (n * v[0] + v[1], v[0])
                assert odd_half(pairing(B, dv, dv)) == (-q) % 1
                exact_checks += 1
        for m in (1, 2, 3):
            # The hyperbolic double Gauss sum is exactly gcd(m,n).
            a_gauss = gcd(m, n)
            gamma_gauss = gauss(-n * t_D * m, D)
            expected_gamma = -1 if m == 1 or (m == 3 and n % 3 == 0) else 1
            max_gauss_error = max(max_gauss_error, abs(gamma_gauss - expected_gamma))
            if m in (2, 3):
                assert abs(abs(a_gauss + gamma_gauss) ** 2 / 4 - 1) < 1e-10
    assert max_gauss_error < 1e-11
    print("Odd orders 3 through 101: 50 exact lattice/matrix checks.")
    print(f"Exact randomized quotient, pairing, form, and Galois comparisons: {exact_checks}.")
    print(f"Gauss sums at multipliers 1,2,3: max error {max_gauss_error:.3e}.")
    for n in (3, 5, 7, 9):
        rank, s_error, st_error, sv_error, tv_error, gram_error = modular_check(n)
        print(f"n={n}, rank={rank}: S^2 {s_error:.3e}, (ST)^3 {st_error:.3e}, "
              f"Sv-v {sv_error:.3e}, Tv-v {tv_error:.3e}, Gram {gram_error:.3e}.")
    print("These checks do not construct associators or a Lagrangian algebra.")
    print(f"Elapsed {time.monotonic()-start:.3f}s; peak RSS "
          f"{resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f} MiB.")


if __name__ == "__main__":
    main()
