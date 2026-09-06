"""Check the cocycle, sign, and Fourier reductions in Sections 28--31.

Run: python hi_phase_reductions.py
Requires mpmath. The rational cocycle/sign checks are exact. The Fourier
checks use 80-digit arithmetic, including the previously recorded n=13
phases. Finite existence is certified separately by hi_stark_seedless.gp.
"""

from fractions import Fraction
from pathlib import Path
import re

import mpmath as mp


def phase_core(b, delta):
    """All entries, including axes and the origin, from one sequence."""
    n = len(b)
    lam = mp.sqrt(delta) / (delta - 1)
    mu = 1 - 1 / delta
    return [
        [lam * b[g] * b[(h - g) % n] * b[-h] + mu * (g == h == 0)
         for h in range(n)]
        for g in range(n)
    ]


def fourier_residuals(b, delta):
    """Flat-spectrum residuals; zero is the whole quadratic system."""
    n = len(b)
    target = (delta - 1) ** 2 / delta
    roots = [mp.exp(-2j * mp.pi * k / n) for k in range(n)]
    return {
        h: [abs(sum(b[t] * b[(h-t) % n] * roots[k] ** t
                    for t in range(n))) ** 2 - target for k in range(n)]
        for h in range(1, n)
    }


def verify_fourier_equivalence(b, delta):
    """Check the inverse DFT against the original equation, off solution too."""
    n = len(b)
    A = phase_core(b, delta)
    residuals = fourier_residuals(b, delta)
    worst = mp.mpf(0)
    for h in range(n):
        for g in range(n):
            original = sum(A[(t+g) % n][h] * mp.conj(A[t][h])
                           for t in range(n)) - (g == 0) + (h == 0) / delta
            transformed = 0 if h == 0 else (
                delta / (delta-1)**2 / n
                * sum(residuals[h][k] * mp.exp(2j*mp.pi*k*g/n)
                      for k in range(n))
            )
            worst = max(worst, abs(original - transformed))
    assert worst < mp.mpf("1e-70"), worst
    return max(abs(value) for row in residuals.values() for value in row)


def exact_cocycle_checks():
    for n in (3, 5, 7, 9):
        q = [Fraction(1)] + [Fraction(g+2, g+1) for g in range(1, n)]

        def V(a, b):
            return q[a % n] * q[b % n] / q[(a+b) % n]

        for a in range(n):
            for b in range(n):
                assert V(2*a, 2*b) == V(a, b)**2 * V(a+b, a+b) / V(a, a) / V(b, b)
                for c in range(n):
                    assert V(a, b)*V(a+b, c) == V(b, c)*V(a, b+c)
        product = Fraction(1)
        for c in range(2, n):
            product *= V(1, c-1)
            assert product == q[1]**c / q[c]
    print("[ok] exact cocycle duplication and higher-multiplier telescoping")


def sign_rank_checks():
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31):
        ell = next(a for a in range(2, p)
                   if len({pow(a, k, p) for k in range(p-1)}) == p-1)
        prefix = [0] * p
        for h in range(2, p):
            prefix[h] = prefix[h-1] ^ (1 << (min(h, p+1-h)-2))

        def mask(g, h):
            g, h = sorted((g, h))
            return 0 if g == 0 or g == h else prefix[h] ^ prefix[g] ^ prefix[h-g]

        pivots = {}
        for g in range(p):
            for h in range(p):
                row = mask(g, h) ^ mask(ell*g % p, ell*h % p)
                while row:
                    top = row.bit_length()-1
                    if top in pivots:
                        row ^= pivots[top]
                    else:
                        pivots[top] = row
                        break
        assert len(pivots) == (p-3)//2, (p, len(pivots))
    print("[ok] exact binary sign ranks for primes 3 through 31")


def main():
    mp.mp.dps = 80
    exact_cocycle_checks()
    sign_rank_checks()
    for n in (3, 5, 9):
        delta = (n + mp.sqrt(n*n+4))/2
        half = [mp.exp(1j * mp.mpf(g*g+1)/7) for g in range(1, (n+1)//2)]
        b = [-1/mp.sqrt(delta)] + half + [mp.conj(x) for x in half[::-1]]
        assert verify_fourier_equivalence(b, delta) > mp.mpf("1e-3")
    print("[ok] Fourier equivalence for arbitrary phases at n=3,5,9")

    source = Path(__file__).with_name("z13_stark_test.gp").read_text()
    match = re.search(r"jrefined = \[([^]]+)\];", source)
    assert match is not None
    j = list(map(mp.mpf, match.group(1).split(",")))
    n = len(j)
    assert n == 13
    C = j[6] + j[7]
    for g in range(8, n):
        j[g] = C - j[n-g]
    delta = (n + mp.sqrt(n*n+4))/2
    b = [-1/mp.sqrt(delta)] + [mp.exp(-1j*(j[g]-C*g/n)) for g in range(1, n)]
    residual = verify_fourier_equivalence(b, delta)
    assert residual < mp.mpf("1e-70"), residual
    print("[ok] n=13 recorded phases satisfy (Q); max residual =", mp.nstr(residual, 8))
    print("ALL PHASE-REDUCTION CHECKS PASSED")


if __name__ == "__main__":
    main()
