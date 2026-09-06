"""Check the balanced finite beta reduction of the HI cubic equations.

Run: python hi_beta_reductions.py
Export exact index representatives: python hi_beta_reductions.py --gp 199

The index orbit computations and contact-coefficient checks are exact.
Floating-point checks test the change of variables both on and off a
solution; finite existence is certified separately in PARI/GP.
"""

from collections import Counter
from itertools import permutations, product
from pathlib import Path
import argparse
from math import gcd
import re

import numpy as np
import sympy as sp


PERMS = tuple(permutations(range(3)))


def balanced_pair(quad, n):
    g, h, k, l = quad
    return (0, (k-g) % n, (l-h) % n), ((g+h) % n, -k % n, -l % n)


def cross_free(a, c, n):
    return all((x+y) % n for x in a for y in c)


def beta_orbit(quad, p):
    """All scalar-normalized S3 wr C2 transforms of a cross-free tuple."""
    a, c = balanced_pair(quad, p)
    assert cross_free(a, c, p)
    orbit = set()
    for left, right in ((a, c), (c, a)):
        for ix in PERMS:
            u = tuple(left[i] for i in ix)
            for jx in PERMS:
                v = tuple(right[j] for j in jx)
                # Shift u[0] to zero, shift the other triple oppositely.
                k, l = -(v[1]+u[0]) % p, -(v[2]+u[0]) % p
                g, h = (-v[1]-u[1]) % p, (-v[2]-u[2]) % p
                inv = pow(g, -1, p)
                orbit.add((1, h*inv % p, k*inv % p, l*inv % p))
    return orbit


def beta_representatives(p):
    """Exact coverage; primes use scalar normalization, composites full tuples."""
    if p < 3 or p % 2 == 0:
        raise ValueError("an odd order at least three is required")
    if not sp.isprime(p):
        return composite_beta_representatives(p)
    seen, reps, count = set(), [], 0
    for h, k, l in product(range(1, p-1), range(p), range(p)):
        quad = (1, h, k, l)
        a, c = balanced_pair(quad, p)
        if not cross_free(a, c, p):
            continue
        count += 1
        if quad not in seen:
            orbit = beta_orbit(quad, p)
            assert all(cross_free(*balanced_pair(q, p), p) for q in orbit)
            assert not seen.intersection(orbit)
            seen.update(orbit)
            reps.append(quad)
    assert len(seen) == count
    assert count == (p-2)*(p*p-6*p+10)
    return reps, count


def composite_beta_representatives(n):
    """Enumerate full unit/permutation orbits without dividing by a nonunit."""
    units = [u for u in range(n) if gcd(u, n) == 1]
    seen, reps, count = set(), [], 0
    for g, h, k, l in product(range(1, n), range(1, n), range(n), range(n)):
        quad = (g, h, k, l)
        a, c = balanced_pair(quad, n)
        if not cross_free(a, c, n):
            continue
        count += 1
        if quad in seen:
            continue
        orbit = set()
        for left, right in ((a, c), (c, a)):
            for ix in PERMS:
                u = tuple(left[i] for i in ix)
                for jx in PERMS:
                    v = tuple(right[j] for j in jx)
                    q = ((-v[1]-u[1]) % n, (-v[2]-u[2]) % n,
                         (-v[1]-u[0]) % n, (-v[2]-u[0]) % n)
                    for scalar in units:
                        orbit.add(tuple(scalar*x % n for x in q))
        assert not seen.intersection(orbit)
        seen.update(orbit)
        reps.append(quad)
    assert len(seen) == count == (n-1)*(n-2)*(n*n-6*n+10)
    return reps, count


def phase_matrix(b, d):
    n = len(b)
    lam, mu = np.sqrt(d)/(d-1), 1-1/d
    A = np.array([[lam*b[g]*b[(h-g) % n]*b[-h]
                   for h in range(n)] for g in range(n)])
    A[0, 0] += mu
    return A


def cubic_residual(A, d, quad):
    n = len(A)
    g, h, k, l = quad
    return (sum(A[m, (g+h) % n]*A[(m+k) % n, g].conjugate()
                * A[(m+l) % n, h].conjugate() for m in range(n))
            - A[(g+l) % n, k]*A[(h+k) % n, l]
            + (g == h == 0)/d)


def beta_terms(b, d, a, c):
    n = len(b)
    assert (sum(a)+sum(c)) % n == 0
    S = sum(np.prod([b[(m+x) % n] for x in a])
            * np.prod([b[(-m+y) % n] for y in c]) for m in range(n))
    P = np.prod([b[(x+y) % n] for x in a for y in c])
    contact = 0
    multiplicities = Counter(x % n for x in a)
    if multiplicities == Counter(-y % n for y in c):
        contact = (d-1)**3/d**2
        for multiplicity in multiplicities.values():
            for r in range(1, multiplicity+1):
                contact *= sum(d**(-j) for j in range(r))
    return S, (d-1)/np.sqrt(d)*P, contact


def beta_residual(b, d, a, c):
    S, P, contact = beta_terms(b, d, a, c)
    return S-P-contact


def contact_checks():
    d = sp.symbols("d", nonzero=True)
    n = d-1/d
    kappa = (d-1)**3/d**2
    # Match multiplicity patterns 1+1+1, 2+1, and 3.
    sums = [n-3+3/d, n-2+1/d+1/d**2, n-1+1/d**3]
    products = [-(d-1)/d**2, -(d-1)/d**3, -(d-1)/d**5]
    factors = [1, 1+1/d, (1+1/d)*(1+1/d+1/d**2)]
    for S, P, factor in zip(sums, products, factors):
        assert sp.factor(S-P-kappa*factor) == 0
    print("[ok] all three collision coefficients, as exact rational identities")


def random_phase_checks():
    for n in (3, 5, 7, 9):
        d = (n+np.sqrt(n*n+4))/2
        half = [np.exp(1j*(g*g+1)/7) for g in range(1, (n+1)//2)]
        b = np.array([-1/np.sqrt(d)]+half+[z.conjugate() for z in half[::-1]])
        A, lam = phase_matrix(b, d), np.sqrt(d)/(d-1)
        worst, nonzero = 0, 0
        for quad in product(range(n), repeat=4):
            g, h, k, l = quad
            if g == 0 or h == 0 or (g+h) % n == 0:
                continue
            a, c = balanced_pair(quad, n)
            original = cubic_residual(A, d, quad)
            converted = lam**3*b[-(g+h) % n]*b[g]*b[h]*beta_residual(b, d, a, c)
            worst = max(worst, abs(original-converted))
            nonzero = max(nonzero, abs(original))
        assert worst < 2e-13, (n, worst)
        if n > 3:
            assert nonzero > 1e-3, (n, nonzero)
    print("[ok] cubic/beta change of variables for arbitrary phases at n=3,5,7,9")


def recorded_solution_checks():
    source = Path(__file__).with_name("z13_stark_test.gp").read_text()
    match = re.search(r"jrefined = \[([^]]+)\];", source)
    j = list(map(float, match.group(1).split(",")))
    n = len(j)
    C = j[6]+j[7]
    for g in range(8, n):
        j[g] = C-j[n-g]
    d = (n+np.sqrt(n*n+4))/2
    b = np.array([-1/np.sqrt(d)]+[np.exp(-1j*(j[g]-C*g/n)) for g in range(1, n)])
    A = phase_matrix(b, d)
    worst_beta, worst_boundary = 0, 0
    for quad in product(range(n), repeat=4):
        g, h, k, l = quad
        a, c = balanced_pair(quad, n)
        worst_beta = max(worst_beta, abs(beta_residual(b, d, a, c)))
        if g == 0 or h == 0 or (g+h) % n == 0:
            worst_boundary = max(worst_boundary, abs(cubic_residual(A, d, quad)))
    assert worst_beta < 2e-12, worst_beta
    assert worst_boundary < 2e-13, worst_boundary
    print(f"[ok] every balanced beta identity at n=13; max residual {worst_beta:.3g}")
    print(f"[ok] every boundary cubic identity at n=13; max residual {worst_boundary:.3g}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", type=int, help="emit a GP vector of cubic representatives")
    args = parser.parse_args()
    if args.gp is not None:
        reps, _ = beta_representatives(args.gp)
        print(str([list(q) for q in reps]))
        return
    contact_checks()
    random_phase_checks()
    recorded_solution_checks()
    for p in (3, 5, 7, 11, 13, 17, 19, 29):
        reps, count = beta_representatives(p)
        print(f"[ok] n={p}: {count} cross-free scalar tuples covered by {len(reps)} beta orbits")
    for n, expected in ((9, 14), (15, 86), (25, 246)):
        reps, count = beta_representatives(n)
        assert len(reps) == expected
        assert count == (n-1)*(n-2)*(n*n-6*n+10)
        print(f"[ok] n={n}: all {count} cross-free tuples covered by {len(reps)} beta orbits")
    print("ALL BETA-REDUCTION CHECKS PASSED")


if __name__ == "__main__":
    main()
