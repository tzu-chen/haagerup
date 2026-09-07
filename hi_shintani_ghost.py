"""Evaluate the explicit Shintani candidate, without algebraic or HI seeds.

All residuals are NUMERICAL, not interval certificates or existence proofs.
The parameter is the negative dimension delta=-1/d. Consequently the formal
conjugation in the Izumi equations is matrix transposition, not complex
conjugation of these real entries. See Section 51 of the research notes.

Examples:
  python hi_shintani_ghost.py --orders 3 7 11 19 25 31 --digits 60
  python hi_shintani_ghost.py --orders 7 --digits 80 --full-cubic
"""

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import permutations, product
import json
from pathlib import Path
import time

import mpmath as mp


@lru_cache(None)
def log_sinhc_coefficient(k, precision):
    # The precision is part of the cache key because callers may change dps.
    return 2 ** (2 * k) * mp.bernoulli(2 * k) / (2 * k * mp.factorial(2 * k))


def log_sinhc(x):
    if not x:
        return mp.mpf(0)
    if abs(x) < mp.mpf("0.5"):
        square, power, result = x * x, x * x, mp.mpf(0)
        for k in range(1, mp.mp.dps + 30):
            term = log_sinhc_coefficient(k, mp.mp.prec) * power
            result += term
            if abs(term) < mp.eps * abs(result):
                return result
            power *= square
        raise ArithmeticError("log(sinh(x)/x) series did not converge")
    return mp.log(mp.sinh(x) / x)


def log_double_sine(z, beta):
    """log Sin_2(z; beta, 1), with positive periods and 0<z<beta+1."""
    if not beta > 0 or not 0 < z < beta + 1:
        raise ValueError("positive-period integral outside its convergence strip")
    a = beta + 1 - 2 * z
    if not a:
        return mp.mpf(0)

    def integrand(t):
        if not t:
            return -a * (a * a - beta * beta - 1) / (24 * beta)
        ratio_log = (log_sinhc(a * t / 2) - log_sinhc(beta * t / 2)
                     - log_sinhc(t / 2))
        return -a / beta * mp.expm1(ratio_log) / (t * t)

    return mp.quad(integrand, [0, 1, mp.inf])


def characteristic(n, a, j):
    """Exact HJ characteristic in [-1,0) x [0,1), including boundary cases."""
    r1, r2 = Fraction((j - 2) * a, n), Fraction((j - 1) * a, n)
    return r1 - r1.numerator // r1.denominator - 1, r2 % 1


def shintani_log(n, a, conjugate=False):
    if not n >= 3 or n % 2 == 0 or not 0 < a < n:
        raise ValueError("require odd n>=3 and 0<a<n")
    d = (n + mp.sqrt(n * n + 4)) / 2
    if conjugate:
        d = -1 / d
    total = mp.mpf(0)
    for j in range(n):
        beta = d + 1 if j == 0 else (d - j + 1) / (d - j)
        r1, r2 = characteristic(n, a, j)
        z = (mp.mpf(r2.numerator) / r2.denominator * beta
             - mp.mpf(r1.numerator) / r1.denominator)
        total += log_double_sine(z, beta)
    return -total


def ghost_sign(n, a):
    """The proposed sign is -i**(a*(a+n)), always real for odd n."""
    return -(-1) ** (a * (a + n) // 2)


def ghost_matrix(n, logs):
    d = (n + mp.sqrt(n * n + 4)) / 2
    delta = -1 / d
    # Both halves are evaluated independently; norm symmetry is checked below.
    w = [mp.mpf(-1)] + [ghost_sign(n, a) * mp.sqrt(mp.exp(logs[a]) / d)
                       for a in range(1, n)]
    A = [[(delta - 2 if g == h == 0 else
           -1 if not g or not h or g == h else
           w[g] * w[(h - g) % n] / w[h]) / (delta - 1)
          for h in range(n)] for g in range(n)]
    return delta, w, A


def quadratic_residual(A, delta):
    n = len(A)
    return max(abs(mp.fsum(A[(g + m) % n][h] * A[h][m] for m in range(n))
                   - (int(g == 0) - int(h == 0) / delta))
               for g, h in product(range(n), repeat=2))


def cubic_residual(A, delta, quad):
    n = len(A)
    g, h, k, l = quad
    return abs(mp.fsum(A[m][(g + h) % n] * A[g][(m + k) % n]
                       * A[h][(m + l) % n] for m in range(n))
               - A[(g + l) % n][k] * A[(h + k) % n][l]
               + int(g == h == 0) / delta)


PERMS = tuple(permutations(range(3)))


def cubic_representatives(n):
    """Complete cross-free beta coverage, WITHOUT any scalar/Galois quotient.

    Only permutations, swapping the balanced triples, and opposite translation
    are used. Collision identities follow from Q and the multiplicative ansatz.
    No arithmetic reciprocity statement is assumed for the analytic numbers.
    """
    seen, reps = set(), []
    for g, h, k, l in product(range(1, n), range(1, n), range(n), range(n)):
        quad = (g, h, k, l)
        if quad in seen:
            continue
        a, c = (0, (k - g) % n, (l - h) % n), ((g + h) % n, -k % n, -l % n)
        if any((x + y) % n == 0 for x in a for y in c):
            continue
        orbit = set()
        for left, right in ((a, c), (c, a)):
            for ix in PERMS:
                u = tuple(left[i] for i in ix)
                for jx in PERMS:
                    v = tuple(right[i] for i in jx)
                    orbit.add(((-v[1] - u[1]) % n, (-v[2] - u[2]) % n,
                               (-v[1] - u[0]) % n, (-v[2] - u[0]) % n))
        assert not seen.intersection(orbit)
        seen.update(orbit)
        reps.append(quad)
    assert len(seen) == (n - 1) * (n - 2) * (n * n - 6 * n + 10)
    return reps, len(seen)


def analytic_checks():
    beta, z = mp.mpf("1.7"), mp.mpf("0.31")
    value = log_double_sine(z, beta)
    errors = [
        abs(log_double_sine(mp.mpf("0.5"), mp.mpf(1)) - mp.log(2) / 2),
        abs(value + log_double_sine(beta + 1 - z, beta)),
        abs(log_double_sine(z + 1, beta) - value + mp.log(2 * mp.sin(mp.pi * z / beta))),
        abs(log_double_sine(z + beta, beta) - value + mp.log(2 * mp.sin(mp.pi * z))),
        abs(value - log_double_sine(z / beta, 1 / beta)),
    ]
    assert max(errors) < mp.power(10, -mp.mp.dps + 8)
    print("NUMERICAL integral reflection/shift/scaling checks:", mp.nstr(max(errors), 5), flush=True)


def run(n, digits, full_cubic=False, output=None):
    start = time.monotonic()
    logs = {a: shintani_log(n, a) for a in range(1, n)}
    delta, w, A = ghost_matrix(n, logs)
    norm_error = max(abs(mp.expm1(logs[a] + logs[n - a])) for a in logs)
    conjugate_error = abs(mp.expm1(shintani_log(n, 1, conjugate=True)))
    assert all(ghost_sign(n, n - a) == -ghost_sign(n, a) for a in logs)
    q_error = quadratic_residual(A, delta)
    reps, coverage = cubic_representatives(n)
    c_error = max((cubic_residual(A, delta, quad) for quad in reps), default=mp.mpf(0))
    full_error = None
    if full_cubic:
        full_error = max(cubic_residual(A, delta, quad)
                         for quad in product(range(n), repeat=4))
    tolerance = mp.power(10, -digits + 10)
    assert max(norm_error, conjugate_error, q_error, c_error,
               full_error or 0) < tolerance
    print(f"n={n}: q1={mp.nstr(mp.exp(logs[1]), 30)}; "
          f"norm={mp.nstr(norm_error, 5)}; conjugate product-1={mp.nstr(conjugate_error, 5)}", flush=True)
    print(f"  NUMERICAL Q={mp.nstr(q_error, 5)}; C representatives={mp.nstr(c_error, 5)}; "
          f"{len(reps)} orbits cover {coverage} cross-free tuples; "
          f"seconds={time.monotonic()-start:.2f}", flush=True)
    if full_error is not None:
        print("  independent full cubic maximum:", mp.nstr(full_error, 5), flush=True)
    result = {"n": n, "digits": digits, "q": {a: mp.nstr(mp.exp(v), digits) for a, v in logs.items()},
              "signs": [ghost_sign(n, a) for a in range(1, n)],
              "Q": mp.nstr(q_error, 10), "C_representatives": mp.nstr(c_error, 10),
              "C_full": None if full_error is None else mp.nstr(full_error, 10),
              "beta_orbits": len(reps), "coverage": coverage,
              "status": "numerical only; not an existence certificate"}
    if output:
        output.mkdir(parents=True, exist_ok=True)
        (output / f"hi_shintani_ghost{n}.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", nargs="+", type=int, default=[3, 5, 7, 9, 11, 13, 17, 19, 25])
    parser.add_argument("--digits", type=int, default=60)
    parser.add_argument("--full-cubic", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    mp.mp.dps = args.digits + 15
    print(f"Analytic Shintani ghost construction, {args.digits} requested digits + 15 guard digits.", flush=True)
    print("No polynomial seeds, unit searches, or fitted signs. Every additive check is NUMERICAL.", flush=True)
    analytic_checks()
    for n in args.orders:
        run(n, args.digits, args.full_cubic, args.output)
    print("ALL REQUESTED NUMERICAL CHECKS PASSED; infinitude and physical realization remain unproved.", flush=True)


if __name__ == "__main__":
    main()
