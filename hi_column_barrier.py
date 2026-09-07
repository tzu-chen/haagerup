"""Construct the canonical real one-column solution by a concave barrier.

Section 53 proves existence, uniqueness in this chamber, and algebraicity
for every odd n. Only ONE complete quadratic column is proved uniformly.
Checks of the other columns and the cubics are numerical conjecture tests.
Neither a Stark value nor an HI seed is used to construct the solution.
"""

import argparse
import json
from pathlib import Path
import time

import mpmath as mp

from hi_shintani_ghost import cubic_representatives, cubic_residual, quadratic_residual


def barrier_solution(n, digits, coordinate_signs=None):
    if n < 3 or n % 2 == 0:
        raise ValueError("require odd n >= 3")
    m, h = (n - 1) // 2, (n + 1) // 2
    if coordinate_signs is None:
        coordinate_signs = [(-1) ** (a + 1) for a in range(2, h + 1)]
    if len(coordinate_signs) != m or any(value not in (-1, 1) for value in coordinate_signs):
        raise ValueError("coordinate_signs must contain (n-1)/2 signs")
    d = (n + mp.sqrt(n * n + 4)) / 2
    delta, gamma = -1 / d, (d - 1) / (d + 1)
    multiplicities = [2] * (m - 1) + [1]
    spectral_multiplicities = [1] + [2] * m
    base = mp.matrix([2 * mp.cos(mp.pi * k / n) for k in range(m + 1)])
    L = mp.matrix(m + 1, m)
    for k in range(m + 1):
        for j, a in enumerate(range(2, h + 1)):
            L[k, j] = (-(-1) ** k) * coordinate_signs[j] * multiplicities[j] * mp.cos(
                2 * mp.pi * k * (a - h) / n)
    epsilon = min(base[k] / (2 * (1 + mp.fsum(max(mp.mpf(0), -L[k, j])
                                             for j in range(m)))) for k in range(m + 1))
    x = mp.matrix([epsilon] * m)

    def objective(point):
        y = base + L * point
        if min(point) <= 0 or min(y) <= 0:
            return mp.ninf
        return (mp.fsum(spectral_multiplicities[k] * mp.log(y[k]) for k in range(m + 1))
                + gamma * mp.fsum(multiplicities[j] * mp.log(point[j]) for j in range(m)))

    for iteration in range(100):
        y = base + L * x
        gradient = (L.T * mp.matrix([spectral_multiplicities[k] / y[k] for k in range(m + 1)])
                    + mp.matrix([gamma * multiplicities[j] / x[j] for j in range(m)]))
        if max(abs(value) for value in gradient) < mp.power(10, -digits):
            break
        minus_hessian = (
            L.T * mp.diag([spectral_multiplicities[k] / y[k] ** 2 for k in range(m + 1)]) * L
            + mp.diag([gamma * multiplicities[j] / x[j] ** 2 for j in range(m)]))
        step = mp.lu_solve(minus_hessian, gradient)
        decrement = mp.fdot(gradient, step)
        rate, old_value = mp.mpf(1), objective(x)
        for _ in range(200):
            trial = x + rate * step
            value = objective(trial)
            # Below objective precision, use the feasible Newton step itself.
            if value != mp.ninf and (decrement < mp.sqrt(mp.eps)
                                     or value >= old_value + mp.mpf("0.01") * rate * decrement):
                x = trial
                break
            rate /= 2
        else:
            raise ArithmeticError("Newton line search failed")
    else:
        raise ArithmeticError("Newton iteration did not converge")

    column = [mp.mpf(-1)] * n
    for j, a in enumerate(range(2, h + 1)):
        column[a] = column[(1 - a) % n] = coordinate_signs[j] * x[j]
    row = {a: delta / column[a] for a in range(2, n)}
    nth_power = delta * mp.fprod(row.values())
    first = mp.sign(nth_power) * mp.root(abs(nth_power), n)
    w = [mp.mpf(-1), first]
    for a in range(2, n):
        w.append(first * w[-1] / row[a])
    A = [[(delta - 2 if g == h0 == 0 else -1 if not g or not h0 or g == h0
           else w[g] * w[(h0 - g) % n] / w[h0]) / (delta - 1)
          for h0 in range(n)] for g in range(n)]
    return delta, w, A, iteration, min(x), min(base + L * x)


def run(n, digits, cubic, compare, output):
    start = time.monotonic()
    delta, w, A, iterations, min_x, min_y = barrier_solution(n, digits)
    nerr = max(abs(w[a] * w[n - a] / delta - 1) for a in range(1, n))
    colerr = max(abs(mp.fsum(A[(g + a) % n][1] * A[1][a] for a in range(n)) - int(g == 0))
                 for g in range(n))
    allerr = quadratic_residual(A, delta)
    assert nerr < mp.power(10, -digits + 10) and colerr < mp.power(10, -digits + 10)
    assert all(mp.sign(w[a]) == -(-1) ** (a * (a + n) // 2) for a in range(1, n))
    print(f"n={n}: Newton steps={iterations}; chamber margins "
          f"x={mp.nstr(min_x, 6)}, y={mp.nstr(min_y, 6)}", flush=True)
    print(f"  NUMERICAL norm={mp.nstr(nerr, 6)}; proved column Q={mp.nstr(colerr, 6)}; "
          f"conjectural all-column Q={mp.nstr(allerr, 6)}", flush=True)
    reps, coverage, cerr = [], None, None
    if cubic == "orbits":
        reps, coverage = cubic_representatives(n)
    elif cubic == "sample":
        reps = [(0, 0, 0, 0), (1, 0, 1, 0), (1, 1, 2 % n, 2 % n)]
        reps += [tuple(x % n for x in quad) for quad in
                 [(1, 2, 3, 4), (1, 3, 5, 7), (2, 4, 6, 8), (5, 9, 13, 17), (11, 23, 37, 41)]]
    if reps:
        cerr = max(cubic_residual(A, delta, quad) for quad in reps)
        print(f"  NUMERICAL conjectural C ({cubic}, {len(reps)} tests)={mp.nstr(cerr, 6)}"
              + (f"; {coverage} cross-free tuples covered" if coverage is not None else ""), flush=True)
    q = {a: -w[a] ** 2 / delta for a in range(1, n)}
    if compare is not None:
        saved = compare / f"hi_shintani_ghost{n}.json"
        if saved.exists():
            old = json.loads(saved.read_text())
            error = max(abs(q[a] / mp.mpf(old["q"][str(a)]) - 1) for a in q)
            print(f"  comparison to separately evaluated double sines: {mp.nstr(error, 6)}", flush=True)
    print(f"  q1={mp.nstr(q[1], 30)}; seconds={time.monotonic()-start:.2f}", flush=True)
    if output is not None:
        output.mkdir(parents=True, exist_ok=True)
        data = {"n": n, "digits": digits, "q": {a: mp.nstr(value, digits) for a, value in q.items()},
                "Q": mp.nstr(allerr, 12), "C": None if cerr is None else mp.nstr(cerr, 12),
                "cubic_checks": cubic, "status": "numerical; only one column has a uniform proof"}
        (output / f"hi_column_barrier{n}.json").write_text(json.dumps(data, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[3, 5, 7, 9, 11, 13, 19, 25, 31])
    parser.add_argument("--digits", type=int, default=60)
    parser.add_argument("--cubic", choices=["orbits", "sample", "none"], default="orbits")
    parser.add_argument("--compare-shintani", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    mp.mp.dps = args.digits + 30
    print("Concave-barrier construction: no Stark or HI seeds. Residual measurements are NUMERICAL.", flush=True)
    for n in args.orders:
        run(n, args.digits, args.cubic, args.compare_shintani, args.output)
    print("REQUESTED BARRIER CONSTRUCTIONS FINISHED; full existence is not proved uniformly.", flush=True)


if __name__ == "__main__":
    main()
