"""Direct numerical audit of the proposed HI matrices.

This checker constructs phases from the positive-strip double-sine integral,
then sums Q and C directly. It uses no Fourier evaluation, cubic symmetry
reduction, or claimed Frobenius action. These are numerical regression checks,
not certified enclosures or a proof for unbounded orders.
"""

import argparse
from itertools import product
import random
import resource
import time

import mpmath as mp

from hi_shintani_ghost import log_double_sine


def audit(n, digits, full_limit, samples):
    # The negative-dimension matrices have large entries; direct summation
    # loses digits through cancellation as n increases.
    working_digits = digits + max(20, n//2+10)
    mp.mp.dps = working_digits
    d = (n + mp.sqrt(n*n + 4))/2
    delta = -1/d
    w = [-mp.mpf(1)] + [
        -(-1)**(a*(a+n)//2)
        * mp.exp(log_double_sine(1+d*a/(d+1), d))/mp.sqrt(d)
        for a in range(1, n)
    ]
    matrix = [[(delta-2 if a == h == 0 else
                -mp.mpf(1) if a == 0 or h == 0 or a == h else
                w[a]*w[(h-a) % n]/w[h])/(delta-1)
               for h in range(n)] for a in range(n)]
    norm = max(abs(w[a]*w[-a]-delta) for a in range(1, n))
    quadratic = max(abs(
        mp.fsum(matrix[(g+a) % n][h]*matrix[h][a] for a in range(n))
        - int(g == 0) + int(h == 0)/delta)
        for g, h in product(range(n), repeat=2))
    if n <= full_limit:
        quads = product(range(n), repeat=4)
        scope = "all"
    else:
        rng = random.Random(20260907+n)
        selected = {tuple(rng.randrange(n) for _ in range(4))
                    for _ in range(samples)}
        for t in range(n):
            selected.update({(0, 0, t, t), (0, t, 1, 2),
                             (t, -t % n, 2, 1), (1, 1, t, 1),
                             (2, n-3, t, n-3), (1, (n-1)//2, t, (n-1)//2)})
        quads = sorted(selected)
        scope = "sampled"
    cubic, count, worst = mp.mpf(0), 0, None
    for g, h, k, ell in quads:
        residual = abs(mp.fsum(
            matrix[a][(g+h) % n]*matrix[g][(a+k) % n]*matrix[h][(a+ell) % n]
            for a in range(n)) - matrix[(g+ell) % n][k]*matrix[(h+k) % n][ell]
            + int(g == h == 0)/delta)
        if residual > cubic:
            cubic, worst = residual, (g, h, k, ell)
        count += 1
    tolerance = mp.power(10, -digits+15)
    print(f"n={n}; target_digits={digits}; working_digits={working_digits}; norm={mp.nstr(norm, 8)}; "
          f"all Q={mp.nstr(quadratic, 8)}; {scope} C={mp.nstr(cubic, 8)}; "
          f"cubic_count={count}; worst={worst}", flush=True)
    assert max(norm, quadratic, cubic) < tolerance


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", nargs="+", type=int, default=[3, 5, 9, 17, 33, 65])
    parser.add_argument("--digits", type=int, default=60)
    parser.add_argument("--full-limit", type=int, default=17)
    parser.add_argument("--samples", type=int, default=1024)
    args = parser.parse_args()
    if any(n < 3 or n % 2 == 0 for n in args.orders):
        parser.error("orders must be odd and at least 3")
    start = time.monotonic()
    for n in args.orders:
        audit(n, args.digits, args.full_limit, args.samples)
    print(f"elapsed_seconds={time.monotonic()-start:.3f}")
    print(f"peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}")
    print("PASS: direct numerical residual checks; no interval certification claimed.")


if __name__ == "__main__":
    main()
