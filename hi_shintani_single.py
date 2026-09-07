"""One double sine per phase in the uniform analytic HI candidate.

Section 76 proves equivalence with the Shintani product. All integral
evaluations and additive checks here are numerical, not existence proofs.
"""

import argparse

import mpmath as mp

from hi_shintani_ghost import (cubic_representatives, cubic_residual,
                               ghost_sign, log_double_sine,
                               quadratic_residual, shintani_log)


def single_log(n, a):
    if n < 3 or n % 2 == 0 or not 0 <= a < n:
        raise ValueError('Require odd n>=3 and 0<=a<n')
    d = (n+mp.sqrt(n*n+4))/2
    return 2*log_double_sine(1+d*a/(d+1), d)


def phases(n):
    d = (n+mp.sqrt(n*n+4))/2
    W = [ghost_sign(n, a)*mp.exp((single_log(n, a)-mp.log(d))/2)
         for a in range(n)]
    return -1/d, W


def product_checks(tolerance):
    for n, b, v in [(2, '0.7', '0.3'), (3, '1.4', '0.6'), (5, '0.8', '0.4')]:
        b, v = mp.mpf(b), mp.mpf(v)
        left = mp.fsum(log_double_sine((b+v+j)/b, (b+n)/b) for j in range(n))
        right = log_double_sine(v, b)-log_double_sine(v, b+n)
        assert abs(left-right) < tolerance
        print(f'NUMERICAL off-RM product identity n={n}, b={b}, v={v}; '
              f'error={mp.nstr(abs(left-right), 6)}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 7, 11, 19, 31])
    parser.add_argument('--digits', type=int, default=60)
    args = parser.parse_args()
    mp.mp.dps = args.digits+15
    tolerance = mp.power(10, -args.digits+10)
    product_checks(tolerance)
    for n in args.orders:
        delta, W = phases(n)
        A = [[(delta-2 if g == h == 0 else
               -1 if not g or not h or g == h else W[g]*W[(h-g) % n]/W[h])/(delta-1)
              for h in range(n)] for g in range(n)]
        norm = max(abs(W[a]*W[-a]-delta) for a in range(1, n))
        origin = abs(W[0]+1)
        comparison = max(abs(single_log(n, a)-shintani_log(n, a)) for a in [1, 2])
        Q = quadratic_residual(A, delta)
        representatives, covered = cubic_representatives(n)
        C = max((cubic_residual(A, delta, quad) for quad in representatives),
                default=mp.mpf(0))
        assert max(norm, origin, comparison, Q, C) < tolerance
        print(f'NUMERICAL single-sine n={n}; old/new log error={mp.nstr(comparison, 6)}; '
              f'norm={mp.nstr(norm, 6)}; origin={mp.nstr(origin, 6)}; '
              f'all Q={mp.nstr(Q, 6)}; C={mp.nstr(C, 6)} '
              f'({len(representatives)} representatives, {covered} cross-free tuples)', flush=True)
    print('ALL REQUESTED NUMERICAL CHECKS PASSED; the uniform additive identity remains unproved.')


if __name__ == '__main__':
    main()
