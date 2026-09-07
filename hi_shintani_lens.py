"""The fixed-period lens-product expression for the Shintani candidate.

The change of variables is proved in Section 75 of the research notes.
Integral comparisons below are numerical. They do not prove the additive
HI equations or existence at any unbounded set of orders.
"""

import argparse
from fractions import Fraction

import mpmath as mp

from hi_shintani_ghost import ghost_sign, log_double_sine, shintani_log


def lens_log(n, a):
    """log(q_a), including the intrinsic origin value q_0=d."""
    if n < 3 or n % 2 == 0 or not 0 <= a < n:
        raise ValueError('Require odd n>=3 and 0<=a<n')
    d = (n + mp.sqrt(n*n+4))/2
    beta = d*d
    terms = []
    for j in range(n):
        z = (1+a*d+j*beta+(-a-1-j) % n)/n
        assert 0 < z < beta+1
        terms.append(log_double_sine(z, beta))
    return mp.fsum(terms)


def exact_checks():
    # The normalized lens gamma's phase is an integer sign. Verify the
    # derived polynomial identity off the real-multiplication locus too.
    B = lambda x, b: ((x-(b+1)/2)**2-(b*b+1)/12)/b
    for n in range(3, 60, 2):
        beta, mu = Fraction(17, 5), Fraction(7, 3)
        for m in range(n):
            mixed = sum(j*((m-j) % n) for j in range(n))
            assert mixed == (n*(n*n-1)+3*n*m*(n-m-2))//6
            difference = sum(B((mu+j*beta+(m-j) % n)/n, beta)
                             for j in range(n))-B(mu, beta)/n
            assert difference == (-Fraction((n-1)**2, 2*n)
                                  + Fraction(2*mixed, n*n))
            z_phase = (Fraction((n-1)*(n-5), 12*n)
                       + Fraction((n+1)*m*(m+2), 2*n))
            assert z_phase+difference/2 == Fraction(m*(m+3), 2)
    print('EXACT lens Bernoulli/sign identity passed off the RM locus for all odd n<=59.',
          flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 5, 7, 9, 11, 15])
    parser.add_argument('--digits', type=int, default=40)
    args = parser.parse_args()
    mp.mp.dps = args.digits+15
    exact_checks()
    tolerance = mp.power(10, -args.digits+7)
    for n in args.orders:
        d = (n+mp.sqrt(n*n+4))/2
        zero = lens_log(n, 0)
        origin_error = abs(zero-mp.log(d))
        assert origin_error < tolerance
        error = norm_error = mp.mpf(0)
        for a in sorted({1, 2, (n-1)//2, n-1}):
            value = lens_log(n, a)
            error = max(error, abs(value-shintani_log(n, a)))
            norm_error = max(norm_error, abs(value+lens_log(n, n-a)))
        origin_phase = ghost_sign(n, 0)*mp.exp((zero-mp.log(d))/2)
        assert abs(origin_phase+1) < tolerance
        assert max(error, norm_error) < tolerance
        print(f'NUMERICAL fixed-period identity n={n}; old/new log error='
              f'{mp.nstr(error, 6)}; log(q_0)-log(d)={mp.nstr(origin_error, 6)}; '
              f'inverse-norm error={mp.nstr(norm_error, 6)}; W_0=-1 recovered', flush=True)
    print('ALL REQUESTED COMPARISONS PASSED; no uniform additive HI identity is proved.')


if __name__ == '__main__':
    main()
