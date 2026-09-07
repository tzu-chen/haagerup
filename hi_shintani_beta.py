"""Numerical normalization check for the proved shifted beta integral (77.9).

This checks a continuous integral. It does not prove its proposed relation
to the finite HI sum (77.10). Quadrature errors are not interval-certified.
"""

import argparse

import mpmath as mp

from hi_shintani_meromorphic import log_sine_strip, sine


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=3)
    parser.add_argument('--digits', type=int, default=28)
    parser.add_argument('--nodes', type=int, nargs='+', default=[32, 64])
    parser.add_argument('--cutoff', type=str, default='8')
    args = parser.parse_args()
    n = args.order
    if n < 3 or n % 2 == 0:
        raise ValueError('Require odd n>=3')
    mp.mp.dps = args.digits
    d = (n+mp.sqrt(n*n+4))/2
    A, B = d+1, 1+1/d
    half = mp.mpf('0.5')
    a = [-half, -half, n*half+1]
    assert abs(2*sum(a)-n) < mp.eps
    S = lambda u: sine(u/B, d)
    rhs = (2*mp.sin(mp.pi*(A-2*a[2])/B)
           /(2*mp.sin(-mp.pi/B))**4
           *mp.fprod(S(B+x+y) for x in a for y in a))
    print(f'NUMERICAL n={n}; symmetric parameters a=c={a}; '
          f'four-shift beta RHS={mp.nstr(rhs, 24)}', flush=True)
    cutoff = mp.mpf(args.cutoff)
    for count in args.nodes:
        nodes, weights = mp.gauss_quadrature(count, 'legendre')
        value = mp.mpf(0)
        for node, weight in zip(nodes, weights):
            y = cutoff*(node+1)/2
            logv = (4*log_sine_strip((B-half+1j*y)/B, d).real
                    +2*log_sine_strip((B+a[2]+1j*y)/B, d).real
                    -4*mp.log(abs(2*mp.sin(mp.pi*(-half+1j*y)/B))))
            value += weight*mp.exp(logv)
        # The two halves of the imaginary axis are conjugate.
        value *= cutoff/mp.sqrt(A*B)
        error = abs(value-rhs)
        print(f'NUMERICAL nodes={count}; cutoff={cutoff}; integral='
              f'{mp.nstr(value, 24)}; error={mp.nstr(error, 8)}', flush=True)
    assert error < mp.mpf('1e-10')
    print('CONTINUOUS BETA NORMALIZATION CHECK PASSED; finite HI summation remains unproved.')


if __name__ == '__main__':
    main()
