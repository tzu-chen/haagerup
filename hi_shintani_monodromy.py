"""Check the rational monodromy reduction for the HI summation kernels.

The n-shift is controlled by a rational function of degree two for Q and
degree three for C. This is a meromorphic identity, not the finite sum.
"""

import argparse

import mpmath as mp
import sympy as sp

from hi_shintani_meromorphic import sine


def bezout_checks():
    x, y = sp.symbols('x y')
    for r in [2, 3]:
        p = sp.symbols(f'p1:{r+1}')
        q = sp.symbols(f'q1:{r+1}')
        P = 1+sum(p[j-1]*x**j for j in range(1, r+1))
        D = 1+sum(q[j-1]*x**j for j in range(1, r+1))
        numerator = sp.expand(P*D.subs(x, y)-P.subs(x, y)*D)
        quotient, remainder = sp.div(numerator, x-y, x)
        assert remainder == 0
        poly = sp.Poly(quotient, x, y)
        matrix = sp.Matrix(r, r, lambda i, j: poly.coeff_monomial(x**i*y**j))
        assert matrix == matrix.T
        assert sp.expand(matrix.det()-(-1)**(r*(r-1)//2)*sp.resultant(P, D, x)) == 0
        diagonal = sp.expand(quotient.subs(y, x))
        assert sp.expand(diagonal-(sp.diff(P, x)*D-P*sp.diff(D, x))) == 0
        print(f'EXACT generic r={r}: Bezout division, symmetry, diagonal, '
              'and resultant determinant passed.', flush=True)


def numerical_check(n, a, c):
    r = len(a)
    assert len(c) == r and sum(a)+sum(c) == (r-2)*n
    d = (n+mp.sqrt(n*n+4))/2
    A, B = d+1, 1+1/d
    q = mp.exp(2*mp.pi*1j/d)
    alpha = [mp.exp(2*mp.pi*1j*v/A) for v in a]
    beta = [mp.exp(2*mp.pi*1j*(v-n)/A) for v in c]
    P = lambda x: mp.fprod(1-v*x for v in alpha)
    D = lambda x: mp.fprod(1-x/v for v in beta)
    H = lambda x: P(x)/D(x)
    F = lambda x: sine((B+x)/B, d)
    psi = lambda z: mp.fprod(F(z+x) for x in a)*mp.fprod(F(x-z) for x in c)
    error = max(abs(mp.fprod(alpha)*mp.fprod(beta)-q*q), mp.mpf(0))
    for z in [mp.mpc('0.37', '0.21'), mp.mpc('-0.23', '-0.19')]:
        x = mp.exp(2*mp.pi*1j*z/A)
        y = mp.exp(-2*mp.pi*1j*z/B)
        t = mp.exp(2*mp.pi*1j*z)
        before, after = psi(z), psi(z+n)
        ratio = H(x)/H(y)
        error = max(error, abs(after/(before*ratio)-1))
        bezout = (P(x)*D(y)-P(y)*D(x))/(x-y)
        reduced = before*y*bezout/(D(x)*P(y))
        error = max(error, abs((after-before)/(t-1)/reduced-1))
    return error


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 7, 11])
    parser.add_argument('--digits', type=int, default=35)
    args = parser.parse_args()
    bezout_checks()
    mp.mp.dps = args.digits+15
    tolerance = mp.power(10, -args.digits+8)
    for n in args.orders:
        if n < 3 or n % 2 == 0:
            raise ValueError('Require odd n>=3')
        # A complete-Q kernel and a cross-free cubic kernel; integer lifts
        # satisfy exactly the sum required for each number of factors.
        for a, c in [([0, 1], [1, -2]),
                     ([0, 0, (n+3)//2], [-1, -1, (n+1)//2])]:
            assert all((x+y) % n for x in a for y in c)
            error = numerical_check(n, a, c)
            assert error < tolerance
            print(f'NUMERICAL n={n}, r={len(a)}: rational monodromy and '
                  f'Bezout reduction error={mp.nstr(error, 6)}', flush=True)
    print('ALL MONODROMY CHECKS PASSED; unweighted finite Q/C sums remain unproved.')


if __name__ == '__main__':
    main()
