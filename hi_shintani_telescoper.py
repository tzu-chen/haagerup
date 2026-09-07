"""Exact rational period primitives for the quadratic double-sine kernel.

The quadratic kernel has a B-shift primitive and its reciprocal an A-shift
primitive. The cross-free cubic kernel has no rational B-shift primitive
of the same multiplicative form. Period shifts are not unit sample shifts;
none of these checks asserts the finite HI summation identities.
"""

import argparse

import mpmath as mp
import sympy as sp

from hi_shintani_meromorphic import sine


def symbolic_checks():
    x, q, p1, d1, d2 = sp.symbols('x q p1 d1 d2', nonzero=True)
    P = 1 + p1*x + q*q*d2*x*x
    D = 1 + d1*x + d2*x*x
    kappa = q*d1-p1
    assert sp.expand(D.subs(x, q*x)-P-kappa*x) == 0
    h = 1/(kappa*x)
    assert sp.cancel(q*D.subs(x, q*x)*h.subs(x, q*x)-P*h-1) == 0
    # Reciprocal kernel, with y sent to y/q by the A shift.
    v = -D.subs(x, q*x)/(kappa*x)
    assert sp.cancel(P/(q*D)*v.subs(x, x/q)-v-1) == 0
    print('EXACT generic quadratic: B primitive and reciprocal A primitive passed.', flush=True)

    # The endpoints of the Laurent operator supply the uniform degree proof.
    for r in range(2, 9):
        coefficients_p = sp.symbols(f'p0:{r}')
        coefficients_d = sp.symbols(f'd0:{r+1}')
        P = 1+sum(coefficients_p[j]*x**j for j in range(1, r))+q*q*coefficients_d[r]*x**r
        D = 1+sum(coefficients_d[j]*x**j for j in range(1, r+1))
        for k in range(-5, 5):
            expression = sp.expand(q*D.subs(x, q*x)*q**k-P)
            assert sp.expand(expression.coeff(x, 0)-(q**(k+1)-1)) == 0
            assert sp.expand(expression.coeff(x, r)-coefficients_d[r]*(q**(k+r+1)-q*q)) == 0
    print('EXACT endpoint coefficients: lower q^(k+1)-1; '
          'upper d_r*(q^(k+r+1)-q^2).', flush=True)

    # Independent exact rational linear systems, with no cross q-orbit collisions.
    for r, proots, droots in [(2, [3, 5], [7, sp.Rational(60, 7)]),
                              (3, [3, 5, 7], [11, 13, sp.Rational(420, 143)])]:
        P = sp.prod(1-x/root for root in proots)
        D = sp.prod(1-x/root for root in droots)
        assert sp.Poly(P, x).LC() == 4*sp.Poly(D, x).LC()
        for a in proots:
            for b in droots:
                quotient = sp.Rational(a)/b
                primes = set(sp.factorint(quotient.p)) | set(sp.factorint(quotient.q))
                assert primes - {2}, 'Unexpected cross q-orbit collision'
        variables = sp.symbols('h0:17')
        h = sum(variable*x**k for variable, k in zip(variables, range(-8, 9)))
        residual = sp.Poly(sp.expand(x**8*(2*D.subs(x, 2*x)*h.subs(x, 2*x)-P*h-1)), x)
        solution = sp.linsolve(residual.all_coeffs(), variables)
        if r == 2:
            assert solution != sp.EmptySet
            solved = h.subs(dict(zip(variables, next(iter(solution)))))
            expected = 1/(sp.expand(D.subs(x, 2*x)-P).coeff(x, 1)*x)
            assert sp.cancel(solved-expected) == 0
        else:
            assert solution == sp.EmptySet
        print(f'EXACT rational r={r}: Laurent degrees -8..8 '
              f'{"unique primitive" if r == 2 else "inconsistent"}.', flush=True)


def numerical_check(n):
    d = (n+mp.sqrt(n*n+4))/2
    A, B = d+1, 1+1/d
    q = mp.exp(2j*mp.pi/d)
    a, c = [0, -(n-1)], [1, n-2]
    assert sum(a+c) == 0 and all((u+v) % n for u in a for v in c)
    alpha = [mp.exp(2j*mp.pi*u/A) for u in a]
    beta = [mp.exp(2j*mp.pi*(u-n)/A) for u in c]
    P = lambda x: mp.fprod(1-u*x for u in alpha)
    D = lambda x: mp.fprod(1-x/u for u in beta)
    kappa = mp.fsum(alpha)-q*mp.fsum(1/u for u in beta)
    trigonometric = (-4*mp.exp(1j*mp.pi*sum(a)/A)
                     *mp.sin(mp.pi*(a[0]+c[0])/A)*mp.sin(mp.pi*(a[0]+c[1])/A))
    assert abs(kappa-trigonometric) < mp.sqrt(mp.eps)
    assert abs(kappa) > mp.mpf('1e-6')
    F = lambda z: sine((B+z)/B, d)
    cache = {}

    def psi(z):
        if z not in cache:
            cache[z] = mp.fprod(F(z+u) for u in a)*mp.fprod(F(u-z) for u in c)
        return cache[z]

    def primitive(z):
        x = mp.exp(2j*mp.pi*z/A)
        return psi(z)*P(x)/(kappa*x)

    def dual(z):
        y = mp.exp(-2j*mp.pi*z/B)
        return -D(q*y)/(kappa*y*psi(z))

    error = mp.mpf(0)
    for z in [mp.mpc('0.37', '0.21'), mp.mpc('1.23', '-0.17')]:
        error = max(error, abs((primitive(z+B)-primitive(z))/psi(z)-1),
                    abs((dual(z+A)-dual(z))*psi(z)-1))
        multiplier = (mp.sin(mp.pi*(z+a[0])/A)*mp.sin(mp.pi*(z+a[1])/A)
                      /(mp.sin(mp.pi*(a[0]+c[0])/A)*mp.sin(mp.pi*(a[0]+c[1])/A)))
        error = max(error, abs(primitive(z)/(psi(z)*multiplier)-1))
    print(f'NUMERICAL n={n}: direct double-sine primitive errors={mp.nstr(error, 8)}', flush=True)
    assert error < mp.power(10, -mp.mp.dps+10)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 7, 11])
    parser.add_argument('--digits', type=int, default=35)
    args = parser.parse_args()
    symbolic_checks()
    mp.mp.dps = args.digits+10
    for n in args.orders:
        assert n >= 3 and n % 2
        numerical_check(n)
    print('COMPLETE: period primitives verified; the unweighted finite Q/C sums remain unproved.')


if __name__ == '__main__':
    main()
