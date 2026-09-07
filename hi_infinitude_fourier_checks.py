"""Independent algebraic and numerical audits of Section 111.

Exact checks cover the Laurent identity behind the contour primitive,
the descending cubic permutations, and the signed ordered normal form.
Numerical checks audit gamma shifts and all normalization coefficients;
the uniform existence argument is the written proof, not these samples.
"""

import argparse
from fractions import Fraction
from itertools import product
from math import prod
import resource
import time

import mpmath as mp
import sympy as sp

from hi_shintani_fourier import FourierCandidate


def exact_primitive_identity():
    ac, ae, af, t, bc, be, u, lam = sp.symbols('ac ae af t bc be u lam', nonzero=True)
    sn = lambda x: (x-1/x)/(2*sp.I)
    a = sn(af/ac)/sn(ae/ac)
    d = sn(ae/af)/sn(ae/ac)
    b = lam*sn(be)/sn(be/bc)
    c = -lam*sn(bc)/sn(be/bc)
    lhs = (a*sn(t)*sn(u)*sn(ae/t)
           +b*sn(ac/t)*sn(bc/u)*sn(ae/t)
           +c*sn(ac/t)*sn(ae/t)*sn(be/u)
           +d*sn(ac/t)*sn(t)*sn(u))
    rhs = -sn(u)*(lam*sn(ac/t)*sn(ae/t)+sn(t)*sn(t/af))
    assert sp.cancel(lhs-rhs) == 0
    print('EXACT four-term primitive: generic Laurent identity is zero.', flush=True)


def triples(n, q):
    g, h, k, ell = q
    return (0, (k-g) % n, (ell-h) % n), ((g+h) % n, -k % n, -ell % n)


def exact_balanced_factors():
    cases = 0
    for n in [3, 5, 7]:
        delta = Fraction(-2, 3)
        w = [Fraction(-1)]*n
        for a in range(1, (n+1)//2):
            w[a] = Fraction(a+2)
            w[-a] = delta/w[a]
        core = [[delta-2 if a == h == 0 else Fraction(-1)
                 if a == 0 or h == 0 or a == h else w[a]*w[(h-a) % n]/w[h]
                 for h in range(n)] for a in range(n)]
        for g, h, k, ell in product(range(1, n), repeat=4):
            a, c = triples(n, (g, h, k, ell))
            if any((x+y) % n == 0 for x in a for y in c):
                continue
            s6 = sum(prod(w[(m+x) % n] for x in a)*prod(w[(y-m) % n] for y in c)
                     for m in range(n))
            p9 = prod(w[(x+y) % n] for x in a for y in c)
            residual = (sum(core[m][(g+h) % n]*core[g][(m+k) % n]*core[h][(m+ell) % n]
                            for m in range(n))
                        -(delta-1)*core[(g+ell) % n][k]*core[(h+k) % n][ell])
            prefactor = w[(-g-h) % n]*w[g]*w[h]/delta**5
            assert residual == prefactor*(delta**2*s6-(delta-1)*p9)
            cases += 1
    print(f'EXACT cross-free residual normalization: {cases} off-solution cases.', flush=True)


def normalize(n, a, c, rows, cols):
    shift = a[rows[0]]
    aa = tuple((a[i]-shift) % n for i in rows)
    cc = tuple((c[i]+shift) % n for i in cols)
    g, h = -(aa[1]+cc[1]) % n, -(aa[2]+cc[2]) % n
    k, ell = -cc[1] % n, -cc[2] % n
    assert triples(n, (g, h, k, ell)) == (aa, cc)
    return g, h, k, ell


def exact_induction(limit):
    cases = 0
    for n in range(3, limit+1, 2):
        for g in range(1, n-1):
            excluded = []
            for j in range(n):
                v = (2*j+n*(-g-1)+n) % (2*n)-n
                if abs(v) > n-g:
                    excluded.append(j)
            assert len(excluded) == g-1
            if excluded:
                block = set(excluded)
                start = next(j for j in excluded if (j-1) % n not in block)
                assert block == {(start+t) % n for t in range(g-1)}
            for h in range(1, n-g):
                for ell in range(1, h+1):
                    for k in range(1, g):
                        a, c = triples(n, (g, h, k, ell))
                        if ell+g-k <= h:
                            q = normalize(n, a, c, (1, 0, 2), (0, 1, 2))
                            assert q == (k, h, g, ell+g-k)
                        else:
                            q = normalize(n, a, c, (2, 0, 1), (2, 1, 0))
                            assert q == (k, n-h-k, k+h-ell, n-g-ell)
                        gg, hh, _, ll = q
                        assert 1 <= gg < g and 1 <= hh and gg+hh < n and 1 <= ll <= hh
                        cases += 1
    print(f'EXACT descending permutations: {cases} cases through n={limit}; '
          'all exceptional-frequency sets are consecutive blocks.', flush=True)


def exact_normal_form(limit):
    count, negations = 0, 0
    for n in range(3, limit+1, 2):
        for q in product(range(1, n), repeat=4):
            a, c = triples(n, q)
            matrix = [[(x+y) % n for y in c] for x in a]
            if any(t == 0 for row in matrix for t in row):
                continue
            diagonal_sum = sum(matrix[j][j] for j in range(3))
            assert diagonal_sum in [n, 2*n]
            if diagonal_sum == n:
                a, c = tuple(-x % n for x in a), tuple(-x % n for x in c)
                matrix = [[(x+y) % n for y in c] for x in a]
                negations += 1
            assert sum(matrix[j][j] for j in range(3)) == 2*n
            choices = [(i, j) for i in range(3) for j in range(3)
                       if i != j and matrix[i][j] >= matrix[j][j]]
            assert choices
            i, j = choices[0]
            remaining = 3-i-j
            g, h, k, ell = normalize(n, a, c, (i, remaining, j), (i, remaining, j))
            assert g >= 1 and h >= 1 and g+h < n and 1 <= ell <= h
            count += 1
    print(f'EXACT signed normal form: {count} cross-free quadruples through n={limit}; '
          f'{negations} use simultaneous negation.', flush=True)


def numerical_primitive(n):
    c = FourierCandidate(n)
    A, B, Q = c.A, c.B, c.Q
    u, v = Q/2+mp.mpf('.2'), B/2+mp.mpf('.2')
    Y, Z, z = A/2+mp.mpf('.1'), mp.mpc('.13', '.17'), mp.mpc('.37', '.21')
    C, D, F = 2*u-Q, v+Y-u, u-v-A+Y
    E = C+D
    al, be = lambda t: mp.sin(mp.pi*t/A), lambda t: mp.sin(mp.pi*t/B)
    lam = mp.exp(2j*mp.pi*Z*B/Q)
    coeffs = [al(F-C)/al(D), lam*be(E)/be(D), -lam*be(C)/be(D), al(E-F)/al(D)]
    def parameters(z):
        return u-B+z, u-A-z, v-B+Y+z, v-Y-z
    zeta, eta, theta, nu = parameters(z)
    terms = [c.gamma(zeta)*c.gamma(eta+Q)*c.gamma(theta+B)*c.gamma(nu),
             c.gamma(zeta+Q)*c.gamma(eta)*c.gamma(theta+B)*c.gamma(nu),
             c.gamma(zeta+B)*c.gamma(eta)*c.gamma(theta+Q)*c.gamma(nu),
             c.gamma(zeta+B)*c.gamma(eta+Q)*c.gamma(theta)*c.gamma(nu)]
    lhs = mp.exp(2j*mp.pi*Z*z/Q)*mp.fsum(a*t for a, t in zip(coeffs, terms))
    def primitive(z):
        ze, et, th, nu = parameters(z)
        return mp.exp(2j*mp.pi*Z*z/Q)*c.gamma(ze)*c.gamma(th)*c.gamma(et+Q)*c.gamma(nu+B)
    error = abs(lhs/(primitive(z+B)-primitive(z))-1)
    assert error < mp.power(10, -mp.mp.dps+8)
    print(f'NUMERICAL n={n}: off-real gamma primitive error={mp.nstr(error, 8)}', flush=True)
    c.F.cache_clear()
    c.gamma.cache_clear()


def numerical_normalizations(n):
    c = FourierCandidate(n)
    Q = c.Q
    signed_error, coefficient_error = mp.mpf(0), mp.mpf(0)
    cases = 0
    for g in range(1, n):
        for j in range(n):
            omega_r = c.omega(-g, j)
            v = int(mp.nint(n*omega_r/mp.pi))
            if abs(v) > n-g:
                continue
            D = c.gamma((Q-g)/2-Q*omega_r/(2*mp.pi))*c.gamma((Q-g)/2+Q*omega_r/(2*mp.pi))
            signed = -c.B*mp.exp(1j*g*omega_r/2)*D
            signed_error = max(signed_error, abs(signed-c.direct_fourier(n-g, j)))
            if g == n-1:
                continue
            h = n-1-g
            for ell in sorted({1, h}):
                p, q, s = g+h, -h, ell-h
                pp, qq, ss = -g-ell, ell, g+h+ell
                omega = c.omega(g, -j)
                assert abs(omega+omega_r) < mp.power(10, -mp.mp.dps+3)
                y, Z = -Q*omega/(2*mp.pi), Q*omega/(2*mp.pi)
                R, X = -mp.mpf(g)/2, mp.mpf(n+g)/2+ell
                s1, s2 = -Q/2-mp.mpf(g)/2-h, Q/2-mp.mpf(g)/2-h
                G = lambda v: c.gamma(Q/2+R+v)*c.gamma(Q/2+R-v)
                cL = (-1)**(p+q+q*s)/(c.d*c.F(p)*c.F(q))
                cR = (-1)**(pp+qq+qq*ss)/(c.d*c.F(pp)*c.F(qq))
                aL, bL = (-1)**q*mp.sin(mp.pi*p/c.A), (-1)**s*mp.sin(mp.pi*q/c.A)
                aR, bR = (-1)**qq*mp.sin(mp.pi*pp/c.A), (-1)**ss*mp.sin(mp.pi*qq/c.A)
                ft = c.evaluated_fourier(n-g, j)  # independent, original principal-branch formula
                right_scale = c.B*mp.exp(-2j*mp.pi*j*ell/n)*cR
                lhs = [ft*cL*aL*mp.exp(mp.pi*1j*y*(p+s1-X)/Q)*G(s1)*G(X)/G(y),
                       ft*cL*bL*mp.exp(mp.pi*1j*y*(n+p+s2-X)/Q)*G(s2)*G(X)/G(y),
                       right_scale*aR*mp.exp(mp.pi*1j*pp*Z/Q),
                       right_scale*bR*mp.exp(mp.pi*1j*(n+pp)*Z/Q)]
                rhs = [mp.sin(mp.pi*h/c.A),
                       (-1)**(g+ell+1)*mp.sin(mp.pi*p/c.A)*mp.exp(-2j*mp.pi*Z*c.A/Q),
                       (-1)**p*mp.sin(mp.pi*(g+ell)/c.A)*mp.exp(-1j*mp.pi*Z*c.A/Q),
                       -mp.sin(mp.pi*ell/c.A)*mp.exp(-1j*mp.pi*Z*c.B/Q)]
                common = (c.B*(-1)**(g+h*(ell+1))*c.F(g+ell)/(c.d*c.F(ell))
                          *mp.exp(mp.pi*1j*Z*(c.A+ell-g)/Q))
                coefficient_error = max(coefficient_error,
                    max(abs(a/(common*b)-1) for a, b in zip(lhs, rhs)))
                cases += 1
    tolerance = mp.power(10, -mp.mp.dps+10)
    assert max(signed_error, coefficient_error) < tolerance
    print(f'NUMERICAL n={n}: signed_Fourier_error={mp.nstr(signed_error, 8)}; '
          f'{cases} coefficient quadruples, relative error={mp.nstr(coefficient_error, 8)}', flush=True)
    c.F.cache_clear()
    c.gamma.cache_clear()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--induction-limit', type=int, default=35)
    parser.add_argument('--normal-form-limit', type=int, default=17)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 5, 7, 9])
    parser.add_argument('--digits', type=int, default=32)
    args = parser.parse_args()
    mp.mp.dps = args.digits
    start = time.monotonic()
    exact_primitive_identity()
    exact_balanced_factors()
    exact_induction(args.induction_limit)
    exact_normal_form(args.normal_form_limit)
    for n in args.orders:
        numerical_primitive(n)
        numerical_normalizations(n)
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: all requested proof audits pass. Uniformity is supplied by the analytic and combinatorial proofs in Section 111.')


if __name__ == '__main__':
    main()
