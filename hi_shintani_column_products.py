"""Checks for the product Fourier reduction and Euler identity in Section 110.

The finite reindexing and the six-step Euler word are checked exactly.
Double-sine and optional contour checks are numerical, not certificates
of quadrature accuracy. The completed uniform argument is in Section 111.
"""

import argparse
from collections import Counter
from fractions import Fraction
import resource
import time

import mpmath as mp

from hi_shintani_fourier import FourierCandidate


def euler_word():
    state = (1, 2, 3, 4)  # signed variables r, s, x, y
    phase, gammas = Counter(), Counter()

    def product(a, b, coefficient):
        sign = (1 if a > 0 else -1)*(1 if b > 0 else -1)
        phase[tuple(sorted((abs(a), abs(b))))] += coefficient*sign

    def pair(r, v, coefficient):
        for sign in [-1, 1]:
            offset = [0]*4
            offset[abs(r)-1] += 1 if r > 0 else -1
            offset[abs(v)-1] += sign*(1 if v > 0 else -1)
            first = next(t for t in offset if t)
            # gamma(Omega/2-u) = 1/gamma(Omega/2+u).
            orientation = 1 if first > 0 else -1
            gammas[tuple(orientation*t for t in offset)] += coefficient*orientation

    for move in 'DPDPDP':
        r, s, x, y = state
        if move == 'P':
            product(y, s, 1)
            product(y, x, -1)
            state = r, x, s, y
        else:
            pair(r, s, 1)
            product(x, y, -2)
            state = -r, -s, -y, x
    assert state == (-1, 2, 3, 4)
    assert not any(phase.values())
    for v, coefficient in [(2, -1), (3, -1), (4, 1)]:
        pair(1, v, coefficient)
    assert not any(gammas.values())
    print('EXACT Euler word (DP)^3: coupling reflection, all phases cancel.', flush=True)


def finite_reindexing(orders):
    cases, failures = 0, 0
    for n in orders:
        delta = Fraction(-2, 3)
        w = [Fraction(-1)]*n
        for a in range(1, (n+1)//2):
            w[a] = Fraction(a+1)+Fraction(1, a+2)
            w[-a] = delta/w[a]
        core = [[delta-2 if a == h == 0 else Fraction(-1)
                 if a == 0 or h == 0 or a == h else w[a]*w[(h-a) % n]/w[h]
                 for h in range(n)] for a in range(n)]

        def pair(p, q, s, reverse=False):
            values = [Fraction(0)]*n
            for a in range(n):
                values[(-a if reverse else a) % n] += core[a][p % n]*core[(a+s) % n][q % n]
            return values

        for g in range(1, n):
            for h in range(1, n):
                if (g+h) % n == 0:
                    continue
                for ell in range(n):
                    lhs = [sum(core[m][(g+h) % n]*core[g][(m+k) % n]
                               *core[h][(m+ell) % n] for m in range(n))
                           -(delta-1)*core[(g+ell) % n][k]*core[(h+k) % n][ell]
                           for k in range(n)]
                    column = [core[a][-g % n] for a in range(n)]
                    left = pair(g+h, -h, ell-h, reverse=True)
                    right = pair(-g-ell, ell, g+h+ell)
                    rhs = [Fraction(0)]*n
                    for a in range(n):
                        for b in range(n):
                            rhs[(a+b+g) % n] += column[a]*left[b]
                        rhs[(a+g+ell) % n] -= (delta-1)*right[a]
                    assert lhs == rhs
                    failures += any(lhs)
                    cases += 1
    assert failures  # This is an identity away from the solution scheme.
    print(f'EXACT partial Fourier reindexing: {cases} off-solution cases; '
          f'{failures} have nonzero cubic residuals.', flush=True)


def gamma_residue(c, j):
    """Residue of gamma at -j*B, from its B-shift and origin residue."""
    result = mp.sqrt(c.Q)/(2*mp.pi)
    for t in range(1, j+1):
        result /= 2*mp.sin(-mp.pi*t*c.B/c.A)
    return result


def four_gamma(c, p, q, s, z):
    j1 = (c.gamma(-z)*c.gamma(z-p)*c.gamma(c.B-z-s)
          *c.gamma(c.A+z+s-q))
    j2 = (c.gamma(c.A-z)*c.gamma(c.B+z-p)*c.gamma(-z-s)
          *c.gamma(z+s-q))
    return j1, j2


def local_checks(n):
    c = FourierCandidate(n)
    errors = dict(signed_column=mp.mpf(0), two_ratio_shift=mp.mpf(0),
                  extra_residues=mp.mpf(0), diagonal_residue=mp.mpf(0))
    for q in range(1-n, 0):
        for a in range(n):
            raw = ((-1)**(q*(a+1))*c.F(a)/c.F(a-q)
                   /(mp.sqrt(c.d)*c.F(q)))
            errors['signed_column'] = max(errors['signed_column'], abs(raw-c.core[a][q % n]))
    for p, q, s, k in [(1, -1, 1, 0), (2, -1, 1, 1), (1, 1, -1, 2)]:
        omega = c.omega(p+q, k)
        z = mp.mpc('0.37', '0.21')
        def kernel(z):
            return (mp.pi*mp.exp(-1j*omega*z)/mp.sin(mp.pi*z)
                    *c.F(z)*c.F(z+s)/(c.F(z-p)*c.F(z+s-q)))
        j1, j2 = four_gamma(c, p, q, s, z)
        rhs = -4*mp.pi*mp.exp(-1j*omega*z)*(
            (-1)**q*mp.sin(mp.pi*p/c.A)*j1
            +(-1)**s*mp.sin(mp.pi*q/c.A)*j2)
        errors['two_ratio_shift'] = max(errors['two_ratio_shift'],
                                       abs((kernel(z+n)-kernel(z))/rhs-1))
    for g in range(1, n-1):
        h = n-1-g
        ell = max(1, h//2)
        p, q, s = g+h, -h, ell-h
        omega = c.omega(p+q, 1)
        acoef, bcoef = (-1)**q*mp.sin(mp.pi*p/c.A), (-1)**s*mp.sin(mp.pi*q/c.A)
        for j in range(1, int(mp.floor(p/c.B))+1):
            z = p-j*c.B
            exp = mp.exp(-1j*omega*z)
            r1 = (exp*gamma_residue(c, j)*c.gamma(-z)
                  *c.gamma(c.B-z-s)*c.gamma(c.A+z+s-q))
            r2 = (exp*gamma_residue(c, j-1)*c.gamma(c.A-z)
                  *c.gamma(-z-s)*c.gamma(z+s-q))
            direct = (mp.pi*exp/mp.sin(mp.pi*z)*c.F(z)
                      *c.F(z+s)/c.F(z+s-q)*gamma_residue(c, j-1))
            errors['extra_residues'] = max(errors['extra_residues'],
                                          abs((4*mp.pi*(acoef*r1+bcoef*r2))/direct-1))
        r0 = (mp.sqrt(c.Q)/(2*mp.pi)*mp.exp(-1j*omega*p)*c.gamma(-p)
              *c.gamma(c.B-p-s)*c.gamma(c.A+p+s-q))
        c0 = (-1)**(p+q+q*s)/(c.d*c.F(p)*c.F(q))
        expected = c.B*c.core[(p+s) % n][q % n]*mp.exp(-2j*mp.pi*p/n)
        errors['diagonal_residue'] = max(errors['diagonal_residue'],
                                         abs(c0*4*mp.pi*acoef*r0-expected))
    assert max(errors.values()) < mp.power(10, -mp.mp.dps+10), errors
    print(f'NUMERICAL n={n}: '+', '.join(f'{k}={mp.nstr(v, 7)}' for k, v in errors.items()), flush=True)
    c.F.cache_clear()
    c.gamma.cache_clear()


def quadrature_checks(counts):
    c = FourierCandidate(3)
    r, s, x, eta = map(mp.mpf, ['0.31', '0.27', '0.19', '0.17'])
    y = 1j*eta
    G = lambda v: c.gamma(c.Q/2+r+v)*c.gamma(c.Q/2+r-v)
    factor = G(s)*G(x)/G(y)
    # An ordered-column case: g=h=ell=1, p=2, q=-1, s=0, k=0.
    p, q, offset = 2, -1, 0
    acoef, bcoef = -mp.sin(2*mp.pi/c.A), -mp.sin(mp.pi/c.A)
    c0 = -1/(c.d*c.F(p)*c.F(q))
    L = int(mp.floor(p/c.B))
    sigma = -min(mp.mpf('0.2'), ((L+1)*c.B-p)/2)
    residue_sum = mp.mpf(0)
    for j in range(L+1):
        z = p-j*c.B
        residue_sum += acoef*gamma_residue(c, j)*c.gamma(-z)*c.gamma(c.B-z)*c.gamma(c.A+z+1)
        if j:
            residue_sum += bcoef*gamma_residue(c, j-1)*c.gamma(c.A-z)*c.gamma(-z)*c.gamma(z+1)
    target = sum(c.core[a][p]*c.core[a][-1] for a in range(c.n))
    for count in counts:
        nodes, weights = mp.gauss_quadrature(count, 'legendre')
        samples = [(6*(node+1), weight*12/mp.sqrt(c.Q)) for node, weight in zip(nodes, weights)]
        def K(rr):
            U, V = c.Q/4+(rr+s)/2, c.Q/4+(rr-s)/2
            return mp.fsum(weight*(mp.exp(2j*mp.pi*y*(1j*t)/c.Q)
                       *c.gamma(U+1j*t)*c.gamma(U-1j*t)
                       *c.gamma(V+x+1j*t)*c.gamma(V-x-1j*t)).real
                       for t, weight in samples)
        euler_error = abs(K(r)-factor*K(-r))
        integral = mp.mpf(0)
        for t, weight in samples:
            j1, j2 = four_gamma(c, p, q, offset, sigma+1j*t)
            integral += weight*(acoef*j1+bcoef*j2).real
        integral += 2*mp.pi/mp.sqrt(c.Q)*residue_sum
        predicted = -2*mp.sqrt(c.Q)*c0*integral
        product_error = abs(predicted-target)
        print(f'NUMERICAL quadrature nodes={count}, cutoff=12: Euler_error={mp.nstr(euler_error, 8)}, '
              f'corrected_product_Fourier_error={mp.nstr(product_error, 8)}', flush=True)
    assert euler_error < mp.mpf('1e-10') and product_error < mp.mpf('1e-10')
    c.F.cache_clear()
    c.gamma.cache_clear()


def right_product_quadrature(counts):
    """The shifted sampling interval and its coincident-diagonal patch."""
    c = FourierCandidate(3)
    p, q, offset = -2, 1, 3
    acoef, bcoef = mp.sin(2*mp.pi/c.A), -mp.sin(mp.pi/c.A)
    c0 = 1/(c.d*c.F(p)*c.F(q))
    sigma = -offset-(c.B-1)/2
    z = mp.mpf(-2)
    r1 = gamma_residue(c, 0)*c.gamma(-z)*c.gamma(c.B-z-offset)*c.gamma(c.A+z+offset-q)
    r2 = gamma_residue(c, 0)*c.gamma(c.A-z)*c.gamma(c.B+z-p)*c.gamma(-z-offset)
    residue_sum = acoef*r1+bcoef*r2
    patch = 1/c.d**2-1  # raw coincident diagonals minus actual (-1)*(-1)
    patch_error = abs(4*mp.pi*c0*residue_sum-patch)
    assert patch_error < mp.power(10, -mp.mp.dps+8)
    print(f'NUMERICAL shifted-interval collision residue error={mp.nstr(patch_error, 8)}', flush=True)
    target = mp.fsum(c.core[a][p % c.n]*c.core[(a+offset) % c.n][q] for a in range(c.n))
    for count in counts:
        nodes, weights = mp.gauss_quadrature(count, 'legendre')
        integral = mp.mpf(0)
        for node, weight in zip(nodes, weights):
            j1, j2 = four_gamma(c, p, q, offset, sigma+6j*(node+1))
            integral += weight*12/mp.sqrt(c.Q)*(acoef*j1+bcoef*j2).real
        integral += 2*mp.pi/mp.sqrt(c.Q)*residue_sum
        error = abs(-2*mp.sqrt(c.Q)*c0*integral-target)
        print(f'NUMERICAL shifted-interval nodes={count}, cutoff=12: corrected_product_Fourier_error={mp.nstr(error, 8)}', flush=True)
    assert error < mp.mpf('1e-9')
    c.F.cache_clear()
    c.gamma.cache_clear()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 5, 7])
    parser.add_argument('--digits', type=int, default=28)
    parser.add_argument('--quadrature', type=int, nargs='+')
    parser.add_argument('--right-quadrature', type=int, nargs='+')
    args = parser.parse_args()
    if any(n < 3 or n % 2 == 0 for n in args.orders):
        raise ValueError('Require odd orders at least 3')
    mp.mp.dps = args.digits
    start = time.monotonic()
    euler_word()
    finite_reindexing(args.orders)
    for n in args.orders:
        local_checks(n)
    if args.quadrature:
        quadrature_checks(args.quadrature)
    if args.right_quadrature:
        right_product_quadrature(args.right_quadrature)
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: requested Section 110 reduction checks pass. The uniform infinitude proof is in Section 111.')


if __name__ == '__main__':
    main()
