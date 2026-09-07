"""Check the uniform Fourier evaluation and quadratic theorem in Section 93.

Double-sine samples and the gamma-product Fourier formula are evaluated
independently. These are numerical regression checks of an analytic proof,
not interval certificates. No algebraic HI seed is used.
"""

import argparse
from functools import lru_cache
import resource
import time

import mpmath as mp

from hi_shintani_meromorphic import sine


class FourierCandidate:
    def __init__(self, n):
        self.n = n
        self.d = (n + mp.sqrt(n*n + 4))/2
        self.A = self.d + 1
        self.B = 1 + 1/self.d
        self.Q = self.A*self.B
        self.delta = -1/self.d
        self.w = [-mp.mpf(1)] + [
            -(-1)**(a*(a+n)//2)*self.F(a)/mp.sqrt(self.d)
            for a in range(1, n)]
        self.core = [[
            self.delta-2 if a == h == 0 else
            -mp.mpf(1) if a == 0 or h == 0 or a == h else
            self.w[a]*self.w[(h-a) % n]/self.w[h]
            for h in range(n)] for a in range(n)]

    @lru_cache(None)
    def F(self, z):
        return sine(1+z/self.B, self.d)

    @lru_cache(None)
    def gamma(self, z):
        return 1/sine(z/self.B, self.d)

    def omega(self, h, k):
        # Exact integer reduction prevents an accidental 2*pi branch change.
        t = (2*k + self.n*(h-1) + self.n) % (2*self.n)-self.n
        return mp.pi*t/self.n

    def evaluated_fourier(self, h, k):
        omega = self.omega(h, k)
        x = (self.Q+h)/2
        y = self.Q*omega/(2*mp.pi)
        return (-self.B*mp.exp(-1j*h*omega/2)
                * self.gamma(x-y)*self.gamma(x+y))

    def direct_fourier(self, h, k):
        return mp.fsum(self.core[a][h]*mp.exp(-2j*mp.pi*k*a/self.n)
                       for a in range(self.n))

    def check(self):
        n, A, B, Q = self.n, self.A, self.B, self.Q
        errors = {}
        # Include off-real points in both half planes, away from divisors.
        errors['kernel_shift'] = mp.mpf(0)
        errors['sample_correction'] = mp.mpf(0)
        errors['residue_cancellation'] = mp.mpf(0)
        for h in range(1, n):
            for z in [mp.mpc('0.37', '0.21'), mp.mpc('-0.13', '-0.31')]:
                k = (h+1) % n
                omega = self.omega(h, k)
                K = lambda u: (mp.pi/mp.sin(mp.pi*u)*mp.exp(-1j*omega*u)
                               * self.F(u)/self.F(u-h))
                rhs = (-4*mp.pi*mp.sin(mp.pi*h/A)*mp.exp(-1j*omega*z)
                       * self.gamma(-z)*self.gamma(z-h))
                errors['kernel_shift'] = max(errors['kernel_shift'],
                    abs((K(z+n)-K(z))/rhs-1))
            for a in range(n):
                raw = ((-1)**(h*(a+1))*self.F(a)/self.F(a-h)
                       / (mp.sqrt(self.d)*self.F(h)))
                expected = self.core[a][h]+B*int(a == h)
                errors['sample_correction'] = max(errors['sample_correction'],
                                                   abs(raw-expected))
            # Direct residue ratio at p=h-l*B. The shared residue of 1/F
            # cancels, so this tests the cancellation without small epsilon.
            for ell in range(1, int(mp.floor(h/B))+1):
                p = h-ell*B
                ratio = (self.F(p)*mp.sin(mp.pi*(p-h)/A)
                         / (2*mp.sin(mp.pi*h/A)*self.gamma(-p)
                            *mp.sin(mp.pi*p)))
                errors['residue_cancellation'] = max(
                    errors['residue_cancellation'], abs(ratio-1))
        errors['fourier'] = mp.mpf(0)
        spectral = {}
        for h in range(1, n):
            for k in range(n):
                rhs = self.evaluated_fourier(h, k)
                spectral[h, k] = rhs
                errors['fourier'] = max(errors['fourier'],
                    abs(self.direct_fourier(h, k)-rhs))
        errors['spectral_inverse'] = max(
            abs(spectral[h, k]*spectral[n-h, (-k) % n]
                *mp.exp(2j*mp.pi*k*h/n)/B**2-1)
            for h in range(1, n) for k in range(n))
        errors['all_Q'] = max(abs(
            mp.fsum(self.core[(g+a) % n][h]*self.core[h][a]
                    for a in range(n))/B**2
            - int(g == 0)+int(h == 0)/self.delta)
            for g in range(n) for h in range(n))
        errors['convolution'] = max(abs(
            mp.fsum(self.w[a]*self.w[(2*r-a) % n] for a in range(n))
            + self.delta*(self.delta-1)*self.w[2*r % n]/self.w[r]**2)
            for r in range(n))
        errors['zero_mode'] = max(abs(
            self.direct_fourier(h, 0)+B/self.F((h*((n+1)//2)) % n)**2)
            for h in range(1, n))
        errors['scalar_H'] = abs(
            mp.fsum(self.w)**2
            + (self.delta-1)*mp.fsum(self.core[a][2*a % n] for a in range(n))
            - 2*(self.delta-1)**2)
        # Both the coordinate and Fourier signs of the selected chamber.
        assert all((-1)**(a+1)*self.core[a][1].real > 0 for a in range(2, n))
        center = (n+1)//2
        for k in range((n+1)//2):
            eigenvalue = (mp.exp(-2j*mp.pi*k*center/n)
                          *self.direct_fourier(1, -k)).real
            assert -(-1)**k*eigenvalue > 0
        tolerance = mp.power(10, -mp.mp.dps+12)
        assert max(errors.values()) < tolerance, errors
        for key, value in errors.items():
            print(f'  NUMERICAL {key}={mp.nstr(value, 8)}', flush=True)
        print('  prescribed coordinate and Fourier chamber: PASS', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 5, 7, 9, 11])
    parser.add_argument('--digits', type=int, default=40)
    args = parser.parse_args()
    mp.mp.dps = args.digits
    start = time.monotonic()
    for n in args.orders:
        if n < 3 or n % 2 == 0:
            raise ValueError('Require odd n >= 3')
        print(f'CASE n={n} digits={args.digits}', flush=True)
        candidate = FourierCandidate(n)
        candidate.check()
        # Method caches contain their instances; release them between orders.
        candidate.F.cache_clear()
        candidate.gamma.cache_clear()
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: all requested Fourier, residue, chamber and Q checks pass. '
          'The uniform proof is in Section 93; cubic identities and infinitude remain open.')


if __name__ == '__main__':
    main()
