"""Numerical audit of the merged noninteger poles in Section 110.4.

At n=5, g=1, h=l=2, the right product has a genuine double pole.
Its full residue is computed using gamma Laurent coefficients and
compared with the independently differentiated cosecant kernel.
"""

import resource
import time

import mpmath as mp

from hi_shintani_column_products import four_gamma, gamma_residue
from hi_shintani_fourier import FourierCandidate


def main():
    mp.mp.dps = 32
    start = time.monotonic()
    c = FourierCandidate(5)
    p, q, s = -3, 2, 5
    aa, bb = -mp.sin(3*mp.pi/c.A), -mp.sin(2*mp.pi/c.A)
    c0 = -1/(c.d*c.F(p)*c.F(q))
    logarithmic_constant = mp.diff(c.gamma, c.B)/c.gamma(c.B)

    def regular_to_residue(j):
        return logarithmic_constant-mp.fsum(
            mp.pi/c.A*mp.cot(-mp.pi*t*c.B/c.A) for t in range(1, j+1))

    residue_sum = mp.mpf(0)
    for j in [0, 1]:
        z = p-j*c.B
        r1 = (gamma_residue(c, j)*c.gamma(-z)
              *c.gamma(c.B-z-s)*c.gamma(c.A+z+s-q))
        if j == 0:
            r2 = gamma_residue(c, 0)*c.gamma(c.A-z)*c.gamma(c.B)*c.gamma(-z-s)
            patch_error = abs(4*mp.pi*c0*(aa*r1+bb*r2)-(1/c.d**2-1))
            assert patch_error < mp.mpf('1e-28')
            print('NUMERICAL coincident integer patch error', mp.nstr(patch_error, 10), flush=True)
        else:
            smooth = lambda z: c.gamma(c.A-z)*c.gamma(-z-s)
            r2 = gamma_residue(c, j-1)*gamma_residue(c, j)*(
                mp.diff(smooth, z)+(regular_to_residue(j-1)+regular_to_residue(j))*smooth(z))
            kernel_smooth = lambda z: mp.pi/mp.sin(mp.pi*z)*c.F(z)*c.F(z+s)
            direct_residue = gamma_residue(c, j-1)**2*(
                mp.diff(kernel_smooth, z)+2*regular_to_residue(j-1)*kernel_smooth(z))
            residue_error = abs(4*mp.pi*(aa*r1+bb*r2)/direct_residue-1)
            assert residue_error < mp.mpf('1e-28')
            print('NUMERICAL full double-pole residue relative error', mp.nstr(residue_error, 10), flush=True)
        residue_sum += aa*r1+bb*r2
    target = mp.fsum(c.core[a][p % 5]*c.core[(a+s) % 5][q] for a in range(5))
    sigma = -s-(c.B-1)
    for count in [40, 80]:
        nodes, weights = mp.gauss_quadrature(count, 'legendre')
        integral = mp.mpf(0)
        for node, weight in zip(nodes, weights):
            j1, j2 = four_gamma(c, p, q, s, sigma+6j*(node+1))
            integral += weight*12/mp.sqrt(c.Q)*(aa*j1+bb*j2).real
        integral += 2*mp.pi/mp.sqrt(c.Q)*residue_sum
        error = abs(-2*mp.sqrt(c.Q)*c0*integral-target)
        print(f'NUMERICAL nodes={count}, cutoff=12: product Fourier error={mp.nstr(error, 10)}', flush=True)
    assert error < mp.mpf('1e-9')
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: the full double residue and the coincident diagonal patch both pass.')


if __name__ == '__main__':
    main()
