"""Numerical checks for the meromorphic formulas in Sections 76--77.

The proofs use double-sine shifts and the convergent product identity.
These computations do not establish the finite additive HI identities.
"""

import argparse

import mpmath as mp

from hi_shintani_ghost import log_sinhc


def log_sine_strip(z, d):
    """log S(z;d,1) in 0<Re(z)<d+1, with the positive-real branch."""
    z = mp.mpc(z)
    if not d > 0 or not 0 < z.real < d+1:
        raise ValueError('Outside the positive-period convergence strip')
    a = d+1-2*z
    if not a:
        return mp.mpc(0)

    def integrand(t):
        if not t:
            return -a*(a*a-d*d-1)/(24*d)
        ratio_log = (log_sinhc(a*t/2)-log_sinhc(d*t/2)
                     - log_sinhc(t/2))
        return -a/d*mp.expm1(ratio_log)/(t*t)

    return mp.quad(integrand, [0, 1, mp.inf])


def sine(z, d):
    """Continue S(z;d,1) with integer shifts; callers avoid its poles."""
    z = mp.mpc(z)
    # Keep the integration point away from both strip boundaries.
    k = int(mp.floor(z.real-(d+1)/2))
    base = z-k
    value = mp.exp(log_sine_strip(base, d))
    if k >= 0:
        for j in range(k):
            value /= 2*mp.sin(mp.pi*(base+j)/d)
    else:
        for j in range(-k):
            value *= 2*mp.sin(mp.pi*(z+j)/d)
    return value


def interpolation(n, z):
    d = (n+mp.sqrt(n*n+4))/2
    return (-mp.exp(mp.pi*1j*z*(z+n)/2)/mp.sqrt(d)
            * sine(1+d*z/(d+1), d))


def lens_product_log(n, mu, m):
    """Independent n-factor expression, evaluated inside its strips."""
    d = (n+mp.sqrt(n*n+4))/2
    return mp.fsum(log_sine_strip((mu*d+j*d*d+(m-j) % n)/n, d*d)
                   for j in range(n))


def factored_product(n, mu, m):
    d = (n+mp.sqrt(n*n+4))/2
    return sine((d*mu+m)/n, d)*sine((d*(n-m)-mu)/n, d)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 7, 11])
    parser.add_argument('--digits', type=int, default=40)
    args = parser.parse_args()
    mp.mp.dps = args.digits+20
    tolerance = mp.power(10, -args.digits+8)
    for n in args.orders:
        if n < 3 or n % 2 == 0:
            raise ValueError('Require odd n>=3')
        d = (n+mp.sqrt(n*n+4))/2
        mu = (d+1/d)/2+mp.mpc(0, '0.13')
        factor_error = max(abs(mp.exp(lens_product_log(n, mu, m))
                               /factored_product(n, mu, m)-1)
                           for m in sorted({0, (n-1)//2, n-1}))
        print(f'NUMERICAL n={n}: off-diagonal two-factor relative error='
              f'{mp.nstr(factor_error, 6)}', flush=True)

        nu, lam = 1/(d+1), d/(d+1)
        shift_error = norm_error = mp.mpf(0)
        for z in [mp.mpc('0.37', '0.21'), mp.mpc('-1.23', '-0.17')]:
            f = interpolation(n, z)
            ratio = -mp.exp(mp.pi*1j*n*z)*mp.sin(mp.pi*nu*z)/mp.sin(mp.pi*lam*z)
            norm = mp.exp(mp.pi*1j*z*z)/d*mp.sin(mp.pi*lam*z)/mp.sin(mp.pi*nu*z)
            shift_error = max(shift_error, abs(interpolation(n, z+n)/(f*ratio)-1))
            norm_error = max(norm_error, abs(f*interpolation(n, -z)/norm-1))

        jump_error = mp.mpf(0)
        for a in [-n-1, -n, -1, 0, 1, n, n+1, 2*n]:
            error = (interpolation(n, a+n)-interpolation(n, a)
                     -(1+1/d)*int(a == 0))
            jump_error = max(jump_error, abs(error))

        # Symmetric evaluation cancels the first-order error in mu*Gamma.
        h = mp.power(10, -(args.digits//2+3))
        residue = (h/factored_product(n, h, 0)
                   - h/factored_product(n, -h, 0))/2
        residue_error = abs(residue-n/(2*mp.pi))
        assert max(factor_error, shift_error, norm_error,
                   jump_error, residue_error) < tolerance
        print(f'NUMERICAL n={n}: complex shift={mp.nstr(shift_error, 6)}; '
              f'complex norm={mp.nstr(norm_error, 6)}; '
              f'integer jump={mp.nstr(jump_error, 6)}; '
              f'origin residue={mp.nstr(residue_error, 6)}', flush=True)
    print('ALL REQUESTED MEROMORPHIC CHECKS PASSED; no additive HI proof is claimed.')


if __name__ == '__main__':
    main()
