"""Check convergent Abel--Plana formulas for the canonical HI kernels.

The contour formula is unconditional. Evaluating it as the proposed zero
or nine-factor product remains an unproved uniform summation problem.
Numerical quadrature here is not an interval certificate.
"""

import argparse

import mpmath as mp

from hi_shintani_meromorphic import sine


class Kernel:
    def __init__(self, n, a, c):
        self.n, self.a, self.c = n, a, c
        assert len(a) == len(c) and len(a) in (2, 3)
        assert sum(a)+sum(c) == (len(a)-2)*n
        assert all(-(n-1) <= u <= 0 for u in a)
        assert all(0 <= v <= n-1 for v in c)
        assert all((u+v) % n for u in a for v in c)
        self.d = (n+mp.sqrt(n*n+4))/2
        self.A, self.B = self.d+1, 1+1/self.d
        self.q = mp.exp(2*mp.pi*1j/self.d)
        self.alpha = [mp.exp(2*mp.pi*1j*u/self.A) for u in a]
        self.beta = [mp.exp(2*mp.pi*1j*(v-n)/self.A) for v in c]

    def F(self, z):
        return sine(1+z/self.B, self.d)

    def psi(self, z):
        # Repeated parameters are frequent in the smallest cross-free cases.
        arguments = [z+u for u in self.a]+[v-z for v in self.c]
        values = {u: self.F(u) for u in set(arguments)}
        return mp.fprod(values[u] for u in arguments)

    def H(self, x):
        return (mp.fprod(1-u*x for u in self.alpha)
                / mp.fprod(1-x/v for v in self.beta))

    def shift_ratio(self, z):
        x = mp.exp(2*mp.pi*1j*z/self.A)
        y = mp.exp(-2*mp.pi*1j*z/self.B)
        return self.H(x)/self.H(y)

    def check_periods(self):
        error = mp.mpf(0)
        for z in [mp.mpc('0.37', '0.21'), mp.mpc('0.17', '-0.19')]:
            x = mp.exp(2*mp.pi*1j*z/self.A)
            y = mp.exp(-2*mp.pi*1j*z/self.B)
            value = self.psi(z)
            for step, ratio in [(self.B, self.q/self.H(self.q*x)),
                                (self.A, self.q/self.H(y)),
                                (self.n, self.shift_ratio(z))]:
                error = max(error, abs(self.psi(z+step)/(value*ratio)-1))
        return error

    def quadrature(self, count, cutoff):
        nodes, weights = mp.gauss_quadrature(count, 'legendre')
        horizontal = mp.mpf(0)
        vertical = mp.mpf(0)
        for node, weight in zip(nodes, weights):
            x = self.n*(node+1)/2
            horizontal += weight*self.psi(x).real
            t = cutoff*(node+1)/2
            z = 1j*t
            difference = self.psi(z)*(self.shift_ratio(z)-1)
            vertical += weight*2*difference.imag/mp.expm1(2*mp.pi*t)
        horizontal *= self.n/2
        vertical *= cutoff/2
        endpoint = (self.psi(0)-self.psi(self.n)).real/2
        return horizontal, endpoint, vertical


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--digits', type=int, default=30)
    parser.add_argument('--nodes', nargs='+', type=int, default=[32, 64])
    parser.add_argument('--cutoff', default='12')
    args = parser.parse_args()
    mp.mp.dps = args.digits
    cutoff = mp.mpf(args.cutoff)
    for a, c in [([0, -2], [1, 1]), ([0, 0, 0], [1, 1, 1])]:
        kernel = Kernel(3, a, c)
        error = kernel.check_periods()
        assert error < mp.power(10, -args.digits+8)
        print(f'NUMERICAL n=3 r={len(a)} A/B/n-shift relative error='
              f'{mp.nstr(error, 8)}', flush=True)
        finite = mp.fsum(kernel.psi(m).real for m in range(3))
        print(f'Finite sample sum: {mp.nstr(finite, 24)}', flush=True)
        for count in args.nodes:
            parts = kernel.quadrature(count, cutoff)
            result = mp.fsum(parts)
            error = abs(result-finite)
            print(f'NUMERICAL nodes={count} cutoff={cutoff} horizontal/endpoint/'
                  f'vertical={[mp.nstr(x, 18) for x in parts]} '
                  f'error={mp.nstr(error, 8)}', flush=True)
        assert error < mp.mpf('1e-8')
    print('ABEL--PLANA AND PERIOD CHECKS PASSED; uniform target evaluations remain unproved.')


if __name__ == '__main__':
    main()
