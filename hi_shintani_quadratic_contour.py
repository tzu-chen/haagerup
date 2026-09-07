"""A single convergent vertical contour for the finite quadratic sum.

Use the quadratic B-period primitive and a difference of cotangents. Its
residues include one extra pair of shifted samples, which is retained.
Checks include a perturbation away from real multiplication where the
finite sample sum is nonzero. Quadrature is numerical, not an interval
certificate or a uniform evaluation of the contour.
"""

import argparse

import mpmath as mp

from hi_shintani_meromorphic import sine


class QuadraticContour:
    def __init__(self, n, a, c, B=None):
        self.n, self.a, self.c = n, tuple(a), tuple(c)
        assert len(a) == len(c) == 2 and sum(a)+sum(c) == 0
        assert all(-(n-1) <= u <= 0 for u in a)
        assert all(0 <= u <= n-1 for u in c)
        assert all((u+v) % n for u in a for v in c)
        d = (n+mp.sqrt(n*n+4))/2
        self.B = 1+1/d if B is None else mp.mpf(B)
        assert 1 < self.B < mp.mpf('1.5')
        self.A = n+self.B
        self.d = self.A/self.B
        self.sigma = -mp.mpf('0.5')
        self.denominator = 4*mp.sin(mp.pi*(a[0]+c[0])/self.A)*mp.sin(mp.pi*(a[0]+c[1])/self.A)

    def F(self, z):
        return sine(1+z/self.B, self.d)

    def product(self, arguments):
        cached = {z: self.F(z) for z in set(arguments)}
        return mp.fprod(cached[z] for z in arguments)

    def psi(self, z):
        return self.product([z+a for a in self.a]+[c-z for c in self.c])

    def G(self, z):
        return self.product([z+a-self.B for a in self.a]+[c-z for c in self.c])/self.denominator

    def n_ratio(self, z):
        # Separate A/B sine shifts; valid also away from 1/A+1/B=1.
        return (mp.fprod(mp.sin(mp.pi*(z+a+self.n)/self.A)/mp.sin(mp.pi*(z+a)/self.B)
                         for a in self.a)
                *mp.fprod(mp.sin(mp.pi*(c-z-self.n)/self.B)/mp.sin(mp.pi*(c-z-self.n)/self.A)
                          for c in self.c))

    def integral(self, nodes_count, cutoff):
        nodes, weights = mp.gauss_quadrature(nodes_count, 'legendre')
        result = mp.mpf(0)
        for node, weight in zip(nodes, weights):
            t = cutoff*(node+1)/2
            z = self.sigma+1j*t
            # cot(u)-cot(v)=sin(v-u)/(sin(u)sin(v)) avoids cancellation at large t.
            cotangent_difference = -mp.sin(mp.pi*self.B)/(mp.sin(mp.pi*z)*mp.sin(mp.pi*(z-self.B)))
            difference = self.G(z)*(self.n_ratio(z)-1)
            result += weight*(cotangent_difference*difference).real
        return result*cutoff/2

    def check(self, nodes_counts, cutoff, label):
        z = mp.mpc('0.37', '0.21')
        shift_error = max(abs((self.G(z+self.B)-self.G(z))/self.psi(z)-1),
                          abs(self.G(z+self.n)/(self.G(z)*self.n_ratio(z))-1))
        assert shift_error < mp.power(10, -mp.mp.dps+8)
        finite = mp.fsum(self.psi(m).real for m in range(self.n))
        endpoint = (self.G(self.A-1)-self.G(self.B-1)).real
        # Check the residue indexing independently, retaining the extra pair.
        residues = (mp.fsum(self.G(m).real for m in range(self.n))
                    -mp.fsum(self.G(m+self.B).real for m in range(-1, self.n-1)))
        assert abs(residues-endpoint+finite) < mp.power(10, -mp.mp.dps+8)
        print(f'CASE {label} n={self.n} B={mp.nstr(self.B,18)} '
              f'shift_error={mp.nstr(shift_error,7)}', flush=True)
        print(f'  finite_sum={mp.nstr(finite,24)} endpoint_pair={mp.nstr(endpoint,24)}', flush=True)
        for count in nodes_counts:
            contour = self.integral(count, cutoff)
            error = abs(endpoint-contour-finite)
            print(f'  NUMERICAL nodes={count} cutoff={cutoff} contour={mp.nstr(contour,24)} '
                  f'formula_error={mp.nstr(error,8)}', flush=True)
        assert error < mp.mpf('1e-9')
        if label == 'off_RM':
            assert abs(finite) > mp.mpf('1e-4')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--digits', type=int, default=30)
    parser.add_argument('--nodes', type=int, nargs='+', default=[64, 128])
    parser.add_argument('--cutoff', default='24')
    args = parser.parse_args()
    mp.mp.dps = args.digits
    cutoff = mp.mpf(args.cutoff)
    for label, B in [('RM', None), ('off_RM', '1.25')]:
        QuadraticContour(3, [0, -2], [1, 1], B=B).check(args.nodes, cutoff, label)
    print('COMPLETE: the contour identity is checked; its uniform RM evaluation remains unproved.')


if __name__ == '__main__':
    main()
