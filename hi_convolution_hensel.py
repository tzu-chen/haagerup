"""Exact finite-precision checks of the quartic convolution lift.

Work in (Z/2^bits)[z]/f(z), where f modulo 2 is a saved irreducible
polynomial. This is an unramified ring. Lift the convolution equations
by their strict contraction, and construct arithmetic Frobenius by
Hensel lifting z^4 to a root of f. No floating-point arithmetic is used.

Full Q and C are checked after lifting the known order-3 and order-9
certificates. A non-Q Frobenius/norm tuple is a negative control:
the convolution lift alone must not be reported as a category.
"""

import argparse
import json
from pathlib import Path
import resource
import time


class UnramifiedRing:
    def __init__(self, polynomial, bits):
        assert polynomial[-1] == 1 and all(c in (0, 1) for c in polynomial)
        self.f = polynomial
        self.degree = len(polynomial)-1
        self.bits = bits
        self.mask = (1 << bits)-1
        self.modulus = sum(c << i for i, c in enumerate(polynomial))
        self.support = [i for i, c in enumerate(polynomial[:-1]) if c]
        self.zero = (0,)*self.degree
        self.one = self.scalar(1)
        # Rabin irreducibility test, entirely in binary polynomial arithmetic.
        divisors, remaining, prime = [], self.degree, 2
        while prime*prime <= remaining:
            if remaining % prime == 0:
                divisors.append(prime)
                while remaining % prime == 0:
                    remaining //= prime
            prime += 1
        if remaining > 1:
            divisors.append(remaining)
        assert self.ff_pow(2, 1 << self.degree) == 2
        for prime in divisors:
            a, b = self.modulus, self.ff_pow(2, 1 << (self.degree//prime)) ^ 2
            while b:
                remainder = a
                while remainder and remainder.bit_length() >= b.bit_length():
                    remainder ^= b << (remainder.bit_length()-b.bit_length())
                a, b = b, remainder
            assert a == 1, 'Residue polynomial must be irreducible'

    def scalar(self, value):
        return (value & self.mask,)+(0,)*(self.degree-1)

    def lift(self, value):
        return tuple((value >> i) & 1 for i in range(self.degree))

    def residue(self, value):
        return sum((c & 1) << i for i, c in enumerate(value))

    def ff_mul(self, a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a >> self.degree:
                a ^= self.modulus
        return result

    def ff_pow(self, value, exponent):
        result = 1
        while exponent:
            if exponent & 1:
                result = self.ff_mul(result, value)
            value = self.ff_mul(value, value)
            exponent >>= 1
        return result

    def ff_inv(self, value):
        assert value
        return self.ff_pow(value, (1 << self.degree)-2)

    def add(self, a, b):
        return tuple((x+y) & self.mask for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple((x-y) & self.mask for x, y in zip(a, b))

    def scale(self, a, scalar):
        return tuple((scalar*x) & self.mask for x in a)

    def mul(self, a, b):
        if a == self.zero or b == self.zero:
            return self.zero
        if a == self.one:
            return b
        if b == self.one:
            return a
        d = self.degree
        product = [0]*(2*d-1)
        for i, x in enumerate(a):
            if x:
                for j, y in enumerate(b):
                    product[i+j] += x*y
        for i in range(2*d-2, d-1, -1):
            value = product[i]
            if value:
                for j in self.support:
                    product[i-d+j] -= value
        return tuple(c & self.mask for c in product[:d])

    def inv(self, value):
        inverse = self.lift(self.ff_inv(self.residue(value)))
        precision = 1
        while precision < self.bits:
            inverse = self.mul(inverse, self.sub(self.scalar(2), self.mul(value, inverse)))
            precision *= 2
        assert self.mul(value, inverse) == self.one
        return inverse

    def valuation(self, value):
        return min((self.bits if not c else (c & -c).bit_length()-1) for c in value)

    def polynomial(self, coefficients, argument):
        result = self.zero
        for coefficient in reversed(coefficients):
            result = self.add(self.mul(result, argument), self.scalar(coefficient))
        return result

    def frobenius_parameter(self):
        parameter = self.lift(self.ff_pow(2, 4))
        derivative = [i*c for i, c in enumerate(self.f)][1:]
        for _ in range(self.bits.bit_length()+1):
            error = self.polynomial(self.f, parameter)
            if error == self.zero:
                break
            slope = self.polynomial(derivative, parameter)
            parameter = self.sub(parameter, self.mul(error, self.inv(slope)))
        assert self.polynomial(self.f, parameter) == self.zero
        assert self.residue(parameter) == self.ff_pow(2, 4)
        return parameter


def saved_phases(data, ring):
    n = data[0]
    encode = lambda row: sum(c << i for i, c in enumerate(row))
    delta = encode(data[3])
    row = [encode(v) for v in data[4]]
    phases = [1]*n
    phases[1] = ring.ff_pow(ring.ff_inv(row[2]), 1 << (ring.degree-1))
    for a in range(2, n):
        phases[a] = ring.ff_mul(ring.ff_mul(phases[1], phases[a-1]), ring.ff_inv(row[a]))
    assert all(ring.ff_mul(phases[a], phases[-a]) == delta for a in range(1, n))
    assert all(ring.ff_pow(phases[a], 4) == phases[2*a % n] for a in range(n))
    return delta, phases


def convolution(ring, phases):
    n = len(phases)
    result = [ring.zero]*n
    # Pair the unequal-index terms. The diagonal terms are separate.
    for a in range(n):
        result[2*a % n] = ring.add(result[2*a % n], ring.mul(phases[a], phases[a]))
        for b in range(a+1, n):
            k = (a+b) % n
            result[k] = ring.add(result[k], ring.scale(ring.mul(phases[a], phases[b]), 2))
    return result


def lift_convolution(ring, n, delta_residue, phase_residues):
    delta = ring.lift(delta_residue)
    for _ in range(ring.bits.bit_length()+1):
        error = ring.sub(ring.sub(ring.mul(delta, delta), ring.scale(delta, n)), ring.one)
        if error == ring.zero:
            break
        derivative = ring.sub(ring.scale(delta, 2), ring.scalar(n))
        delta = ring.sub(delta, ring.mul(error, ring.inv(derivative)))
    assert ring.sub(ring.sub(ring.mul(delta, delta), ring.scale(delta, n)), ring.one) == ring.zero
    coefficient = ring.scale(ring.inv(ring.mul(delta, ring.sub(delta, ring.one))), -1)
    phases = [ring.lift(a) for a in phase_residues]
    defects = []
    for step in range(ring.bits+2):
        conv = convolution(ring, phases)
        updated = [ring.zero]*n
        for r in range(n):
            updated[2*r % n] = ring.mul(coefficient, ring.mul(
                ring.mul(phases[r], phases[r]), conv[2*r % n]))
        valuation = min(ring.valuation(ring.sub(x, y)) for x, y in zip(updated, phases))
        defects.append(valuation)
        if updated == phases:
            break
        if len(defects) > 1:
            assert defects[-1] >= min(ring.bits, defects[-2]+1)
        phases = updated
    else:
        raise AssertionError('Contraction did not converge at its proved rate')
    assert [ring.residue(a) for a in phases] == phase_residues
    return delta, phases, defects


def check_relations(ring, n, delta, phases):
    norm = min(ring.valuation(ring.sub(ring.mul(phases[a], phases[-a]), delta))
               for a in range(1, n))
    origin = ring.valuation(ring.add(phases[0], ring.one))
    inverse = [ring.inv(a) for a in phases]
    normalization = ring.inv(ring.sub(delta, ring.one))
    A = [[ring.mul(normalization,
        ring.sub(delta, ring.scalar(2)) if a == h == 0 else
        ring.scalar(-1) if a == 0 or h == 0 or a == h else
        ring.mul(ring.mul(phases[a], phases[(h-a) % n]), inverse[h]))
        for h in range(n)] for a in range(n)]
    inverse_delta = ring.inv(delta)
    q = ring.bits
    for g in range(n):
        for h in range(n):
            value = ring.zero
            for a in range(n):
                value = ring.add(value, ring.mul(A[(g+a) % n][h], A[h][a]))
            if g == 0:
                value = ring.sub(value, ring.one)
            if h == 0:
                value = ring.add(value, inverse_delta)
            q = min(q, ring.valuation(value))
    c = ring.bits
    for g in range(n):
        for h in range(n):
            for k in range(n):
                for ell in range(n):
                    value = ring.zero
                    for a in range(n):
                        value = ring.add(value, ring.mul(A[a][(g+h) % n],
                            ring.mul(A[g][(a+k) % n], A[h][(a+ell) % n])))
                    value = ring.sub(value, ring.mul(A[(g+ell) % n][k], A[(h+k) % n][ell]))
                    if g == h == 0:
                        value = ring.add(value, inverse_delta)
                    c = min(c, ring.valuation(value))
    return origin, norm, q, c


def run(data, bits, label, control=False):
    n = data[0]
    ring = UnramifiedRing(data[2], bits)
    delta_residue, residues = saved_phases(data, ring)
    if control:
        residues = [1]+[ring.ff_mul(delta_residue, delta_residue)]*(n-1)
    delta, phases, defects = lift_convolution(ring, n, delta_residue, residues)
    frobenius = ring.frobenius_parameter()
    assert ring.polynomial(delta, frobenius) == delta
    assert all(ring.polynomial(phases[a], frobenius) == phases[2*a % n] for a in range(n))
    origin, norm, q, c = check_relations(ring, n, delta, phases)
    print(f'EXACT n={n} {label} absolute_residue_degree={ring.degree} modulus=2^{bits}', flush=True)
    print(f'  contraction_defect_valuations={defects}', flush=True)
    print('  arithmetic_Frobenius_4_equals_label_doubling: PASS', flush=True)
    print(f'  residual_valuations origin={origin} norm={norm} Q={q} all_C={c} '
          f'(value {bits} means zero modulo 2^{bits})', flush=True)
    if control:
        assert q == 0 and c == 0
        assert norm < bits or origin < bits
    else:
        assert min(origin, norm, q, c) == bits


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bits', type=int, default=24)
    args = parser.parse_args()
    start = time.monotonic()
    directory = Path(__file__).resolve().parent / 'hi_finite_field_certificates'
    first = None
    for n, branch in [(3, 0), (9, 0), (9, 1)]:
        data = json.loads((directory / f'hi_finite_field_{n}_char2_{branch}.json').read_text())
        if first is None:
            first = data
        run(data, args.bits, f'known_certificate_branch_{branch}')
    run(first, args.bits, 'constant_phase_negative_control', control=True)
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: exact finite-precision lift and Frobenius checks pass. '
          'The negative control excludes completion from the convolution alone; '
          'uniform cubic completion is not proved.')


if __name__ == '__main__':
    main()
