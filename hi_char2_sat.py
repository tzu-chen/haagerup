"""Exact SAT search for Frobenius-covariant characteristic-two HI phases.

This encodes inverse norms, selected Q equations, and the necessary full
top field degree at n=3^k. Remaining quadratics are added as needed.
A model is not a categorical certificate until the independent complete
cubic verifier has passed. Timeouts never mean unsatisfiability.
Section 71 proves that every full characteristic-two phase solution has
a unique normalization in this gauge; the gauge loses no full solutions.

Requires PARI/GP and pycryptosat. The latter is currently installed for
Python 3.9 in /tmp/hi_boolean_solver39, outside the workspace:
  PYTHONPATH=/tmp/hi_boolean_solver39 /usr/bin/python3.9 hi_char2_sat.py --order 9
"""

import argparse
from collections import Counter
from functools import reduce
import json
from operator import xor
from pathlib import Path
import time
import tempfile

from pycryptosat import Solver
from hi_char2_frobenius import field_parameters
from hi_char2_quadratic_orbits import representative, representatives
from hi_finite_field_certificate import verify


class Circuit:
    def __init__(self, threads=1):
        self.solver = Solver(threads=threads)
        self.count = 1
        self.solver.add_clause([1])
        self.xors, self.ands = {}, {}

    def variable(self):
        self.count += 1
        return self.count

    def xsum(self, values):
        parity, terms = False, set()
        for value in values:
            if value < 0:
                parity = not parity
                value = -value
            if value == 1:
                parity = not parity
            elif value in terms:
                terms.remove(value)
            else:
                terms.add(value)
        if not terms:
            return 1 if parity else -1
        if len(terms) == 1:
            result = next(iter(terms))
        else:
            key = frozenset(terms)
            result = self.xors.get(key)
            if result is None:
                result = self.variable()
                self.solver.add_xor_clause(list(terms) + [result], False)
                self.xors[key] = result
        return -result if parity else result

    def product(self, a, b):
        if a == -1 or b == -1 or a == -b:
            return -1
        if a == 1 or a == b:
            return b
        if b == 1:
            return a
        key = tuple(sorted((a, b)))
        result = self.ands.get(key)
        if result is None:
            result = self.variable()
            self.solver.add_clause([-result, a])
            self.solver.add_clause([-result, b])
            self.solver.add_clause([result, -a, -b])
            self.ands[key] = result
        return result


class Field:
    def __init__(self, degree, modulus, circuit):
        self.degree, self.modulus, self.circuit = degree, modulus, circuit
        self.zero, self.one = self.constant(0), self.constant(1)
        self.products, self.squares, self.linear_cache = {}, {}, {}
        self.frobenius_matrices = [[1 << j for j in range(degree)]]
        self.reductions = [self.power(2, i) for i in range(2*degree-1)]

    def multiply(self, a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a >> self.degree:
                a ^= self.modulus
        return result

    def power(self, a, exponent):
        result = 1
        while exponent:
            if exponent & 1:
                result = self.multiply(result, a)
            a = self.multiply(a, a)
            exponent >>= 1
        return result

    def constant(self, value):
        return tuple(1 if value >> i & 1 else -1 for i in range(self.degree))

    def add(self, *values):
        return tuple(self.circuit.xsum(row) for row in zip(*values))

    def linear(self, value, columns):
        return tuple(self.circuit.xsum(value[j] for j, column in enumerate(columns)
                                       if column >> i & 1)
                     for i in range(self.degree))

    def frobenius(self, value, exponent=1):
        key = value, exponent % self.degree
        if key not in self.linear_cache:
            while len(self.frobenius_matrices) <= key[1]:
                self.frobenius_matrices.append([self.multiply(c, c)
                                                for c in self.frobenius_matrices[-1]])
            columns = self.frobenius_matrices[key[1]]
            self.linear_cache[key] = self.linear(value, columns)
        return self.linear_cache[key]

    def polynomial_product(self, a, b):
        length = len(a)
        if length <= 4:
            return tuple(self.circuit.xsum(self.circuit.product(a[i], b[k-i])
                                           for i in range(length) if 0 <= k-i < length)
                         for k in range(2*length-1))
        half = length//2
        lo = self.polynomial_product(a[:half], b[:half])
        hi = self.polynomial_product(a[half:], b[half:])
        middle = self.polynomial_product(
            tuple(self.circuit.xsum(pair) for pair in zip(a[:half], a[half:])),
            tuple(self.circuit.xsum(pair) for pair in zip(b[:half], b[half:])))
        middle = tuple(self.circuit.xsum(items) for items in zip(middle, lo, hi))
        terms = [[] for _ in range(2*length-1)]
        for offset, values in [(0, lo), (half, middle), (2*half, hi)]:
            for i, value in enumerate(values):
                terms[offset+i].append(value)
        return tuple(self.circuit.xsum(values) for values in terms)

    def product(self, a, b):
        if a == self.zero or b == self.zero:
            return self.zero
        if a == self.one:
            return b
        if b == self.one:
            return a
        if a == b:
            return self.frobenius(a)
        key = tuple(sorted((a, b)))
        if key not in self.products:
            size = 1 << (self.degree-1).bit_length()
            padding = (-1,)*(size-self.degree)
            raw = self.polynomial_product(a+padding, b+padding)[:2*self.degree-1]
            self.products[key] = self.linear(raw, self.reductions)
        return self.products[key]

    def require(self, value, target=0):
        for i, literal in enumerate(value):
            self.circuit.solver.add_clause([literal if target >> i & 1 else -literal])

    def evaluate(self, value, model):
        return sum((bool(model[abs(literal)]) ^ (literal < 0)) << i
                   for i, literal in enumerate(value))


def binary_rank(columns):
    pivots = {}
    for value in columns:
        while value:
            pivot = value.bit_length()-1
            if pivot not in pivots:
                pivots[pivot] = value
                break
            value ^= pivots[pivot]
    return len(pivots)


def normal_basis(field):
    for first in range(2, 10000):
        columns, value = [], first
        for _ in range(field.degree):
            columns.append(value)
            value = field.multiply(value, value)
        if binary_rank(columns) == field.degree:
            assert value == first
            return columns
    raise ArithmeticError('normal basis search exhausted')


class Search:
    def __init__(self, n, threads=1):
        assert n >= 3 and n == 3**round(__import__('math').log(n, 3))
        self.n = n
        degree, (modulus, self.omega, _, _) = field_parameters(n)
        self.circuit = Circuit(threads)
        self.field = field = Field(degree, modulus, self.circuit)
        self.normal = normal_basis(field)
        self.phases = [field.one]*n
        self.seed_variables, self.seed_positions = [], []
        scale = 1
        while scale < n:
            local_degree = degree//scale
            variables = tuple(self.circuit.variable() for _ in range(local_degree))
            self.seed_variables.extend(variables)
            self.seed_positions.append((scale, variables))
            normal_value = variables*(degree//local_degree)
            value = field.linear(normal_value, self.normal)
            first, a = value, scale
            for _ in range(2*n//(3*scale)):
                self.phases[a] = value
                a = 2*a % n
                # A normal-coordinate rotation implements squaring twice.
                normal_value = normal_value[-2:]+normal_value[:-2]
                value = field.linear(normal_value, self.normal)
            assert value == first and a == scale
            field.require(field.product(first, self.phases[-scale]), self.omega)
            scale *= 3
        self.encoded = set()
        self.phase_products = {}
        # The top norm excludes all odd proper degrees. The remaining
        # proper degrees lie in the largest proper even-degree subfield.
        exponent = 2 if n == 3 else degree//3
        difference = field.add(self.phases[1], field.frobenius(self.phases[1], exponent))
        self.circuit.solver.add_clause(list(difference))

    def phase_product(self, indices):
        """Use inverse norms, squaring, and doubling before bit encoding."""
        counts = Counter(i % self.n for i in indices)
        counts.pop(0, None)
        omega_power = 0
        for a in range(1, (self.n+1)//2):
            pairs = min(counts[a], counts[-a % self.n])
            counts[a] -= pairs
            counts[-a % self.n] -= pairs
            omega_power += pairs
        indices = tuple(sorted(a for a, count in counts.items() for _ in range(count)))
        coefficient = self.field.constant(self.field.power(self.omega, omega_power % 3))
        if not indices:
            return coefficient
        orbit, current = [], indices
        while current not in orbit:
            orbit.append(current)
            current = tuple(sorted(2*a % self.n for a in current))
        canonical = min(orbit)
        shift = orbit.index(canonical)
        if canonical not in self.phase_products:
            if len(canonical) == 1:
                result = self.phases[canonical[0]]
            elif all(count % 2 == 0 for count in Counter(canonical).values()):
                half = [a for a, count in Counter(canonical).items() for _ in range(count//2)]
                result = self.field.frobenius(self.phase_product(half))
            else:
                middle = len(canonical)//2
                result = self.field.product(self.phase_product(canonical[:middle]),
                                            self.phase_product(canonical[middle:]))
            self.phase_products[canonical] = result
        result = self.field.frobenius(self.phase_products[canonical], -2*shift)
        return self.field.product(coefficient, result)

    def quadratic_value(self, g, h):
        """Pair m with h-g-m, whose summand is its relative conjugate.

        The sole fixed summand is omega for h=+/-g and omega^2
        otherwise. All other summands form relative-trace pairs.
        The simplification assumes the inverse norms encoded at startup.
        """
        assert g % self.n and h % self.n
        representatives = [m for m in range(self.n) if m < (h-g-m) % self.n]
        products = [self.phase_product((m, h-m, -m-g, m+g-h))
                    for m in representatives]
        half_sum = self.field.add(*products)
        fixed = self.omega if (h-g) % self.n == 0 or (h+g) % self.n == 0 else self.omega ^ 1
        return self.field.add(half_sum, self.field.frobenius(half_sum, self.field.degree//2),
                              self.field.constant(fixed))

    def add_quadratic(self, g, h):
        g, h = representative(self.n, g, h)
        if (g, h) in self.encoded:
            return
        self.encoded.add((g, h))
        self.field.require(self.quadratic_value(g, h))
        print(f'encoded F({g},{h}): variables={self.circuit.count}, '
              f'AND gates={len(self.circuit.ands)}, XOR gates={len(self.circuit.xors)}', flush=True)

    def numeric_quadratic(self, phases, g, h):
        mul, n = self.field.multiply, self.n
        return reduce(xor, (mul(mul(phases[m], phases[(h-m) % n]),
                                mul(phases[(-m-g) % n], phases[(m+g-h) % n]))
                            for m in range(n)), 0)

    def inspect(self, model):
        phases = [self.field.evaluate(value, model) for value in self.phases]
        assert phases[0] == 1
        assert all(self.field.multiply(phases[a], phases[-a]) == self.omega
                   and self.field.power(phases[a], 4) == phases[2*a % self.n]
                   for a in range(1, self.n))
        assert all(self.numeric_quadratic(phases, g, h) == 0 for g, h in self.encoded)
        for h in range(1, self.n):
            for g in range(1, self.n):
                if self.numeric_quadratic(phases, g, h):
                    return phases, (g, h)
        return phases, None

    def export(self, phases, path):
        field, degree = self.field, self.field.degree
        row = [1, 1]+[field.multiply(field.multiply(phases[1], phases[a-1]),
                                     field.power(phases[a], (1 << degree)-2))
                       for a in range(2, self.n)]
        coefficients = lambda value, length: [value >> i & 1 for i in range(length)]
        data = [self.n, 2, coefficients(field.modulus, degree+1),
                coefficients(self.omega, degree), [coefficients(value, degree) for value in row]]
        path.write_text(json.dumps(data) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=9, choices=[3, 9, 27, 81])
    parser.add_argument('--seconds', type=float, default=300)
    parser.add_argument('--threads', type=int, default=1)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--skip-cubic', action='store_true', help='save full-Q data only, explicitly unverified for C')
    parser.add_argument('--all-quadratics', action='store_true',
                        help='encode every quadratic orbit before solving')
    args = parser.parse_args()
    started = time.monotonic()
    search = Search(args.order, args.threads)
    for g, h in representatives(args.order) if args.all_quadratics else [(1, 1), (2, 1)]:
        search.add_quadratic(g, h)
    while time.monotonic()-started < args.seconds:
        remaining = args.seconds-(time.monotonic()-started)
        sat, model = search.circuit.solver.solve(time_limit=min(30, remaining))
        print(f'SAT status={sat}; elapsed={time.monotonic()-started:.1f}s', flush=True)
        if sat is None:
            continue
        if not sat:
            print('UNSAT for the encoded equations and full top-degree constraint; no general nonexistence claim.')
            return
        phases, failure = search.inspect(model)
        if failure:
            search.add_quadratic(*failure)
            continue
        output = args.output or Path(f'/tmp/hi_sat_{args.order}_fullq.json')
        search.export(phases, output)
        print(f'Every quadratic passed independently; full-Q data saved at {output}.', flush=True)
        if args.skip_cubic:
            print('CUBICS NOT CHECKED: this output is not an HI existence certificate.')
        else:
            with tempfile.TemporaryDirectory(prefix="hi_sat_verify_") as temp:
                verify(output, Path(temp))
            print('INDEPENDENT COMPLETE CUBIC VERIFICATION PASSED. This proves one finite order only.')
        return
    print('TIME LIMIT: no SAT/UNSAT conclusion was obtained.')


if __name__ == '__main__':
    main()
