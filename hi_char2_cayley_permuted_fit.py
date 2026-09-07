"""Exact semilinear fits after all binary Frobenius-commuting input permutations.

Tests V(x)=gamma+L0(x)+L1(h(M(x*x+x))), with Li(x*x)=Li(x)^4.
M ranges over distinct invertible restrictions to the absolute-trace-zero
subspace of binary linearized polynomials. Finite h are every positive
power and 1/(z+1); the boundary chart uses 1/z away from z=0.
These are interpolation tests on saved, completely classified finite orders,
not a proof that any formula constructs categories at other orders.
"""

import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path


class Field:
    def __init__(self, modulus):
        self.modulus = modulus
        self.degree = modulus.bit_length() - 1
        self.size = 1 << self.degree

    def mul(self, a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & self.size:
                a ^= self.modulus
        return result

    def power(self, a, exponent):
        result = 1
        while exponent:
            if exponent & 1:
                result = self.mul(result, a)
            a = self.mul(a, a)
            exponent >>= 1
        return result


def binary_sums(basis):
    values = [0]
    for b in basis:
        values += [x ^ b for x in values]
    return values


def xor_sum(values):
    result = 0
    for value in values:
        result ^= value
    return result


def pack(row, degree):
    return sum(x << (degree * j) for j, x in enumerate(row))


def reduce_with_witness(value, pivots):
    witness = 0
    while value:
        leading = value.bit_length() - 1
        if leading not in pivots:
            break
        b, c = pivots[leading]
        value ^= b
        witness ^= c
    return value, witness


def span(rows, degree):
    pivots = {}
    for index, row in enumerate(rows):
        value, witness = reduce_with_witness(pack(row, degree), pivots)
        if value:
            pivots[value.bit_length() - 1] = value, witness ^ (1 << index)
    return pivots


def prepare(data, paths):
    n = data['n']
    q = n - 1
    r = q.bit_length() - 1
    assert q == 1 << r and r % 2
    field = Field(data['modulus'])
    power = field.power
    smallgen = power(data['generator'], (field.size - 1) // (q - 1))
    halfgen = power(data['generator'], (field.size - 1) // (q * q - 1))
    domain = binary_sums([power(smallgen, j) for j in range(r)])
    assert len(set(domain)) == q and all(power(x, q) == x for x in domain)
    for theta in domain:
        normal = [power(theta, 1 << j) for j in range(r)]
        values = binary_sums(normal)
        if len(set(values)) == q:
            break
    else:
        raise ArithmeticError('No normal basis')
    coordinates = {x: mask for mask, x in enumerate(values)}
    maps = []
    for j in range(2 * r):
        seed = power(halfgen, j)
        images = binary_sums([power(seed, 4**i) for i in range(r)])
        mapping = {x: images[coordinates[x]] for x in domain}
        assert all(mapping[power(x, 2)] == power(mapping[x], 4) for x in domain)
        maps.append(mapping)
    inverse_table = {w: v for v, w in data['table']}
    infinity_phase = power(data['delta'], 2)
    assert infinity_phase not in inverse_table and len(inverse_table) == q * q
    points = []
    for path in paths:
        lines = path.read_text().splitlines()
        assert lines[-1].startswith('COMPLETE'), f'Incomplete source {path}'
        for line in lines:
            if not line.startswith('FULL_Q '):
                continue
            point = json.loads(line[7:])
            row = [None] * q
            for a, index in enumerate(data['indices'], 1):
                w = point['W'][a]
                row[index] = None if w == infinity_phase else inverse_table[w]
            if 'boundary' not in point:
                reconstructed = data['particular'][:]
                for j, b in enumerate(data['basis']):
                    if point['mask'] >> j & 1:
                        reconstructed = [x ^ y for x, y in zip(reconstructed, b)]
                assert row == reconstructed
            lookup = dict(zip(domain, row))
            for x, v in lookup.items():
                assert lookup[x ^ 1] == (None if v is None else v ^ 1)
                assert lookup[power(x, 2)] == (None if v is None else power(v, 4))
            point['V'] = row
            points.append(point)
    assert len({tuple(p['W']) for p in points}) == len(points)
    tracezero = [power(x, 2) ^ x for x in domain]
    tracezero_set = set(tracezero)
    assert len(tracezero_set) == q // 2 and 1 not in tracezero_set
    permutations = {}
    for mask in range(1, q):
        row = tuple(xor_sum(power(y, 1 << i) for i in range(r) if mask >> i & 1)
                    for y in tracezero)
        if set(row) == tracezero_set:
            permutations.setdefault(row, mask)
    return field, domain, maps, points, permutations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('data', type=Path)
    parser.add_argument('results', type=Path, nargs='+')
    parser.add_argument('--json', type=Path)
    parser.add_argument('--terms', type=int, choices=[1, 2], default=1,
                        help='Two terms test pairs of distinct finite power classes and the reciprocal.')
    parser.add_argument('--summary-only', action='store_true')
    args = parser.parse_args()
    data = json.loads(args.data.read_text())
    field, domain, maps, points, permutations = prepare(data, args.results)
    q = len(domain)
    base = [[1] * q, [data['delta']] * q] + [[f[x] for x in domain] for f in maps]
    all_fits = []
    dimensions = Counter()
    tested = Counter()
    spaces = set()
    feature_spaces = 0
    print(f'SOURCE n={q+1} points={len(points)} '
          f'finite={sum(None not in p["V"] for p in points)} '
          f'input_permutations={len(permutations)}', flush=True)
    for row, mask in permutations.items():
        features = [('reciprocal_plus_one', [field.power(y ^ 1, field.size - 2) for y in row])]
        features += [(f'power_{j}', [field.power(y, j) for y in row]) for j in range(1, q)]
        features += [('reciprocal_boundary',
                      [None if y == 0 else field.power(y, field.size - 2) for y in row])]
        if args.terms == 1:
            candidates = [(name, [feature]) for name, feature in features]
        else:
            # Powers in the same doubling orbit give the same output-map space;
            # the orbit of 1 is already contained in the linear base.
            seen = set()
            representatives = []
            for j in range(1, q):
                if j in seen:
                    continue
                k = j
                while k not in seen:
                    seen.add(k)
                    k = (2*k - 1) % (q - 1) + 1
                if j != 1:
                    representatives.append(j)
            selected = [features[0]] + [features[j] for j in representatives]
            candidates = [(a[0] + '+' + b[0], [a[1], b[1]])
                          for a, b in combinations(selected, 2)]
        for name, feature_list in candidates:
            feature_spaces += 1
            support = tuple(j for j in range(q) if all(feature[j] is not None
                                                      for feature in feature_list))
            rows = [[b[j] for j in support] for b in base]
            rows += [[f[feature[j]] for j in support] for feature in feature_list for f in maps]
            pivots = span(rows, field.degree)
            dimensions[(name.split('_')[0], len(pivots))] += 1
            # Canonical reduced row space identifies redundant features exactly.
            reduced = {}
            for lead in sorted(pivots):
                value = pivots[lead][0]
                for low in sorted(reduced, reverse=True):
                    if value >> low & 1:
                        value ^= reduced[low]
                reduced[lead] = value
            spaces.add((support, tuple(reduced.values())))
            fits = []
            for point in points:
                if tuple(j for j, v in enumerate(point['V']) if v is not None) != support:
                    continue
                tested['boundary' if len(support) < q else 'finite'] += 1
                target = pack([point['V'][j] for j in support], field.degree)
                residual, witness = reduce_with_witness(target, pivots)
                if residual:
                    continue
                assert target == xor_sum(pack(b, field.degree) for i, b in enumerate(rows)
                                         if witness >> i & 1)
                fit = dict(point_mask=point['mask'], boundary=point.get('boundary', 0),
                           input_mask=mask, feature=name, witness=witness,
                           dimension=len(pivots))
                fits.append(fit)
                all_fits.append(fit)
            if fits and not args.summary_only:
                print('FIT ' + json.dumps(dict(input_mask=mask, feature=name,
                                              dimension=len(pivots), points=fits)), flush=True)
    summary = dict(n=q+1, input_permutations=len(permutations),
                   terms=args.terms, feature_spaces=feature_spaces, distinct_spaces=len(spaces),
                   membership_tests=dict(tested), fits=len(all_fits),
                   fitted_points=len({(f['boundary'], f['point_mask']) for f in all_fits}),
                   dimensions={str(k): v for k, v in dimensions.items()})
    print('COMPLETE PERMUTED SEMILINEAR FIT ' + json.dumps(summary), flush=True)
    print('No uniform existence assertion.')
    if args.json:
        args.json.write_text(json.dumps(dict(summary=summary, fits=all_fits), indent=2) + '\n')


if __name__ == '__main__':
    main()
