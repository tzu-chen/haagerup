"""Test compact semilinear Cayley formulas against a complete finite chart.

The candidate is V(x)=gamma+L0(x)+L1(h(x^2+x)), where gamma is in F4
and Li(x^2)=Li(x)^4. Testing every semilinear map avoids a preferred
normal-basis choice. A fit is only an interpolation fact, not a family.
"""

import argparse
from collections import Counter
from functools import reduce
import json
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('data', type=Path)
    parser.add_argument('results', type=Path)
    args = parser.parse_args()
    data = json.loads(args.data.read_text())
    q = data['n']-1
    r = q.bit_length()-1
    modulus = data['modulus']
    degree = modulus.bit_length()-1
    size = 1 << degree

    def mul(a, b):
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & size:
                a ^= modulus
        return result

    def power(a, exponent):
        result = 1
        while exponent:
            if exponent & 1:
                result = mul(result, a)
            a = mul(a, a)
            exponent >>= 1
        return result

    def binary_sums(basis):
        values = [0]
        for b in basis:
            values += [x ^ b for x in values]
        return values

    smallgen = power(data['generator'], (size-1)//(q-1))
    halfgen = power(data['generator'], (size-1)//(q*q-1))
    domain = binary_sums([power(smallgen, j) for j in range(r)])
    assert len(set(domain)) == q
    for theta in domain:
        normal = [power(theta, 1 << j) for j in range(r)]
        values = binary_sums(normal)
        if len(set(values)) == q:
            break
    else:
        raise ArithmeticError('Normal basis not found')
    coordinates = {x: mask for mask, x in enumerate(values)}
    maps = []
    for j in range(2*r):
        seed = power(halfgen, j)
        images = binary_sums([power(seed, 4**i) for i in range(r)])
        maps.append({x: images[coordinates[x]] for x in domain})

    def pack(row):
        return sum(x << (degree*j) for j, x in enumerate(row))

    targets = []
    degree_histogram = Counter()
    for line in args.results.read_text().splitlines():
        if not line.startswith('FULL_Q '):
            continue
        point = json.loads(line[7:])
        assert 'boundary' not in point
        row = data['particular'][:]
        for j, b in enumerate(data['basis']):
            if point['mask'] >> j & 1:
                row = [x ^ y for x, y in zip(row, b)]
        targets.append((point['mask'], pack(row)))
        anf = row[:]
        for j in range(r):
            for mask in range(q):
                if mask >> j & 1:
                    anf[mask] ^= anf[mask ^ (1 << j)]
        degree_histogram[max(mask.bit_count() for mask, c in enumerate(anf) if c)] += 1
    print(f'FINITE CHART n={q+1} full-Q points={len(targets)} '
          f'algebraic degree histogram={dict(degree_histogram)}', flush=True)
    base = [[1]*q, [data['delta']]*q]+[[f[x] for x in domain] for f in maps]
    tracezero = [mul(x, x) ^ x for x in domain]
    features = [('reciprocal', [power(y ^ 1, size-2) for y in tracezero])]
    features += [(f'power_{j}', [power(y, j) for y in tracezero]) for j in range(1, q)]
    for name, feature in features:
        rows = base+[[f[y] for y in feature] for f in maps]
        pivots = {}
        for index, row in enumerate(rows):
            value, witness = pack(row), 1 << index
            while value:
                leading = value.bit_length()-1
                if leading in pivots:
                    b, c = pivots[leading]
                    value ^= b
                    witness ^= c
                else:
                    pivots[leading] = (value, witness)
                    break
        fits = []
        for mask, value in targets:
            witness = 0
            while value:
                leading = value.bit_length()-1
                if leading not in pivots:
                    break
                b, c = pivots[leading]
                value ^= b
                witness ^= c
            if not value:
                assert pack([reduce(int.__xor__,
                    (row[j] for i, row in enumerate(rows) if witness >> i & 1), 0)
                    for j in range(q)]) == dict(targets)[mask]
                fits.append((mask, witness))
        print(f'FEATURE {name} dimension={len(pivots)} fits={fits}', flush=True)
    print('COMPLETE SEMILINEAR FUNCTION-FIT CHECK; no uniform existence assertion.')


if __name__ == '__main__':
    main()
