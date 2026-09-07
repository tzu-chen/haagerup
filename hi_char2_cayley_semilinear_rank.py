"""Certify the obstruction to an arbitrary single Cayley nonlinear feature.

For r=3,5, Phi_r is irreducible over F2. The trace-zero Frobenius module
is a line over S=F_(2^(r-1)); its target is a plane over S. A single
feature requires at most two relative-trace values and an affine line
containing all normalized nontrivial values. These conditions are also
sufficient. Every accepted point is reconstructed explicitly below.
No HI equation is inferred from the interpolation criterion.
"""

import argparse
from collections import Counter
import json
from pathlib import Path

from hi_char2_cayley_permuted_fit import Field, prepare, xor_sum


class FrobeniusModule:
    def __init__(self, data, field, domain):
        self.field, self.domain = field, domain
        self.r = (len(domain)).bit_length() - 1
        assert self.r in (3, 5)
        self.scalars = Field((1 << self.r) - 1)
        s = self.scalars
        # Direct irreducibility/field check, rather than an unverified assumption.
        assert all(s.power(a, s.size - 1) == 1 for a in range(1, s.size))
        self.tracezero = [x for x in domain if self.trace2(x) == 0]
        theta = next(x for x in self.tracezero if x)
        self.input_of = {a: xor_sum(field.power(theta, 2**j)
                                   for j in range(self.r - 1) if a >> j & 1)
                         for a in range(s.size)}
        self.coord = {x: a for a, x in self.input_of.items()}
        assert set(self.coord) == set(self.tracezero)
        assert all(self.coord[field.power(x, 2)] == s.mul(2, self.coord[x])
                   for x in self.tracezero)
        halfgen = field.power(data['generator'], (field.size - 1) // (len(domain)**2 - 1))
        projected = [self.project(field.power(halfgen, j)) for j in range(2*self.r)]
        first = next(v for v in projected if v)
        first_line = {self.action(a, first) for a in range(s.size)}
        second = next(v for v in projected if v not in first_line)
        self.output_coord = {self.action(a, first) ^ self.action(b, second): (a, b)
                             for a in range(s.size) for b in range(s.size)}
        assert len(self.output_coord) == s.size**2
        assert all(v in self.output_coord for v in projected)
        assert all(self.trace4(v) == 0 for v in self.output_coord)
        # Independent verification of scalar multiplication on the two generators.
        for a in range(s.size):
            for b in range(s.size):
                for v in (first, second):
                    assert self.action(s.mul(a, b), v) == self.action(a, self.action(b, v))

    def trace2(self, x):
        return xor_sum(self.field.power(x, 2**j) for j in range(self.r))

    def trace4(self, v):
        return xor_sum(self.field.power(v, 4**j) for j in range(self.r))

    def project(self, v):
        return v ^ self.trace4(v)

    def action(self, a, v):
        return xor_sum(self.field.power(v, 4**j)
                       for j in range(self.r - 1) if a >> j & 1)

    def inspect(self, row, reconstruct=True):
        lookup = dict(zip(self.domain, row))
        poles = {x for x, v in lookup.items() if v is None}
        assert poles in (set(), {0, 1})
        traces = {x: self.trace4(lookup[x]) for x in self.tracezero
                  if lookup[x] is not None}
        normalized = {x: self.action(self.scalars.power(self.coord[x], self.scalars.size-2),
                                    self.project(lookup[x]))
                      for x in self.tracezero if x and lookup[x] is not None}
        assert all(normalized[self.field.power(x, 2)] == v for x, v in normalized.items())
        values = list(dict.fromkeys(normalized.values()))
        anchor = values[0]
        direction = next((v ^ anchor for v in values if v != anchor), 0)
        line = {self.action(a, direction): a for a in range(self.scalars.size)}
        on_line = all(v ^ anchor in line for v in values)
        # Cross-check by determinants in S^2, not the field-bit orbit test above.
        ac, bc = self.output_coord[anchor], self.output_coord[direction]
        determinant_zero = all(
            self.scalars.mul(bc[0], self.output_coord[v][1] ^ ac[1]) ==
            self.scalars.mul(bc[1], self.output_coord[v][0] ^ ac[0]) for v in values)
        assert determinant_zero == on_line
        result = dict(trace_values=sorted(set(traces.values())),
                      normalized_values=[list(self.output_coord[v]) for v in values],
                      affine_line=on_line)
        result['single_feature'] = len(result['trace_values']) <= 2 and on_line
        if not result['single_feature'] or not reconstruct:
            return result

        gamma = lookup[0] if not poles else result['trace_values'][0]
        constant = next((v ^ gamma for v in traces.values() if v != gamma), 1)
        assert self.field.power(gamma, 4) == gamma
        assert self.field.power(constant, 4) == constant and constant
        feature = {}
        for x in self.tracezero:
            y = self.field.power(x, 2) ^ x
            if lookup[x] is None:
                feature[y] = None
            elif x == 0:
                feature[y] = 0
            else:
                bit = int(traces[x] != gamma)
                assert traces[x] == gamma ^ (constant if bit else 0)
                scalar = line[normalized[x] ^ anchor] if direction else 0
                feature[y] = bit ^ self.input_of[self.scalars.mul(self.coord[x], scalar)]
        assert set(feature) == set(self.tracezero)
        assert all(feature[self.field.power(y, 2)] ==
                   (None if h is None else self.field.power(h, 2)) for y, h in feature.items())

        def linear0(x):
            bit = self.trace2(x)
            return bit ^ self.action(self.coord[x ^ bit], anchor)

        def linear1(x):
            bit = self.trace2(x)
            return (constant if bit else 0) ^ self.action(self.coord[x ^ bit], direction)

        for linear in (linear0, linear1):
            assert all(linear(self.field.power(x, 2)) == self.field.power(linear(x), 4)
                       for x in self.domain)
            assert all(linear(x ^ y) == linear(x) ^ linear(y)
                       for x in self.domain for y in self.domain)
        assert linear0(1) == 1
        for x, v in lookup.items():
            h = feature[self.field.power(x, 2) ^ x]
            reconstructed = None if h is None else gamma ^ linear0(x) ^ linear1(h)
            assert reconstructed == v
        result['reconstruction_verified'] = True
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[9, 33])
    parser.add_argument('--json', type=Path)
    args = parser.parse_args()
    reports = []
    for n in args.orders:
        r = (n - 1).bit_length() - 1
        data = json.loads(Path(f'hi_char2_cayley_degree{r-1}_{n}.json').read_text())
        field, domain, maps, points, permutations = prepare(data, [
            Path(f'hi_char2_cayley_degree{r-1}_{n}_results.txt'),
            Path(f'hi_char2_cayley_boundary{n}_results.txt')])
        module = FrobeniusModule(data, field, domain)
        histogram = Counter()
        certificates = []
        for point in points:
            result = module.inspect(point['V'])
            key = (bool(point.get('boundary')), len(result['trace_values']), result['affine_line'])
            histogram[key] += 1
            certificates.append(dict(mask=point['mask'], boundary=point.get('boundary', 0), **result))
        # Synthetic positive examples ensure the order-33 criterion can accept,
        # with reconstruction checked at every field input; no Q claim is made.
        for mapping in maps:
            row = [data['delta'] ^ module.trace2(x) ^
                   mapping[field.power(field.power(x, 2) ^ x, 3) ^ 1] for x in domain]
            assert module.inspect(row)['reconstruction_verified']
        report = dict(n=n, histogram={str(k): v for k, v in histogram.items()},
                      accepted=sum(c['single_feature'] for c in certificates),
                      points=len(points), certificates=certificates,
                      synthetic_reconstructions=len(maps))
        print('EXACT SINGLE-FEATURE RANK ' + json.dumps({k: v for k, v in report.items()
                                                      if k != 'certificates'}), flush=True)
        reports.append(report)
    if args.json:
        args.json.write_text(json.dumps(reports, indent=2) + '\n')
    print('COMPLETE: exact interpolation obstruction; infinitude is not established.')


if __name__ == '__main__':
    main()
