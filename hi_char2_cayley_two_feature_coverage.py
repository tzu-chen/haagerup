"""Check whether the short two-feature fits at order 33 constrain anything.

Proves coverage of the entire 32-bit finite Cayley chart by verifying a
24-dimensional common fiber and all 256 relative-trace patterns. No
enumeration of the 2^32 points, and no inference of HI equations, is used.
"""

from itertools import combinations, product
import json
from pathlib import Path

from hi_char2_cayley_permuted_fit import pack, prepare, reduce_with_witness, span, xor_sum
from hi_char2_cayley_semilinear_rank import FrobeniusModule


def canonical(pivots):
    reduced = {}
    for lead in sorted(pivots):
        value = pivots[lead][0]
        for low in sorted(reduced, reverse=True):
            if value >> low & 1:
                value ^= reduced[low]
        reduced[lead] = value
    return tuple(reduced.values())


def main():
    data = json.loads(Path('hi_char2_cayley_degree4_33.json').read_text())
    field, domain, maps, points, permutations = prepare(data, [
        Path('hi_char2_cayley_degree4_33_results.txt'),
        Path('hi_char2_cayley_boundary33_results.txt')])
    module = FrobeniusModule(data, field, domain)
    q = len(domain)
    base = [[1]*q, [data['delta']]*q] + [[f[x] for x in domain] for f in maps]
    maximal = {}
    for inputs, mask in permutations.items():
        features = [('reciprocal', [field.power(y ^ 1, field.size-2) for y in inputs])]
        features += [(f'power_{j}', [field.power(y, j) for y in inputs])
                     for j in [3, 5, 7, 11, 15, 31]]
        for left, right in combinations(features, 2):
            rows = base + [[f[y] for y in feature] for _, feature in (left, right) for f in maps]
            pivots = span(rows, field.degree)
            if len(pivots) == 32:
                maximal.setdefault(canonical(pivots), (pivots, mask, left[0], right[0]))
    assert len(maximal) == 7
    print('LARGEST FEATURE SPACES count=7 linear_dimension=32', flush=True)

    remaining = set(module.tracezero) - {0}
    orbits = []
    while remaining:
        initial = min(remaining)
        orbit, x = [], initial
        while x not in orbit:
            orbit.append(x)
            x = field.power(x, 2)
        assert x == initial and len(orbit) == 5
        orbits.append(orbit)
        remaining -= set(orbit)
    assert len(orbits) == 3
    # Eight independent binary directions in ker Tr(K/F4).
    output_basis = []
    current = {}
    for value in module.output_coord:
        if reduce_with_witness(value, current)[0]:
            output_basis.append([value])
            current = span(output_basis, field.degree)
    assert len(output_basis) == 8
    fiber = []
    for orbit in orbits:
        for (value,) in output_basis:
            assignment = dict.fromkeys(domain, 0)
            for j, x in enumerate(orbit):
                assignment[x] = assignment[x ^ 1] = field.power(value, 4**j)
            row = [assignment[x] for x in domain]
            assert all(module.trace4(v) == 0 for v in row)
            fiber.append(row)
    assert len(span(fiber, field.degree)) == 24
    for pivots, *_ in maximal.values():
        assert all(not reduce_with_witness(pack(row, field.degree), pivots)[0] for row in fiber)
    print('COMMON FIBER dimension=24 contained_in_each_space=true', flush=True)

    origin = [module.trace2(x) for x in domain]
    constants = [0, 1, data['delta'], field.power(data['delta'], 2)]
    representatives = []
    trace_patterns = []
    cover_counts = []
    for values in product(constants, repeat=4):
        assignment = {0: values[0], 1: values[0] ^ 1}
        for orbit, c in zip(orbits, values[1:]):
            for x in orbit:
                assignment[x] = c
                assignment[x ^ 1] = c ^ 1
        row = [assignment[x] for x in domain]
        assert all(assignment[x ^ 1] == assignment[x] ^ 1 for x in domain)
        assert all(assignment[field.power(x, 2)] == field.power(assignment[x], 4) for x in domain)
        representatives.append(row)
        trace_patterns.append(values)
        covered = sum(not reduce_with_witness(pack(row, field.degree), pivots)[0]
                      for pivots, *_ in maximal.values())
        assert covered > 0
        cover_counts.append(covered)
    full_span = span(fiber + [[v ^ o for v, o in zip(row, origin)]
                             for row in representatives], field.degree)
    assert len(full_span) == len(data['basis']) == 32
    assert all(not reduce_with_witness(pack(row, field.degree), full_span)[0]
               for row in data['basis'])
    assert not reduce_with_witness(pack([v ^ o for v, o in zip(data['particular'], origin)],
                                       field.degree), full_span)[0]
    assert len(representatives) == 256
    normals = set()
    for pivots, mask, left, right in maximal.values():
        matches = [normal for normal in range(1, 8) if all(
            (not reduce_with_witness(pack(row, field.degree), pivots)[0]) ==
            (xor_sum(values[i+1] ^ values[0] for i in range(3) if normal >> i & 1) == 0)
            for row, values in zip(representatives, trace_patterns))]
        assert len(matches) == 1
        normals.add(matches[0])
        print(f'TRACE PLANE input_mask={mask} features={left},{right} binary_normal={matches[0]}')
    assert normals == set(range(1, 8))
    print('TRACE PATTERNS count=256 all_covered=true '
          f'cover_multiplicities={dict((c, cover_counts.count(c)) for c in sorted(set(cover_counts)))}')
    print('COMPLETE: all 4294967296 finite norm/Frobenius functions at order 33 '
          'fit this union of two-feature spaces. Only 80 satisfy full Q; '
          'these fits alone provide no HI construction.')


if __name__ == '__main__':
    main()
