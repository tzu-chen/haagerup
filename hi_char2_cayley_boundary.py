"""Complete an affine Cayley search by enumerating the omitted infinity charts.

The domain splits into orbits under a -> -a and a -> 2a. Infinity must be
constant on each such orbit. Restricting a full affine chart to the remaining
orbits gives every finite function there; binary elimination removes the
directions supported on infinity. No extra degree assumption is made.
"""

import argparse
import json
from pathlib import Path
import subprocess

from hi_char2_general_search import quadratic_representatives


def independent(rows, degree):
    pivots = {}
    selected = []
    for row in rows:
        packed = sum(x << (degree*j) for j, x in enumerate(row))
        reduced = packed
        while reduced:
            leading = reduced.bit_length()-1
            if leading in pivots:
                reduced ^= pivots[leading]
            else:
                pivots[leading] = reduced
                selected.append(row)
                break
    return selected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('data', type=Path)
    parser.add_argument('--directory', type=Path, default=Path('/tmp/hi_cayley_boundary'))
    parser.add_argument('--search', type=Path)
    args = parser.parse_args()
    data = json.loads(args.data.read_text())
    n = data['n']
    r = (n-1).bit_length()-1
    assert n == (1 << r)+1 and r % 2 == 1
    assert data.get('maxdegree', 2) >= r-1, 'Requires the full finite chart.'
    degree = data['modulus'].bit_length()-1
    assert len(independent(data['basis'], degree)) == len(data['basis'])
    orbits = []
    todo = set(range(1, n))
    while todo:
        orbit = {min(todo)}
        while True:
            larger = orbit | {2*a % n for a in orbit} | {-a % n for a in orbit}
            if larger == orbit:
                break
            orbit = larger
        todo -= orbit
        orbits.append(sorted(orbit))
    print(f'DOMAIN ORBITS n={n}: {orbits}', flush=True)
    args.directory.mkdir(parents=True, exist_ok=True)
    pairs = quadratic_representatives(n)
    total = 0
    for pattern in range(1, 1 << len(orbits)):
        infinite = {a for j, orbit in enumerate(orbits) if pattern >> j & 1 for a in orbit}
        omitted = {data['indices'][a-1] for a in infinite}
        restrict = lambda row: [0 if j in omitted else x for j, x in enumerate(row)]
        origin = restrict(data['particular'])
        basis = independent([restrict(row) for row in data['basis']], degree)
        indices = [n-1 if a in infinite else data['indices'][a-1] for a in range(1, n)]
        dim = len(basis)
        # For this family each domain orbit contributes its cardinality in bits.
        # The assertion also certifies surjectivity of the restricted chart.
        assert dim == n-1-len(infinite)
        total += 1 << dim
        rows = [[n, data['modulus'], data['delta'], data['generator'], dim, len(pairs)],
                origin, indices, *basis, *data['table'], *[list(pair) for pair in pairs]]
        path = args.directory/f'hi_cayley_boundary_{n}_{pattern}.txt'
        path.write_text('\n'.join(' '.join(map(str, row)) for row in rows)+'\n')
        print(f'BOUNDARY pattern={pattern} infinity={sorted(infinite)} dimension={dim} '
              f'candidates={1 << dim}', flush=True)
        if args.search:
            process = subprocess.Popen([str(args.search.resolve()), str(path)],
                                       stdout=subprocess.PIPE, text=True)
            for line in process.stdout:
                if line.startswith('FULL_Q '):
                    point = json.loads(line[7:])
                    point['boundary'] = pattern
                    line = 'FULL_Q '+json.dumps(point)+'\n'
                print(line, end='', flush=True)
            if process.wait():
                raise RuntimeError(f'Search failed on boundary chart {pattern}')
    print(f'COMPLETE BOUNDARY n={n} charts={(1 << len(orbits))-1} candidates={total}', flush=True)


if __name__ == '__main__':
    main()
