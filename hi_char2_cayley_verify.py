"""Convert new Cayley-search points to the independent GP certificate format.

Only one representative per scalar-reindexing orbit is sent to the complete
quadratic/cubic verifier. A search's full-Q label is never accepted as C.
"""

import argparse
import json
from math import gcd
from pathlib import Path
import tempfile

from hi_finite_field_certificate import verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('data', type=Path)
    parser.add_argument('search', type=Path)
    parser.add_argument('--limit', type=int, default=1)
    parser.add_argument('--skip', type=int, default=0,
                        help='Skip this many distinct reindexing orbits already verified.')
    parser.add_argument('--output', type=Path, default=Path('hi_finite_field_certificates'))
    args = parser.parse_args()
    data = json.loads(args.data.read_text())
    n, modulus = data['n'], data['modulus']
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

    def power(a, b):
        result = 1
        while b:
            if b & 1:
                result = mul(result, a)
            a = mul(a, a)
            b >>= 1
        return result

    coefficients = lambda a: [(a >> j) & 1 for j in range(degree)]
    units = [a for a in range(1, n) if gcd(a, n) == 1]
    seen = set()
    checked = 0
    args.output.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='hi_cayley_verify_') as temporary:
        for line in args.search.read_text().splitlines():
            if not line.startswith('FULL_Q '):
                continue
            point = json.loads(line[7:])
            W = point['W']
            assert point['n'] == n and len(W) == n and W[0] == 1
            orbit = min(tuple(W[(u*a) % n] for a in range(n)) for u in units)
            if orbit in seen:
                continue
            seen.add(orbit)
            if len(seen) <= args.skip:
                continue
            row = [1, 1]+[mul(mul(W[1], W[a-1]), power(W[a], size-2)) for a in range(2, n)]
            certificate = [n, 2, coefficients(modulus)+[1], coefficients(data['delta']),
                           [coefficients(x) for x in row]]
            chart = f'_boundary{point["boundary"]}' if 'boundary' in point else ''
            path = args.output/f'hi_finite_field_{n}_char2_cayley{chart}_{point["mask"]}.json'
            path.write_text(json.dumps(certificate)+'\n')
            print(f'Checking scalar-reindexing orbit {len(seen)}: {path}', flush=True)
            verify(path, Path(temporary))
            checked += 1
            if checked >= args.limit:
                break
    if not checked:
        raise ValueError('No full-Q point was available to verify')
    print(f'COMPLETE INDEPENDENT VERIFICATION: {checked} scalar-reindexing orbit(s), '
          f'{args.skip} earlier orbit(s) skipped.')


if __name__ == '__main__':
    main()
