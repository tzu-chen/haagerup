"""Summarize completed finite and boundary Cayley searches, without assuming C."""

import argparse
from collections import defaultdict
import json
from math import gcd
from pathlib import Path
import re


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('data', type=Path)
    parser.add_argument('finite', type=Path)
    parser.add_argument('boundary', type=Path)
    args = parser.parse_args()
    data = json.loads(args.data.read_text())
    n = data['n']
    points = []
    candidates = first = full = 0
    for path in [args.finite, args.boundary]:
        lines = path.read_text().splitlines()
        assert lines[-1].startswith('COMPLETE'), f'Incomplete search: {path}'
        for line in lines:
            if line.startswith('FULL_Q '):
                points.append(json.loads(line[7:]))
            elif line.startswith('COMPLETE n='):
                match = re.fullmatch(r'COMPLETE n=(\d+) candidates=(\d+) first_Q=(\d+) '
                                     r'full_Q=(\d+) seconds=\S+', line)
                assert match and int(match[1]) == n
                candidates += int(match[2])
                first += int(match[3])
                full += int(match[4])
    assert full == len(points)
    assert len({tuple(p['W']) for p in points}) == full
    units = [u for u in range(1, n) if gcd(u, n) == 1]
    groups = defaultdict(list)
    for point in points:
        W = point['W']
        assert len(W) == n and W[0] == 1
        orbit = {tuple(W[u*a % n] for a in range(n)) for u in units}
        groups[min(orbit)].append(point)
    for group in groups.values():
        point = group[0]
        W = point['W']
        orbit = {tuple(W[u*a % n] for a in range(n)) for u in units}
        assert orbit == {tuple(p['W']) for p in group}, 'Search is not closed under reindexing.'
        frobenius = set()
        current = tuple(W)
        while current not in frobenius:
            frobenius.add(current)
            current = tuple(current[2*a % n] for a in range(n))
        print(f'ORBIT n={n} mask={point["mask"]} boundary={point.get("boundary", 0)} '
              f'length={len(group)} F4_residue_degree={len(frobenius)}', flush=True)
    print(f'COMPLETE CLASSIFICATION n={n} norm_Frobenius_candidates={candidates} '
          f'first_Q={first} canonical_Q={full} U_orbits={len(groups)} '
          f'raw_phase_count_if_C_verified={n*full}')
    print('Cubic acceptance is supplied separately by the independent GP certificates.')


if __name__ == '__main__':
    main()
