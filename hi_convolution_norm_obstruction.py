"""Bounded exact norm-obstruction census for the convolution lift.

Exhaust every inverse-normalized Frobenius phase tuple at orders
3, 5, 7, and 9. Compare full residue Q with preservation of the
origin and inverse norms by the unique quartic lift modulo 2^bits.
The optional residue-quartic filter exhausts orders through 17 and
lifts only its survivors; it still tests every survivor against all Q.
The finite counts do not prove a uniform completion implication.
"""

import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import resource
import time

from hi_char2_general_search import seed_orbits
from hi_convolution_hensel import UnramifiedRing, lift_convolution


def all_phases(n, ring, delta):
    orbits = seed_orbits(n)
    choices = []
    for orbit, paired, size in orbits:
        length = len(orbit)
        factors, remaining, prime = [], size, 2
        while prime*prime <= remaining:
            if remaining % prime == 0:
                factors.append(prime)
                while remaining % prime == 0:
                    remaining //= prime
            prime += 1
        if remaining > 1:
            factors.append(remaining)
        for candidate in range(2, 1 << ring.degree):
            generator = ring.ff_pow(candidate, ((1 << ring.degree)-1)//size)
            if all(ring.ff_pow(generator, size//p) != 1 for p in factors):
                break
        else:
            raise AssertionError('A generator of the finite cyclic subgroup must exist')
        assert ring.ff_pow(generator, size) == 1
        seeds, value = [], delta ^ 1
        for _ in range(size):
            seeds.append(value)
            value = ring.ff_mul(value, generator)
        assert len(set(seeds)) == size and value == seeds[0]
        assert all(ring.ff_pow(x, 4**length) == x and
                   (paired or ring.ff_mul(x, ring.ff_pow(x, 4**(length//2))) == delta)
                   for x in seeds)
        assert len(seeds) == size
        choices.append(seeds)
    for values in product(*choices):
        phases = [1]*n
        for value, (orbit, paired, _) in zip(values, orbits):
            for a in orbit:
                phases[a] = value
                if paired:
                    phases[-a % n] = ring.ff_mul(delta, ring.ff_inv(value))
                value = ring.ff_pow(value, 4)
        assert all(ring.ff_mul(phases[a], phases[-a]) == delta and
                   ring.ff_pow(phases[a], 4) == phases[2*a % n]
                   for a in range(1, n))
        yield phases


def residue_q(n, ring, delta, phases):
    mul = ring.ff_mul
    t_inverse = ring.ff_inv(delta ^ 1)
    inverse = [ring.ff_inv(a) for a in phases]
    A = [[mul(t_inverse,
              delta if a == h == 0 else
              1 if a == 0 or h == 0 or a == h else
              mul(mul(phases[a], phases[(h-a) % n]), inverse[h]))
          for h in range(n)] for a in range(n)]
    failures = []
    for g in range(n):
        for h in range(n):
            residual = int(g == 0) ^ (ring.ff_inv(delta) if h == 0 else 0)
            for a in range(n):
                residual ^= mul(A[(g+a) % n][h], A[h][a])
            if residual:
                failures.append((g, h, residual))
    return not failures, failures[:1]


def first_obstructions(n, ring, delta, phases):
    """One entry per doubling orbit modulo negation suffices."""
    mul = ring.ff_mul
    result = []
    for orbit, _, _ in seed_orbits(n):
        r = orbit[0]
        h = 2*r % n
        pair_sum = {}
        for target in (h, -h % n):
            value = 0
            for a in range(n):
                b = (target-a) % n
                if a < b:
                    value ^= mul(phases[a], phases[b])
            pair_sum[target] = value
        mixed = mul(mul(phases[r], phases[r]), pair_sum[-h % n])
        mixed ^= mul(mul(phases[-r], phases[-r]), pair_sum[h])
        result.append((delta if ((n-1)//2) % 2 else 0) ^ (delta ^ 1) ^ mul(delta ^ 1, mixed))
    return result


def run(n, bits, first_only=False):
    suffix = 'char2_0' if n in (3, 9) else 'char2_general_0'
    path = Path('hi_finite_field_certificates') / f'hi_finite_field_{n}_{suffix}.json'
    data = json.loads(path.read_text())
    ring = UnramifiedRing(data[2], bits)
    delta_residue = sum(c << i for i, c in enumerate(data[3]))
    counts = Counter()
    witnesses = {}
    total = 0
    accepted = []
    for phases in all_phases(n, ring, delta_residue):
        if first_only:
            total += 1
            if any(first_obstructions(n, ring, delta_residue, phases)):
                continue
            is_q, first_q = residue_q(n, ring, delta_residue, phases)
            delta, lifted, _ = lift_convolution(ring, n, delta_residue, phases)
            origin = ring.valuation(ring.add(lifted[0], ring.one))
            norm = min(ring.valuation(ring.sub(ring.mul(lifted[a], lifted[-a]), delta))
                       for a in range(1, n))
            assert min(origin, norm) >= 2 and origin >= min(bits, norm+1)
            accepted.append((is_q, origin, norm))
            if not is_q:
                print(f'NONQ_FIRST_OBSTRUCTION_WITNESS n={n}; phases={phases}; '
                      f'first_Q={first_q}; origin={origin}; norm={norm}', flush=True)
            continue
        is_q, first_q = residue_q(n, ring, delta_residue, phases)
        delta, lifted, _ = lift_convolution(ring, n, delta_residue, phases)
        origin = ring.valuation(ring.add(lifted[0], ring.one))
        norm = min(ring.valuation(ring.sub(ring.mul(lifted[a], lifted[-a]), delta))
                   for a in range(1, n))
        # Uniform origin estimate and the explicit first norm obstruction.
        assert origin >= min(bits, norm+1)
        pair_sum = [0]*n
        for a in range(n):
            for b in range(a+1, n):
                pair_sum[(a+b) % n] ^= ring.ff_mul(phases[a], phases[b])
        t = delta_residue ^ 1
        for r in range(1, n):
            h = 2*r % n
            defect = ring.sub(ring.mul(lifted[h], lifted[-h]), delta)
            actual = sum(((value >> 1) & 1) << i for i, value in enumerate(defect))
            mixed = ring.ff_mul(ring.ff_pow(phases[r], 2), pair_sum[-h])
            mixed ^= ring.ff_mul(ring.ff_pow(phases[-r], 2), pair_sum[h])
            expected = (delta_residue if ((n-1)//2) % 2 else 0) ^ t ^ ring.ff_mul(t, mixed)
            assert actual == expected, ('first norm obstruction', n, phases, r)
        counts[is_q, origin, norm] += 1
        witnesses.setdefault((is_q, origin, norm), (phases, first_q))
        total += 1
    if first_only:
        print(f'COMPLETE FIRST-OBSTRUCTION n={n}; tuples={total}; accepted={len(accepted)}; '
              f'Q_among_accepted={sum(q for q, _, _ in accepted)}; bits={bits}', flush=True)
        for (is_q, origin, norm), count in sorted(Counter(accepted).items()):
            print(f'  residue_Q={is_q}; origin_valuation={origin}; '
                  f'norm_valuation={norm}; count={count}', flush=True)
        return
    print(f'COMPLETE n={n}; residue_field_degree={ring.degree}; '
          f'tuples={total}; bits={bits}; allQ={sum(v for (q, _, _), v in counts.items() if q)}', flush=True)
    for (is_q, origin, norm), count in sorted(counts.items()):
        print(f'  residue_Q={is_q}; origin_valuation={origin}; '
              f'norm_valuation={norm}; count={count}', flush=True)
    for precision in range(2, bits+1):
        accepted = sum(v for (_, origin, norm), v in counts.items()
                       if min(origin, norm) >= precision)
        false = sum(v for (q, origin, norm), v in counts.items()
                    if not q and min(origin, norm) >= precision)
        print(f'  normalized_mod_2^{precision}: accepted={accepted}; nonQ={false}', flush=True)
    for key, (phases, first_q) in witnesses.items():
        if not key[0] and min(key[1:]) >= 2:
            print(f'  NONQ_NORM_WITNESS {key}: phases={phases}; first_Q={first_q}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 5, 7, 9])
    parser.add_argument('--bits', type=int, default=8)
    parser.add_argument('--first-obstruction-only', action='store_true',
                        help='Filter by the explicit residue quartic before computing the lift or Q')
    args = parser.parse_args()
    allowed = (3, 5, 7, 9, 11, 13, 15, 17) if args.first_obstruction_only else (3, 5, 7, 9)
    if not 2 <= args.bits <= 24 or any(n not in allowed for n in args.orders):
        raise ValueError('The full census supports 3..9; the residue filter supports 3..17; use 2..24 bits')
    start = time.monotonic()
    for n in args.orders:
        run(n, args.bits, args.first_obstruction_only)
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: finite norm-obstruction census; no uniform Q or C completion claimed.')


if __name__ == '__main__':
    main()
