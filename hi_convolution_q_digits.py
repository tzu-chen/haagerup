"""Exact checks of paired Q sums and the extra norm digit.

Verify the uniform identity for arbitrary normalized lifts, compare
its residue with the independent quartic norm obstruction on every
small Frobenius tuple, and inspect Q on known convolution branches.
These checks do not establish a uniform implication to cubics.
"""

from collections import Counter
import json
from pathlib import Path
import random
import resource
import time

from hi_convolution_hensel import UnramifiedRing, convolution, lift_convolution
from hi_convolution_norm_obstruction import all_phases, first_obstructions
from hi_char2_general_search import seed_orbits


def q_residuals(ring, delta, phases):
    n = len(phases)
    inverse = [ring.inv(x) for x in phases]
    coefficient = ring.inv(ring.sub(delta, ring.one))
    A = [[ring.mul(coefficient,
                   ring.sub(delta, ring.scalar(2)) if g == h == 0 else
                   ring.scalar(-1) if not g or not h or g == h else
                   ring.mul(ring.mul(phases[g], phases[(h-g) % n]), inverse[h]))
          for h in range(n)] for g in range(n)]
    result = [[ring.zero]*n for _ in range(n)]
    for g in range(n):
        for h in range(n):
            value = ring.zero
            for m in range(n):
                value = ring.add(value, ring.mul(A[(g+m) % n][h], A[h][m]))
            if g == 0:
                value = ring.sub(value, ring.one)
            if h == 0:
                value = ring.add(value, ring.inv(delta))
            result[g][h] = value
    return result


def residue_q(ring, delta, phases):
    n = len(phases)
    mul = ring.ff_mul
    inverse = [ring.ff_inv(x) for x in phases]
    A = [[delta ^ 1 if g == h == 0 else delta if not g or not h or g == h else
          mul(delta, mul(mul(phases[g], phases[(h-g) % n]), inverse[h]))
          for h in range(n)] for g in range(n)]
    result = [[0]*n for _ in range(n)]
    for g in range(n):
        for h in range(n):
            value = int(g == 0) ^ (delta ^ 1 if h == 0 else 0)
            for m in range(n):
                value ^= mul(A[(g+m) % n][h], A[h][m])
            result[g][h] = value
    return result


def step(ring, delta, phases):
    n = len(phases)
    conv = convolution(ring, phases)
    coefficient = ring.scale(ring.inv(ring.mul(delta, ring.sub(delta, ring.one))), -1)
    result = [ring.zero]*n
    for r in range(n):
        result[2*r % n] = ring.mul(coefficient, ring.mul(ring.mul(phases[r], phases[r]), conv[2*r % n]))
    return result


def small_census(n):
    data = json.loads(Path(f'hi_convolution_native_{n}_certificates.json').read_text())
    modulus = data['modulus']
    ring = UnramifiedRing([(modulus >> i) & 1 for i in range(modulus.bit_length())], 8)
    counts = Counter()
    for phases in all_phases(n, ring, data['delta']):
        q = residue_q(ring, data['delta'], phases)
        obstructions = first_obstructions(n, ring, data['delta'], phases)
        for value, (orbit, _, _) in zip(obstructions, seed_orbits(n)):
            h = 2*orbit[0] % n
            total = 0
            for g in range(1, (n+1)//2):
                assert q[g][h] == q[-g][h]
                total ^= q[g][h]
            assert value == ring.ff_mul(data['delta'], total)
        is_q = not any(value for row in q for value in row)
        assert not is_q or not any(obstructions)
        counts[is_q] += 1
    print(f'EXACT residue identity n={n}; tuples={sum(counts.values())}; Q={counts[True]}', flush=True)


def branch_checks(n, bits=6):
    data = json.loads(Path(f'hi_convolution_native_{n}_certificates.json').read_text())
    modulus = data['modulus']
    ring = UnramifiedRing([(modulus >> i) & 1 for i in range(modulus.bit_length())], bits)
    counts = Counter()
    for record in data['records']:
        if not record['q']:
            continue
        delta, phases, _ = lift_convolution(ring, n, data['delta'], record['phases'])
        residuals = q_residuals(ring, delta, phases)
        q = min(ring.valuation(value) for row in residuals for value in row)
        s = min(ring.valuation(ring.sub(ring.mul(phases[a], phases[-a]), delta))
                for a in range(1, n))
        assert s >= min(bits, q+1)
        counts[q, s] += record['orbit_length']
    print(f'EXACT lifted branches n={n}; (Q_v,norm_v):counts={dict(counts)}; cap={bits}', flush=True)


def perturbed_checks(n):
    data = json.loads(Path(f'hi_convolution_native_{n}_certificates.json').read_text())
    modulus = data['modulus']
    ring = UnramifiedRing([(modulus >> i) & 1 for i in range(modulus.bit_length())], 8)
    record = next(record for record in data['records'] if record['q'])
    delta, base, _ = lift_convolution(ring, n, data['delta'], record['phases'])
    rng = random.Random(10200+n)
    counts = Counter()
    for precision in (1, 2, 3, 4):
        phases = [ring.scalar(-1)]+[ring.zero]*(n-1)
        for a in range(1, (n+1)//2):
            correction = ring.scale(ring.lift(rng.randrange(1 << ring.degree)), 1 << precision)
            phases[a] = ring.add(base[a], correction)
            phases[-a] = ring.mul(delta, ring.inv(phases[a]))
        residuals = q_residuals(ring, delta, phases)
        updated = step(ring, delta, phases)
        assert updated[0] == ring.scalar(-1)
        q = min(ring.valuation(value) for row in residuals for value in row)
        s = ring.bits
        for h in range(1, n):
            total = ring.zero
            for g in range(1, (n+1)//2):
                assert residuals[g][h] == residuals[-g][h]
                total = ring.add(total, residuals[g][h])
            actual = ring.sub(ring.mul(updated[h], updated[-h]), delta)
            assert actual == ring.scale(ring.mul(delta, total), 2)
            s = min(s, ring.valuation(actual))
        assert q >= precision and s >= min(ring.bits, q+1)
        counts[q, s] += 1
    print(f'EXACT perturbed lifts n={n}; (Q_v,updated_norm_v):counts={dict(counts)}', flush=True)


def main():
    started = time.monotonic()
    for n in (3, 5, 7, 9):
        small_census(n)
        perturbed_checks(n)
    for n in (3, 5, 7, 9, 15, 19, 21, 27):
        branch_checks(n)
    print(f'elapsed_seconds={time.monotonic()-started:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: paired Q identities and finite lift checks; no uniform cubic completion claimed.')


if __name__ == '__main__':
    main()
