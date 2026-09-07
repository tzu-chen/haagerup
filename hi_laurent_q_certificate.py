"""Bounded-degree Laurent certificates for a generic balanced cubic.

Eliminate opposite phases using W_a W_-a = omega in characteristic 2.
Use exact GF(4) bit-plane row reduction on monomial multiples of Q.
Every positive result is replayed as a polynomial identity. A bounded
negative result is only a failure of this certificate ansatz.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import resource
import time


MUL = ((0, 0, 0, 0), (0, 1, 2, 3), (0, 2, 3, 1), (0, 3, 1, 2))


def add_term(poly, exponent, coefficient):
    value = poly.get(exponent, 0) ^ coefficient
    if value:
        poly[exponent] = value
    else:
        poly.pop(exponent, None)


def phase_product(n, indices):
    r = (n-1)//2
    exponent, coefficient = [0]*r, 1
    for a in indices:
        a %= n
        if not a:
            continue
        if a <= r:
            exponent[a-1] += 1
        else:
            exponent[n-a-1] -= 1
            coefficient = MUL[coefficient][2]
    return tuple(exponent), coefficient


def q_polynomial(n, g, h):
    result = {}
    for m in range(n):
        add_term(result, *phase_product(n, (m, h-m, -m-g, m+g-h)))
    return result


def cubic_polynomial(n, quad):
    g, h, k, ell = quad
    a, c = (0, (k-g) % n, (ell-h) % n), ((g+h) % n, -k % n, -ell % n)
    assert all((x+y) % n for x in a for y in c)
    result = {}
    for m in range(n):
        add_term(result, *phase_product(n, [m+x for x in a]+[-m+y for y in c]))
    add_term(result, *phase_product(n, [x+y for x in a for y in c]))
    return result


def shell(rank, level):
    if rank == 0:
        if level == 0:
            yield ()
        return
    for first in range(-level, level+1):
        for rest in shell(rank-1, level-abs(first)):
            yield (first,)+rest


def scaled(planes, coefficient):
    a, b = planes
    if coefficient == 1:
        return a, b
    if coefficient == 2:
        return b, a ^ b
    if coefficient == 3:
        return a ^ b, a
    return 0, 0


class LinearSpan:
    def __init__(self):
        self.columns = {}
        self.basis = {}
        self.inputs = []

    def encode(self, poly, shift):
        planes = [0, 0]
        for exponent, coefficient in poly.items():
            key = tuple(a+b for a, b in zip(exponent, shift))
            if key not in self.columns:
                self.columns[key] = len(self.columns)
            mask = 1 << self.columns[key]
            if coefficient & 1:
                planes[0] ^= mask
            if coefficient & 2:
                planes[1] ^= mask
        return tuple(planes)

    def reduce(self, row, certificate=(0, 0)):
        a, b = row
        u, v = certificate
        while a | b:
            pivot = (a | b).bit_length()-1
            previous = self.basis.get(pivot)
            if previous is None:
                break
            coefficient = ((a >> pivot) & 1)+2*((b >> pivot) & 1)
            x, y = scaled(previous[:2], coefficient)
            z, t = scaled(previous[2:], coefficient)
            a ^= x
            b ^= y
            u ^= z
            v ^= t
        return a, b, u, v

    def insert(self, poly, shift, label):
        index = len(self.inputs)
        self.inputs.append((label, shift))
        a, b, u, v = self.reduce(self.encode(poly, shift), (1 << index, 0))
        if not (a | b):
            return
        pivot = (a | b).bit_length()-1
        coefficient = ((a >> pivot) & 1)+2*((b >> pivot) & 1)
        inverse = (0, 1, 3, 2)[coefficient]
        self.basis[pivot] = scaled((a, b), inverse)+scaled((u, v), inverse)

    @staticmethod
    def pairing(row, functional):
        a, b = row
        c, d = functional
        first = ((a & c).bit_count()+(b & d).bit_count()) & 1
        second = ((a & d).bit_count()+(b & c).bit_count()+(b & d).bit_count()) & 1
        return first+2*second

    def separator(self, target):
        residual = self.reduce(target)
        assert residual[0] | residual[1]
        free_pivot = (residual[0] | residual[1]).bit_length()-1
        assert free_pivot not in self.basis
        functional = [0, 0]
        for column in range(len(self.columns)):
            if column in self.basis:
                value = self.pairing(self.basis[column][:2], functional)
            else:
                value = int(column == free_pivot)
            if value & 1:
                functional[0] ^= 1 << column
            if value & 2:
                functional[1] ^= 1 << column
        value = self.pairing(target, functional)
        assert value
        result = scaled(functional, (0, 1, 3, 2)[value])
        assert self.pairing(target, result) == 1
        assert all(self.pairing(row[:2], result) == 0 for row in self.basis.values())
        return result


def save_certificate(n, quad, level, generators, span, remainder, start):
    replay, terms, degree_counts = {}, [], Counter()
    first, second = remainder[2:]
    for index, (label, shift) in enumerate(span.inputs):
        coefficient = ((first >> index) & 1)+2*((second >> index) & 1)
        if not coefficient:
            continue
        terms.append(dict(q=label, shift=shift, coefficient=coefficient))
        degree_counts[sum(abs(a) for a in shift)] += 1
        for exponent, value in generators[label].items():
            add_term(replay, tuple(a+b for a, b in zip(exponent, shift)), MUL[coefficient][value])
    assert replay == cubic_polynomial(n, quad)
    suffix = target_suffix(n, quad)
    Path(f'hi_laurent_q_{n}{suffix}_certificate.json').write_text(json.dumps(
        dict(n=n, omega=2, quad=quad, multiplier_bound=level, terms=terms), indent=2)+'\n')
    print(f'CERTIFIED n={n}; terms={len(terms)}; multiplier_degrees={dict(degree_counts)}; '
          f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)


def target_suffix(n, quad):
    default = (1, 2, 5, 3) if n >= 9 else (1, 1, 1, 1)
    return '' if tuple(quad) == default else '_q'+'_'.join(map(str, quad))


def run(n, level_limit, seconds, memory_mib, checkpoint_rows=0, quad=None):
    start = time.monotonic()
    r = (n-1)//2
    if quad is None:
        quad = (1, 2, 5, 3) if n >= 9 else (1, 1, 1, 1)
    quad = tuple(a % n for a in quad)
    target = cubic_polynomial(n, quad)
    generators = {(g, h): q_polynomial(n, g, h) for g in range(1, r+1) for h in range(g, r+1)}
    weight = lambda exponent: sum((a+1)*value for a, value in enumerate(exponent)) % n
    assert all(weight(exponent) == 0 for exponent in target)
    assert all(weight(exponent) == 0 for poly in generators.values() for exponent in poly)
    span = LinearSpan()
    for level in range(level_limit+1):
        for shift in shell(r, level):
            # The equations and target have cyclic character weight zero.
            # Other weight blocks cannot contribute to this identity.
            if weight(shift):
                continue
            for label, poly in generators.items():
                if time.monotonic()-start > seconds:
                    print(f'INCOMPLETE n={n}; level={level}; timeout_seconds={seconds}; '
                          f'inputs={len(span.inputs)}; columns={len(span.columns)}; '
                          f'rank={len(span.basis)}', flush=True)
                    return
                if len(span.inputs) % 100 == 0:
                    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024
                    if rss > memory_mib:
                        print(f'INCOMPLETE n={n}; level={level}; memory_limit_MiB={memory_mib}; '
                              f'inputs={len(span.inputs)}; columns={len(span.columns)}; '
                              f'rank={len(span.basis)}', flush=True)
                        return
                span.insert(poly, shift, label)
                # A certificate can appear before the final row of a level.
                # Check only after level zero, preserving the original
                # column order and hence all previous search conventions.
                if level and checkpoint_rows and len(span.inputs) % checkpoint_rows == 0:
                    remainder = span.reduce(span.encode(target, (0,)*r))
                    if not (remainder[0] | remainder[1]):
                        print(f'EARLY_MEMBER n={n}; L1_multiplier_bound={level}; '
                              f'inputs={len(span.inputs)}; columns={len(span.columns)}; '
                              f'rank={len(span.basis)}', flush=True)
                        save_certificate(n, quad, level, generators, span, remainder, start)
                        return
        remainder = span.reduce(span.encode(target, (0,)*r))
        passed = not (remainder[0] | remainder[1])
        print(f'LEVEL n={n}; L1_multiplier_bound={level}; inputs={len(span.inputs)}; '
              f'columns={len(span.columns)}; rank={len(span.basis)}; member={passed}', flush=True)
        if not passed:
            continue
        save_certificate(n, quad, level, generators, span, remainder, start)
        return
    functional = span.separator(span.encode(target, (0,)*r))
    for label, shift in span.inputs:
        assert span.pairing(span.encode(generators[label], shift), functional) == 0
    values = []
    for exponent, column in span.columns.items():
        value = ((functional[0] >> column) & 1)+2*((functional[1] >> column) & 1)
        if value:
            values.append(dict(exponent=exponent, coefficient=value))
    suffix = target_suffix(n, quad)
    Path(f'hi_laurent_q_{n}{suffix}_bound{level_limit}_obstruction.json').write_text(json.dumps(
        dict(n=n, omega=2, quad=quad, multiplier_bound=level_limit, functional=values), indent=2)+'\n')
    print(f'BOUNDED_NONMEMBERSHIP n={n}; multiplier_bound={level_limit}; '
          f'dual_support={len(values)}; no nonexistence claim', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[3, 5, 7, 9])
    parser.add_argument('--level', type=int, default=5)
    parser.add_argument('--timeout', type=float, default=45)
    parser.add_argument('--memory-mib', type=float, default=256)
    parser.add_argument('--checkpoint-rows', type=int, default=0,
                        help='Check for a replayable positive certificate within each level')
    parser.add_argument('--quad', type=int, nargs=4,
                        help='A specified cross-free cubic target; keeps separate certificate files')
    args = parser.parse_args()
    if (any(n not in range(3, 18, 2) for n in args.orders)
            or not 0 <= args.level <= 7 or args.checkpoint_rows < 0):
        raise ValueError('This bounded search supports odd orders 3..17 and levels 0..7')
    for n in args.orders:
        run(n, args.level, args.timeout, args.memory_mib, args.checkpoint_rows, args.quad)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)


if __name__ == '__main__':
    main()
