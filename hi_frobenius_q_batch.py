"""Exact bounded Q-to-cubic certificates modulo norm and canonical Frobenius.

Use the finite group algebra GF(4)[z_i]/(z_i**M_i-1), with W_a=omega**2
times a root monomial for a != 0. Section 72.1 proves this is the full
norm/Frobenius coordinate algebra. Degree means Laurent word length in
the original positive-index phases, not degree in the root coordinates.
There is no character-weight filter in this quotient.
"""

import argparse
from collections import Counter
import gzip
import json
from math import prod
from pathlib import Path
import resource
import time

from hi_beta_reductions import beta_representatives
from hi_char2_general_search import seed_orbits
from hi_laurent_q_certificate import LinearSpan, MUL, add_term, shell


MODEL = 'canonical_norm_frobenius_v1'
CPOW = (1, 3, 2)


class PhaseRing:
    def __init__(self, n):
        self.n = n
        self.orbits = seed_orbits(n)
        self.periods = tuple(size for _, _, size in self.orbits)
        self.zero = (0,)*len(self.periods)
        self.images = [None]*n
        self.images[0] = self.zero
        for i, (orbit, paired, period) in enumerate(self.orbits):
            value = 1
            for a in orbit:
                row = [0]*len(self.periods)
                row[i] = value
                self.images[a] = tuple(row)
                if paired:
                    row = [0]*len(self.periods)
                    row[i] = -value % period
                    self.images[-a % n] = tuple(row)
                value = 4*value % period
        assert all(row is not None for row in self.images)
        for a in range(1, n):
            assert self.plus(self.images[a], self.images[-a]) == self.zero
            assert tuple(4*v % m for v, m in zip(self.images[a], self.periods)) == self.images[2*a % n]

    def plus(self, left, right):
        return tuple((a+b) % m for a, b, m in zip(left, right, self.periods))

    def word(self, word):
        assert len(word) == (self.n-1)//2
        exponent = tuple(sum(e*self.images[a+1][i] for a, e in enumerate(word)) % m
                         for i, m in enumerate(self.periods))
        return exponent, CPOW[sum(word) % 3]

    def phase_product(self, indices):
        indices = [a % self.n for a in indices]
        exponent = tuple(sum(self.images[a][i] for a in indices) % m
                         for i, m in enumerate(self.periods))
        return exponent, CPOW[sum(a != 0 for a in indices) % 3]

    def q(self, g, h):
        result = {}
        for m in range(self.n):
            add_term(result, *self.phase_product((m, h-m, -m-g, m+g-h)))
        return result

    def cubic(self, quad):
        g, h, k, ell = quad
        a, c = (0, k-g, ell-h), (g+h, -k, -ell)
        assert all((x+y) % self.n for x in a for y in c)
        result = {}
        for m in range(self.n):
            add_term(result, *self.phase_product([m+x for x in a]+[-m+y for y in c]))
        add_term(result, *self.phase_product([x+y for x in a for y in c]))
        return result

    def lift_error(self, g, h):
        pairs = [[] for _ in range(self.n)]
        for i in range(self.n):
            for j in range(i+1, self.n):
                pairs[(i+j) % self.n].append((i, j))
        quartets = [(m, (h-m) % self.n, (-m-g) % self.n,
                     (m+g-h) % self.n) for m in range(self.n)]
        result = {}
        for m, indices in enumerate(quartets):
            for other in quartets[:m]:
                add_term(result, *self.phase_product(indices+other))
            for slot, a in enumerate(indices):
                others = indices[:slot]+indices[slot+1:]
                for pair in pairs[a]:
                    add_term(result, *self.phase_product((a,)+2*others+2*pair))
        return result


class RingSpan(LinearSpan):
    def __init__(self, ring):
        super().__init__()
        self.ring = ring

    def encode(self, poly, shift):
        planes = [0, 0]
        for exponent, coefficient in poly.items():
            key = self.ring.plus(exponent, shift)
            if key not in self.columns:
                self.columns[key] = len(self.columns)
            mask = 1 << self.columns[key]
            if coefficient & 1:
                planes[0] ^= mask
            if coefficient & 2:
                planes[1] ^= mask
        return tuple(planes)


def export_certificate(ring, quad, level, generators, span, remainder, words):
    first, second = remainder[2:]
    terms, replay = [], {}
    for index, (label, shift) in enumerate(span.inputs):
        coefficient = ((first >> index) & 1)+2*((second >> index) & 1)
        if not coefficient:
            continue
        word, word_coefficient = words[shift]
        original_coefficient = MUL[coefficient][(0, 1, 3, 2)[word_coefficient]]
        term = dict(shift=word, coefficient=original_coefficient)
        term['q' if len(label) == 2 else 'lift'] = label if len(label) == 2 else label[1:]
        terms.append(term)
        for exponent, value in generators[label].items():
            add_term(replay, ring.plus(exponent, shift), MUL[coefficient][value])
    assert replay == ring.cubic(quad)
    return dict(n=ring.n, omega=2, model=MODEL, quad=quad,
                multiplier_bound=level, terms=terms)


def run(n, max_level, timeout, memory_mib, checkpoint, output, lift_errors=False):
    start = time.monotonic()
    r = (n-1)//2
    ring = PhaseRing(n)
    representatives, covered = beta_representatives(n)
    pending = {quad: ring.cubic(quad) for quad in representatives}
    generators = {(g, h): ring.q(g, h) for g in range(1, r+1) for h in range(g, r+1)}
    if lift_errors:
        generators.update({('L', g, h): ring.lift_error(g, h)
                           for g in range(1, r+1) for h in range(g, r+1)})
    generators = {label: poly for label, poly in generators.items() if poly}
    span, words, certified = RingSpan(ring), {}, []
    data = dict(n=n, omega=2, model=MODEL, periods=ring.periods, lift_errors=lift_errors,
                representatives=representatives, covered_count=covered,
                certificates=certified, complete_degree_bound=False)
    print(f'START n={n}; periods={ring.periods}; algebra_dimension={prod(ring.periods)}; '
          f'generators={len(generators)}; lift_errors={lift_errors}; '
          f'cubic_orbits={len(pending)}', flush=True)

    def check_targets(level):
        for quad, poly in list(pending.items()):
            remainder = span.reduce(span.encode(poly, ring.zero))
            if remainder[0] | remainder[1]:
                continue
            cert = export_certificate(ring, quad, level, generators, span, remainder, words)
            certified.append(cert)
            del pending[quad]
            print(f'CERTIFIED n={n}; quad={quad}; L={level}; '
                  f'terms={len(cert["terms"])}; remaining={len(pending)}', flush=True)

    terminal = None
    for level in range(max_level+1):
        for word in shell(r, level):
            shift, scalar = ring.word(word)
            if shift in words:
                continue
            words[shift] = (word, scalar)
            for label, poly in generators.items():
                if time.monotonic()-start > timeout:
                    terminal = 'timeout'
                    break
                if len(span.inputs) % 100 == 0:
                    # ru_maxrss retains the high-water mark of earlier orders.
                    # Enforce the cap against the actual current resident set.
                    rss = (int(Path('/proc/self/statm').read_text().split()[1])
                           * resource.getpagesize() / 2**20)
                    if rss > memory_mib:
                        terminal = 'memory_limit'
                        break
                span.insert(poly, shift, label)
                if level and len(span.inputs) % checkpoint == 0:
                    check_targets(level)
                    if not pending:
                        terminal = 'all_certified'
                        break
            if terminal:
                break
        if terminal:
            break
        check_targets(level)
        print(f'LEVEL n={n}; L={level}; words={len(words)}; inputs={len(span.inputs)}; '
              f'columns={len(span.columns)}; rank={len(span.basis)}; '
              f'pending={len(pending)}', flush=True)
        if not pending:
            terminal = 'all_certified'
            break

    if not pending:
        data['complete_degree_bound'] = True
        data['maximum_used_bound'] = max(c['multiplier_bound'] for c in certified)
    elif terminal is None:
        quad, poly = next(iter(pending.items()))
        functional = span.separator(span.encode(poly, ring.zero))
        for label, shift in span.inputs:
            assert span.pairing(span.encode(generators[label], shift), functional) == 0
        values = []
        for exponent, column in span.columns.items():
            value = ((functional[0] >> column) & 1)+2*((functional[1] >> column) & 1)
            if value:
                values.append(dict(exponent=exponent, coefficient=value))
        data['obstruction'] = dict(n=n, omega=2, model=MODEL, quad=quad, lift_errors=lift_errors,
                                   multiplier_bound=max_level, functional=values)
        print(f'BOUNDED_NONMEMBERSHIP n={n}; quad={quad}; L={max_level}; '
              f'dual_support={len(values)}', flush=True)
        terminal = 'completed_bound'
    else:
        print(f'INCOMPLETE n={n}; reason={terminal}; inputs={len(span.inputs)}; '
              f'columns={len(span.columns)}; rank={len(span.basis)}', flush=True)

    data['terminal'], data['pending'] = terminal, list(pending)
    data['statistics'] = dict(words=len(words), inputs=len(span.inputs),
                              columns=len(span.columns), rank=len(span.basis))
    prefix = 'hi_frobenius_ql' if lift_errors else 'hi_frobenius_q'
    path = output / f'{prefix}_batch{n}_L{max_level}_certificates.json.gz'
    with gzip.open(path, 'wt') as handle:
        json.dump(data, handle, separators=(',', ':'))
        handle.write('\n')
    print(f'BUNDLE {path}; certificates={len(certified)}/{len(representatives)}; '
          f'bounds={dict(Counter(c["multiplier_bound"] for c in certified))}; '
          f'complete_degree_bound={data["complete_degree_bound"]}', flush=True)
    print(f'elapsed_seconds={time.monotonic()-start:.3f}; '
          f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('Finite identities modulo norm and Frobenius; no uniform implication is asserted.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 5, 7, 9, 11, 13])
    parser.add_argument('--level', type=int, default=3)
    parser.add_argument('--timeout', type=float, default=60)
    parser.add_argument('--memory-mib', type=float, default=256)
    parser.add_argument('--checkpoint-rows', type=int, default=256)
    parser.add_argument('--output', type=Path, default=Path('.'))
    parser.add_argument('--lift-errors', action='store_true',
                        help='Also use the first balanced Q lift equations, equation 103.1')
    args = parser.parse_args()
    if (any(n not in range(3, 28, 2) for n in args.orders) or
            not 0 <= args.level <= 6 or args.checkpoint_rows <= 0 or
            args.timeout <= 0 or args.memory_mib <= 0):
        raise ValueError('Require odd orders 3..27, level 0..6 and positive resource limits')
    args.output.mkdir(parents=True, exist_ok=True)
    for n in args.orders:
        run(n, args.level, args.timeout, args.memory_mib, args.checkpoint_rows, args.output,
            args.lift_errors)


if __name__ == '__main__':
    main()
