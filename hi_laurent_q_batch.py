"""Bounded Laurent certificates for every cubic orbit at one finite order.

One exact GF(4) row space is shared by all targets. Positive certificates
are replayed before writing; a completed negative search saves a separating
functional for one target. A resource stop never asserts nonmembership.
"""

import argparse
from collections import Counter
import gzip
import json
from pathlib import Path
import resource
import time

from hi_beta_reductions import beta_representatives
from hi_laurent_q_certificate import (
    LinearSpan, MUL, add_term, cubic_polynomial, q_polynomial, shell,
)


def certificate(n, quad, level, generators, span, remainder):
    first, second = remainder[2:]
    terms, replay = [], {}
    for index, (label, shift) in enumerate(span.inputs):
        coefficient = ((first >> index) & 1) + 2 * ((second >> index) & 1)
        if not coefficient:
            continue
        terms.append(dict(q=label, shift=shift, coefficient=coefficient))
        for exponent, value in generators[label].items():
            add_term(replay, tuple(a+b for a, b in zip(exponent, shift)),
                     MUL[coefficient][value])
    assert replay == cubic_polynomial(n, quad)
    return dict(n=n, omega=2, quad=quad, multiplier_bound=level, terms=terms)


def run(n, max_level, timeout, memory_mib, checkpoint):
    start = time.monotonic()
    r = (n-1)//2
    representatives, covered_count = beta_representatives(n)
    targets = {quad: cubic_polynomial(n, quad) for quad in representatives}
    pending = dict(targets)
    generators = {(g, h): q_polynomial(n, g, h)
                  for g in range(1, r+1) for h in range(g, r+1)}
    weight = lambda exponent: sum((a+1)*e for a, e in enumerate(exponent)) % n
    assert all(weight(e) == 0 for p in [*generators.values(), *targets.values()] for e in p)
    span = LinearSpan()
    certified = []
    data = dict(n=n, omega=2, representatives=representatives,
                covered_count=covered_count, certificates=certified,
                complete_degree_bound=False)

    def check_targets(level):
        for quad, poly in list(pending.items()):
            remainder = span.reduce(span.encode(poly, (0,)*r))
            if remainder[0] | remainder[1]:
                continue
            cert = certificate(n, quad, level, generators, span, remainder)
            certified.append(cert)
            del pending[quad]
            print(f'CERTIFIED n={n}; quad={quad}; L={level}; '
                  f'terms={len(cert["terms"])}; remaining={len(pending)}', flush=True)

    terminal = None
    for level in range(max_level+1):
        for shift in shell(r, level):
            if weight(shift):
                continue
            for label, poly in generators.items():
                if time.monotonic()-start > timeout:
                    terminal = 'timeout'
                    break
                if len(span.inputs) % 100 == 0:
                    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024
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
        print(f'LEVEL n={n}; L={level}; inputs={len(span.inputs)}; '
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
        functional = span.separator(span.encode(poly, (0,)*r))
        for label, shift in span.inputs:
            assert span.pairing(span.encode(generators[label], shift), functional) == 0
        values = []
        for exponent, column in span.columns.items():
            value = ((functional[0] >> column) & 1) + 2*((functional[1] >> column) & 1)
            if value:
                values.append(dict(exponent=exponent, coefficient=value))
        data['obstruction'] = dict(n=n, omega=2, quad=quad,
                                   multiplier_bound=max_level, functional=values)
        print(f'BOUNDED_NONMEMBERSHIP n={n}; quad={quad}; L={max_level}; '
              f'dual_support={len(values)}', flush=True)
        terminal = 'completed_bound'
    else:
        print(f'INCOMPLETE n={n}; reason={terminal}; inputs={len(span.inputs)}; '
              f'columns={len(span.columns)}; rank={len(span.basis)}', flush=True)

    data['terminal'] = terminal
    data['pending'] = list(pending)
    path = Path(f'hi_laurent_q_batch{n}_certificates.json.gz')
    with gzip.open(path, 'wt') as output:
        json.dump(data, output, separators=(',', ':'))
        output.write('\n')
    print(f'BUNDLE {path}; certificates={len(certified)}/{len(targets)}; '
          f'bounds={dict(Counter(c["multiplier_bound"] for c in certified))}; '
          f'complete_degree_bound={data["complete_degree_bound"]}', flush=True)
    print(f'elapsed_seconds={time.monotonic()-start:.3f}; '
          f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('Finite identities only. No new category existence or uniform degree bound is asserted.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=13)
    parser.add_argument('--level', type=int, default=6)
    parser.add_argument('--timeout', type=float, default=60)
    parser.add_argument('--memory-mib', type=float, default=192)
    parser.add_argument('--checkpoint-rows', type=int, default=512)
    args = parser.parse_args()
    if args.order not in range(3, 18, 2) or not 0 <= args.level <= 7 or args.checkpoint_rows <= 0:
        raise ValueError('Require odd order 3..17, level 0..7, positive checkpoint interval')
    run(args.order, args.level, args.timeout, args.memory_mib, args.checkpoint_rows)


if __name__ == '__main__':
    main()
