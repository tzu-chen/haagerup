"""Check canonical balanced lifts for the finite double-sine targets.

The lift and sign identities are exact integer checks. The finite
additive identities are only numerical checks, not an infinitude proof.
"""

import argparse
from itertools import combinations_with_replacement

import mpmath as mp

from hi_shintani_meromorphic import sine


def canonical_lifts(n, p, q):
    """Zeros p of positive factors and q of negative factors, modulo n."""
    r = len(p)
    assert r in (2, 3) and len(q) == r and n % 2 == 1
    assert (sum(q)-sum(p)) % n == 0 and set(p).isdisjoint(q)
    for swapped in range(2 if r == 3 else 1):
        pp, qq = (q, p) if swapped else (p, q)
        for shift in range(n):
            a = tuple(-((x-shift) % n) for x in pp)
            c = tuple((x-shift) % n for x in qq)
            if sum(a)+sum(c) == (r-2)*n:
                return a, c, shift, bool(swapped)
    raise AssertionError('The uniform canonical-lift lemma failed')


def exact_checks(n):
    examples = {}
    for r in (2, 3):
        lists = list(combinations_with_replacement(range(n), r))
        by_sum = {}
        for q in lists:
            by_sum.setdefault(sum(q) % n, []).append(q)
        count = swaps = 0
        for p in lists:
            for q in by_sum[sum(p) % n]:
                if not set(p).isdisjoint(q):
                    continue
                a, c, shift, swapped = canonical_lifts(n, p, q)
                count += 1
                swaps += swapped
                assert all(-(n-1) <= x <= 0 for x in a)
                assert all(0 <= x <= n-1 for x in c)
                assert all(x+y != 0 for x in a for y in c)
                E = sum(x*(x+n)//2 for x in a+c)
                for m in range(n):
                    arguments = tuple(m+x for x in a)+tuple(x-m for x in c)
                    assert all(-(n-1) <= x <= n-1 for x in arguments)
                    sign = sum(x*(x+n)//2 for x in arguments)
                    assert (sign-E) % 2 == 0
                if r == 3:
                    J = sum((x+y)*(x+y+n)//2 for x in a for y in c)
                    assert (J-E) % 2 == 0
                # Save one representative needing reversal if available.
                if r not in examples or (swapped and not examples[r][2]):
                    examples[r] = (a, c, swapped)
        print(f'EXACT n={n}, r={r}: all {count} balanced cross-free multiset '
              f'pairs pass lift and sign checks; {swaps} use reversal.', flush=True)
    return examples


def numerical_checks(n, examples):
    d = (n+mp.sqrt(n*n+4))/2
    A, B = d+1, 1+1/d
    cache = {}

    def F(k):
        if k not in cache:
            cache[k] = sine(1+k/B, d)
        return cache[k]

    for r, (a, c, _) in examples.items():
        terms = [mp.fprod(F(m+x) for x in a)*mp.fprod(F(x-m) for x in c)
                 for m in range(n)]
        left = mp.fsum(terms)
        if r == 2:
            error = abs(left)/max(1, sum(abs(x) for x in terms))
        else:
            right = mp.sqrt(A*B)*mp.fprod(F(x+y) for x in a for y in c)
            error = abs(left-right)/max(1, abs(right), sum(abs(x) for x in terms))
        assert error < mp.power(10, -mp.mp.dps+12)
        print(f'NUMERICAL n={n}, r={r}: bare-sine finite target relative '
              f'residual={mp.nstr(error, 7)}; a={a}, c={c}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[3, 5, 7, 9, 11])
    parser.add_argument('--numerical-orders', nargs='*', type=int, default=[3, 7, 11])
    parser.add_argument('--digits', type=int, default=40)
    args = parser.parse_args()
    mp.mp.dps = args.digits
    for n in args.orders:
        examples = exact_checks(n)
        if n in args.numerical_orders:
            numerical_checks(n, examples)
    print('ALL CANONICAL-LIFT CHECKS PASSED; uniform finite sums remain unproved.')


if __name__ == '__main__':
    main()
