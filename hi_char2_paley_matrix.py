"""Exact checks of a matrix-level obstruction to diagonal cubic completion.

At primes p=7 modulo 8 a Legendre-symbol matrix over F4 satisfies
order-three symmetry, fixed axes, Q, transpose inverse products, and
Frobenius covariance. It fails an explicitly counted family of cubics.
It does NOT have the normalized phase factorization, so it is not a
counterexample to the remaining phase-specific implication in Section 94.
"""

import argparse
import resource
import time


# F4 = F2[d]/(d^2+d+1), encoded by binary coefficients.
MUL = [[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]]
DELTA, T = 2, 3


def is_prime(p):
    return p >= 2 and all(p % d for d in range(2, int(p**0.5)+1))


def run(p):
    assert is_prime(p) and p % 8 == 7
    chi = [0] + [1 if pow(a, (p-1)//2, p) == 1 else -1 for a in range(1, p)]
    A = [[DELTA if g == 0 or h == 0 or g == h else
          DELTA ^ int(chi[g]*chi[h]*chi[(h-g) % p] == -1)
          for h in range(p)] for g in range(p)]
    A[0][0] = T
    assert all(A[g][h] == A[-h % p][(g-h) % p]
               for g in range(p) for h in range(p))
    assert all(A[2*g % p][2*h % p] == MUL[MUL[A[g][h]][A[g][h]]][MUL[A[g][h]][A[g][h]]]
               for g in range(p) for h in range(p))
    assert all(MUL[A[g][h]][A[h][g]] == 1
               for g in range(1, p) for h in range(1, p) if g != h)
    for g in range(p):
        for h in range(p):
            residual = int(g == 0) ^ (T if h == 0 else 0)
            for m in range(p):
                residual ^= MUL[A[(g+m) % p][h]][A[h][m]]
            assert residual == 0, ('Q', p, g, h, residual)

    def cubic(g, h, k, ell):
        residual = MUL[A[(g+ell) % p][k]][A[(h+k) % p][ell]]
        if g == h == 0:
            residual ^= T
        for m in range(p):
            residual ^= MUL[A[m][(g+h) % p]][MUL[A[g][(m+k) % p]][A[h][(m+ell) % p]]]
        return residual

    assert all(cubic(g, g, k, k) == 0 for g in range(p) for k in range(p))
    witnesses = [b for b in range(p)
                 if chi[b] == 1 and chi[(b+1) % p] == -1 and chi[(b+2) % p] == 1]
    assert len(witnesses) == (p+1)//8
    assert all(cubic(0, 1, b, (b+2) % p) == 1 for b in witnesses)

    def beta(a, b):
        a, b = a % p, b % p
        if (a+b) % p == 0:
            return DELTA if a else 1
        return MUL[T][A[a][(a+b) % p]]

    for b in witnesses:
        left = MUL[beta(1, 1)][beta(2, b)]
        right = MUL[beta(1, b)][beta(1, b+1)]
        assert left == 1 and right == T
    print(f'EXACT p={p}: all Q, order-three symmetry, inverse products, '
          'Frobenius, and all diagonal C: PASS', flush=True)
    print(f'  failing cubics C(0,1,b,b+2)=1: {len(witnesses)}; '
          f'first b={witnesses[0]}; phase cocycle fails as 1 != d+1', flush=True)
    if p == 7:
        print(f'  explicit F4 matrix (d=2, d+1=3): {A}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--primes', type=int, nargs='+', default=[7, 23, 31, 47, 71, 79, 103])
    args = parser.parse_args()
    start = time.monotonic()
    for p in args.primes:
        run(p)
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: exact counterexamples to matrix-level diagonal completion. '
          'The phase-specific implication and HI infinitude remain unresolved.')


if __name__ == '__main__':
    main()
