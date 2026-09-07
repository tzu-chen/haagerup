"""Exhaust a proposed degree-six recursion for the two-quadratic solutions.

This independently rebuilds the first-phase eliminants at 3, 9 and 27
from exhaustive norm/Frobenius searches. It then enumerates every degree-6
rational map over F4 whose pullback of the order-3 eliminant is the
order-9 eliminant, and tests its next pullback against order 27.
All 20 maps fail. It also excludes a stationary degree-3 recursion on
any single branch: each of the two order-9 branches gives 10 maps, and
none has a full order-27 branch as its next preimage. These statements
do not exclude multivariable constructions or an infinite HI family.
Requires Python, PARI/GP, and a C++17 compiler.
"""

import json,subprocess,sys,itertools
from hi_char2_small_field_obstruction import field_table,power
from pathlib import Path
import tempfile
from hi_char2_frobenius import search


def eliminants():
    polynomials = {}
    with tempfile.TemporaryDirectory(prefix='hi_twoq_recursion_') as tmp:
        for n, expected in [(3, 2), (9, 12), (27, 72)]:
            partial = []
            degree, modulus, omega, alpha, orders, _ = search(n, Path(tmp), partial)
            def multiply(a, b):
                result = 0
                while b:
                    if b & 1:
                        result ^= a
                    b >>= 1
                    a <<= 1
                    if a >> degree:
                        a ^= modulus
                return result
            def exponentiate(a, exponent):
                result = 1
                while exponent:
                    if exponent & 1:
                        result = multiply(result, a)
                    a = multiply(a, a)
                    exponent >>= 1
                return result
            roots = {multiply(omega ^ 1, exponentiate(alpha, seed[0])) for seed in partial}
            assert len(partial) == len(roots) == expected
            p = [1]
            for root in roots:
                nxt = [0]*(len(p)+1)
                for j, value in enumerate(p):
                    nxt[j] ^= multiply(value, root)
                    nxt[j+1] ^= value
                p = nxt
            encode = {0: 0, 1: 1, omega: 2, omega ^ 1: 3}
            assert all(a in encode for a in p)
            polynomials[str(n)] = [encode[a] for a in p]
            print(f'TWO-Q order {n} first-phase eliminant, ascending F4 coefficients: '
                  f'{polynomials[str(n)]}', flush=True)
    return polynomials


F = field_table(2, 7)
E = field_table(4, 19)


def gp_poly(v):
    return '+'.join(f'({a & 1}+{a >> 1}*d)*x^{i}'
                    for i, a in enumerate(v) if a)


def gp_json(source):
    result = subprocess.run(['gp', '-q', '-f'], input=source, text=True,
                            capture_output=True, check=True)
    if result.stderr:
        raise ArithmeticError(result.stderr)
    return json.loads(result.stdout)


def factors_f4(polynomials):
    expressions = ','.join(f'factor({gp_poly(p)})' for p in polynomials)
    return gp_json(f"""
z=ffgen(Mod(1,2)*(t^2+t+1),'z);d=z;
enc(a)=sum(j=0,1,lift(polcoef(a.pol,j))*2^j);
fs=[{expressions}];
print(vector(#fs,k,vector(matsize(fs[k])[1],m,vector(poldegree(fs[k][m,1])+1,j,enc(polcoef(fs[k][m,1],j-1))))));quit;
""")


def pmul(a, b, table):
    result = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i+j] ^= table[x][y]
    while len(result) > 1 and not result[-1]:
        result.pop()
    return result


def homogenized(p, A, B):
    n = len(p)-1
    aa, bb = [[1]], [[1]]
    for _ in range(n):
        aa.append(pmul(aa[-1], A, F))
        bb.append(pmul(bb[-1], B, F))
    result = [0]*(n*max(len(A)-1, len(B)-1)+1)
    for i, c in enumerate(p):
        if c:
            for j, value in enumerate(pmul(aa[i], bb[n-i], F)):
                result[j] ^= F[c][value]
    while len(result) > 1 and not result[-1]:
        result.pop()
    return result


def monic(p):
    inverse = next(a for a in range(1, 4) if F[a][p[-1]] == 1)
    return [F[inverse][a] for a in p]


def preimage_maps(base, target):
    """Every rational map over F4 with pullback of base proportional to target.

    The base is the irreducible order-3 quadratic. The squarefree target
    factors over F16 into conjugate pairs. Coprimality forces one factor
    of each pair into A+rB, and the other into A+r^4 B.
    """
    d, root, factors = gp_json(f"""
z=ffgen(Mod(1,2)*(t^4+t+1),'z);d=z^5;
enc(a)=sum(j=0,3,lift(polcoef(a.pol,j))*2^j);
f1=factor({gp_poly(base)});r=-polcoef(f1[1,1],0);f2=factor({gp_poly(target)});
print([enc(d),enc(r),vector(matsize(f2)[1],m,vector(poldegree(f2[m,1])+1,j,enc(polcoef(f2[m,1],j-1))))]);quit;
""")
    embed = [0, 1, d, d ^ 1]
    decode = {embed[a] ^ E[root][embed[b]]: (a, b)
              for a in range(4) for b in range(4)}
    assert len(decode) == 16 and all(len(f) == 4 for f in factors)
    pairs, remaining = [], list(range(len(factors)))
    while remaining:
        i = remaining.pop(0)
        conjugate = [power(E, c, 4) for c in factors[i]]
        j = next(j for j in remaining if factors[j] == conjugate)
        remaining.remove(j)
        pairs.append([i, j])
    maps = set()
    for choice in itertools.product(*pairs):
        Q = [1]
        for i in choice:
            Q = pmul(Q, factors[i], E)
        for scalar in range(1, 16):
            A, B = map(list, zip(*(decode[E[scalar][c]] for c in Q)))
            while len(A) > 1 and not A[-1]:
                A.pop()
            while len(B) > 1 and not B[-1]:
                B.pop()
            scale = next(t for t in range(1, 4) if F[t][A[-1]] == 1)
            A, B = [F[scale][a] for a in A], [F[scale][b] for b in B]
            key = (tuple(A), tuple(B))
            if key in maps:
                continue
            assert monic(homogenized(base, A, B)) == target
            assert 2*max(len(A)-1, len(B)-1) == len(target)-1
            maps.add(key)
    assert len(maps) == 5*2**len(pairs)
    return sorted(maps)


def main():
    polynomials = eliminants()
    base, order9, order27 = [polynomials[str(n)] for n in [3, 9, 27]]
    maps = preimage_maps(base, order9)
    assert len(maps) == 20
    assert all(monic(homogenized(order9, A, B)) != order27 for A, B in maps)
    print('ALL 20 DEGREE-SIX RATIONAL MAPS REJECTED: '
          'no single F4 rational map gives both preimage steps.', flush=True)

    branches9, factors27 = factors_f4([order9, order27])
    assert len(branches9) == 2 and all(len(p) == 7 for p in branches9)
    assert sorted(len(p)-1 for p in factors27) == [6, 6, 6, 18, 18, 18]
    branches27 = [p for p in factors27 if len(p) == 19]
    for i, branch in enumerate(branches9):
        maps = preimage_maps(base, branch)
        assert len(maps) == 10
        assert all(monic(homogenized(branch, A, B)) not in branches27 for A, B in maps)
        print(f'order-9 branch {i}, ascending F4 coefficients {branch}: '
              'all 10 degree-three maps fail every full order-27 branch.', flush=True)
    print('ALL EXACT RATIONAL-RECURSION CHECKS PASSED; infinitude is not established.')


if __name__ == '__main__':
    main()
