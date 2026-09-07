"""Exhaustive characteristic-two phase searches at general odd cyclic orders.

Section 71 makes the Frobenius gauge lossless for full cubic phase
solutions. Doubling orbits paired by negation have an arbitrary nonzero
seed; self-paired orbits have one norm-torus seed. The current C++ search
supports at most three independent seeds and degrees below 63.
Every accepted orbit goes through the independent complete cubic verifier.
"""

import argparse
from collections import Counter
import json
from math import lcm, prod
from pathlib import Path
import re
import subprocess
import tempfile

from hi_char2_frobenius import CPP
from hi_finite_field_certificate import verify


def order2(n):
    a, r = 2 % n, 1
    while a != 1:
        a = 2*a % n
        r += 1
    return r


def seed_orbits(n):
    remaining, seeds = set(range(1, n)), []
    while remaining:
        first = min(remaining)
        orbit, a = [], first
        while a not in orbit:
            orbit.append(a)
            a = 2*a % n
        assert a == first
        paired = -first % n not in orbit
        length = len(orbit)
        size = 4**length-1 if paired else 2**length+1
        if not paired:
            assert length % 2 == 0 and orbit[length//2] == -first % n
        covered = set(orbit) | {-a % n for a in orbit}
        assert covered <= remaining
        remaining -= covered
        seeds.append((orbit, paired, size))
    return seeds


def quadratic_representatives(n):
    canonical = lambda a, b: tuple(sorted((min(a, n-a), min(b, n-b))))
    seen, reps = set(), []
    for g in range(1, (n+1)//2):
        for h in range(g, (n+1)//2):
            if (g, h) in seen:
                continue
            reps.append((g, h))
            a, b = g, h
            while canonical(a, b) not in seen:
                seen.add(canonical(a, b))
                a, b = 2*a % n, 2*b % n
    assert len(seen) == ((n-1)//2)*((n+1)//2)//2
    return reps


def field_parameters(degree, group_order):
    source = r'''
export_field()={
my(f=ffinit(2,DEG,'z),z=ffgen(f),g=ffprimroot(z),N=ORD,
 d=g^((2^DEG-1)/3),u=g^((2^DEG-1)/N));
if((2^DEG-1)%N,error("parameter group outside the field"));
print([sum(j=0,DEG,lift(polcoef(f,j))*2^j),
 sum(j=0,DEG-1,lift(polcoef(d.pol,j))*2^j),
 sum(j=0,DEG-1,lift(polcoef(u.pol,j))*2^j),Vec(factor(N)[,1])]);
};
iferr(export_field(),e,print(e);quit(1));quit;
'''.replace('DEG', str(degree)).replace('ORD', str(group_order))
    result = subprocess.run(['gp', '-q', '-f'], input=source, text=True,
                            capture_output=True, check=True)
    if result.stderr:
        raise ArithmeticError(result.stderr)
    return json.loads(result.stdout)


def search(n, directory, max_table):
    if n < 3 or n % 2 == 0:
        raise ValueError('An odd cyclic order at least 3 is required')
    seeds = seed_orbits(n)
    if len(seeds) > 3:
        raise ValueError(f'{n}: {len(seeds)} seeds exceed the current search implementation')
    sizes = [seed[2] for seed in seeds] + [1]*(3-len(seeds))
    N, degree = lcm(*sizes), 2*order2(n)
    if degree >= 63 or N > max_table:
        raise ValueError(f'{n}: degree {degree}, power table {N} exceeds this run limit')
    modulus, d, alpha, factors = field_parameters(degree, N)
    coefficients = [(0, 0, 0)]*n
    for s, (orbit, paired, size) in enumerate(seeds):
        exponent = N//size
        for a in orbit:
            value = [0]*3
            value[s] = exponent
            coefficients[a] = tuple(value)
            if paired:
                value[s] = -exponent % N
                coefficients[-a % n] = tuple(value)
            exponent = 4*exponent % N
    assert all(any(value) for value in coefficients[1:])
    polynomials = []
    pairs = quadratic_representatives(n)
    for g, h in pairs:
        terms = Counter()
        for m in range(n):
            indices = [m, (h-m) % n, (-m-g) % n, (m+g-h) % n]
            # Divide the whole residual by omega^2. A term with two
            # zero indices is an inverse pair, hence a constant; the
            # third coefficient table consequently needs only index 0.
            key = ((2*sum(a != 0 for a in indices)-2) % 3,) + tuple(
                sum(coefficients[a][s] for a in indices) % N for s in range(3))
            assert key[0] != 2 or not any(key[1:])
            terms[key] ^= 1
        terms = [key for key, parity in terms.items() if parity]
        polynomials.append('{'+f'{g},{h},'+'{'+','.join(
            '{'+','.join(map(str, term))+'}' for term in terms)+'}}')
    source = CPP.replace('for(unsigned i=0;i<N;++i)', 'for(unsigned i=0;i<__FIRST__;++i)')
    source = source.replace('for(unsigned k=0;k<3;++k)powers[k].resize(N);',
                            'for(unsigned k=0;k<2;++k)powers[k].resize(N);'
                            'powers[2].resize(1);powers[2][0]=d^1;')
    source = source.replace(''' for(unsigned e=0;e<N;++e){
   powers[1][e]=mul(d,powers[0][e]);
   powers[2][e]=powers[0][e]^powers[1][e];
 }''', ''' for(unsigned j=0;j<bytes;++j)for(unsigned b=0;b<256;++b)
   tab[j][b]=mul(d,U(b)<<(8*j));
 for(unsigned e=0;e<N;++e){
   U x=powers[0][e],y=0;
   for(unsigned j=0;j<bytes;++j)y^=tab[j][(x>>(8*j))&255];
   powers[1][e]=y;
 }''')
    source = source.replace('unsigned a=4*i%N,degree=1;', 'unsigned a=4*i%__FIRST__,degree=1;')
    source = source.replace('a=4*a%N;', 'a=4*a%__FIRST__;')
    source = source.replace('first-phase degree=', 'first-seed degree=')
    replacements = dict(N=N, FIRST=sizes[0], DEGREE=degree, LAST=sizes[2], MIDDLE=sizes[1],
                        MODULUS=modulus, DELTA=d, ALPHA=alpha, FACTORS=','.join(map(str, factors)),
                        POLYS=','.join(polynomials), ORBIT=order2(n))
    for key, value in replacements.items():
        source = source.replace('__'+key+'__', str(value))
    assert '__' not in source
    path, executable = directory / 'general.cpp', directory / 'general_search'
    path.write_text(source)
    subprocess.run(['g++', '-O3', '-std=c++17', str(path), '-o', str(executable)],
                   capture_output=True, text=True, check=True)
    print(f'EXHAUSTIVE n={n}; binary field degree={degree}; seed sizes={sizes}; '
          f'candidates={prod(sizes)}; Q representatives={len(pairs)}', flush=True)
    result = subprocess.run([str(executable)], text=True, capture_output=True, check=True)
    assert 'COMPLETE ' in result.stdout
    winners = {tuple(map(int, values)) for values in re.findall(
        r'Q WINNER (\d+) (\d+) (\d+)', result.stdout)}
    for line in result.stdout.splitlines():
        if not line.startswith(('Q WINNER ', 'TWO-Q CANDIDATE ')):
            print(line, flush=True)
    remaining, reps = set(winners), []
    while remaining:
        first = min(remaining)
        orbit, seed = set(), first
        while seed not in orbit:
            orbit.add(seed)
            seed = tuple(4*i % size for i, size in zip(seed, sizes))
        assert seed == first and orbit <= remaining
        remaining -= orbit
        reps.append((first, len(orbit)))
    return degree, modulus, d, alpha, N, coefficients, reps


def export(n, parameters, output):
    degree, modulus, d, alpha, N, coefficients, reps = parameters

    def mul(a, b):
        value = 0
        while b:
            if b & 1:
                value ^= a
            b >>= 1
            a <<= 1
            if a >> degree:
                a ^= modulus
        return value

    def power(a, b):
        value = 1
        while b:
            if b & 1:
                value = mul(value, a)
            a = mul(a, a)
            b >>= 1
        return value

    bits = lambda a, length=degree: [a >> j & 1 for j in range(length)]
    result = []
    for index, (seed, orbit_length) in enumerate(reps):
        W = [1]+[mul(d ^ 1, power(alpha, sum(a*b for a, b in zip(row, seed)) % N))
                 for row in coefficients[1:]]
        assert all(mul(W[a], W[-a]) == d and power(W[a], 4) == W[2*a % n]
                   for a in range(1, n))
        row = [1, 1]+[mul(mul(W[1], W[a-1]), power(W[a], (1 << degree)-2))
                       for a in range(2, n)]
        data = [n, 2, bits(modulus, degree+1), bits(d), list(map(bits, row))]
        path = output / f'hi_finite_field_{n}_char2_general_{index}.json'
        path.write_text(json.dumps(data)+'\n')
        result.append((path, orbit_length))
    return result


def arithmetic_comparison(n, count):
    source = ('{b=bnfinit(x^2-' + str(n) + '*x-1,1);'
              'if(bnfcertify(b)!=1,error("uncertified class group"));'
              'print([b.disc,b.no,eulerphi(' + str(n) + ')]);}\nquit;\n')
    result = subprocess.run(['gp', '-q', '-f'], input=source, text=True,
                            capture_output=True, check=True)
    if result.stderr:
        raise ArithmeticError(result.stderr)
    discriminant, h, phi = json.loads(result.stdout)
    print(f'ARITHMETIC COMPARISON n={n}: maximal-order discriminant={discriminant}; '
          f'class number={h}; h*phi(n)={h*phi}; canonical count={count}; '
          f'match={count == h*phi}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[15, 17, 19, 21, 25])
    parser.add_argument('--output', type=Path, default=Path('hi_finite_field_certificates'))
    parser.add_argument('--max-table', type=int, default=2000000)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='hi_char2_general_') as temp:
        directory = Path(temp)
        for n in args.orders:
            parameters = search(n, directory, args.max_table)
            paths = export(n, parameters, args.output)
            count = 0
            for path, orbit_length in paths:
                verify(path, directory)
                count += orbit_length
            print(f'COMPLETE PHASE CLASSIFICATION n={n}: canonical points={count}; '
                  f'Frobenius orbits={len(paths)}; total phase points={n*count}', flush=True)
            arithmetic_comparison(n, count)
    print('ALL EXPORTED ORBITS PASSED COMPLETE Q/C; these finite orders do not prove infinitude.')


if __name__ == '__main__':
    main()
