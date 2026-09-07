"""Exact Frobenius-covariant phase searches at n = 3, 9, 27.

Section 58 explains why complete finite-field cubic certificates suffice
for complex categorification. This search itself filters only quadratics;
each Frobenius-orbit representative then goes through the independent
all-quadratic/all-cubic verifier hi_finite_field_certificate.py.

No characteristic-zero HI or Stark data are used. The search is exhaustive
inside the explicitly specified Frobenius ansatz, not among all HI matrices.
Section 71 subsequently proves that this gauge represents every full
characteristic-two solution in the phase parametrization uniquely modulo
character gauge. Thus the completed searches classify those phase solutions.
Requirements: Python standard library, PARI/GP, and a C++17 compiler.
"""

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
import tempfile

from hi_finite_field_certificate import verify


CPP = r'''
#include <array>
#include <cstdint>
#include <cstdio>
#include <vector>
using U=uint64_t;
constexpr unsigned N=__N__, degree=__DEGREE__, last_order=__LAST__;
constexpr U modulus=__MODULUS__ULL, d=__DELTA__ULL, alpha=__ALPHA__ULL;
U mul(U a,U b){
 U r=0;
 while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&(1ULL<<degree))a^=modulus;}
 return r;
}
U powr(U a,U b){U r=1;while(b){if(b&1)r=mul(r,a);a=mul(a,a);b>>=1;}return r;}
struct Term {unsigned k,a,b,c;};
struct Poly {int g,h;std::vector<Term> terms;};
std::vector<Poly> polys={__POLYS__};
std::array<std::vector<U>,3> powers;
int main(){
 if(powr(alpha,N)!=1 || mul(d,d)!=(d^1) || d==1)return 2;
 for(auto p: {__FACTORS__})if(powr(alpha,N/p)==1)return 3;
 constexpr unsigned bytes=(degree+7)/8;
 std::array<std::array<U,256>,bytes> tab;
 for(unsigned j=0;j<bytes;++j)for(unsigned b=0;b<256;++b)
   tab[j][b]=mul(alpha,U(b)<<(8*j));
 for(unsigned k=0;k<3;++k)powers[k].resize(N);
 powers[0][0]=1;
 for(unsigned e=1;e<N;++e){
   U x=powers[0][e-1],y=0;
   for(unsigned j=0;j<bytes;++j)y^=tab[j][(x>>(8*j))&255];
   powers[0][e]=y;
 }
 for(unsigned e=0;e<N;++e){
   powers[1][e]=mul(d,powers[0][e]);
   powers[2][e]=powers[0][e]^powers[1][e];
 }
 unsigned total=0,first=0,two=0,two_primitive=0;
 std::vector<unsigned> failures(polys.size()),two_degrees(__ORBIT__+1);
 for(unsigned j=0;j<__MIDDLE__;++j)for(unsigned k=0;k<last_order;++k){
   const auto &terms=polys[0].terms;
   std::vector<unsigned> exponents;
   for(const auto &v:terms)exponents.push_back((v.b*j+v.c*k)%N);
   for(unsigned i=0;i<N;++i){
     U r=0;
     for(unsigned z=0;z<terms.size();++z){
       const auto &v=terms[z];
       r^=powers[v.k][exponents[z]];
       exponents[z]+=v.a;if(exponents[z]>=N)exponents[z]-=N;
     }
     if(r)continue;
     ++first;
     bool ok=true;
     for(unsigned p=1;p<polys.size();++p){
       U r=0;
       for(const auto &v:polys[p].terms)
         r^=powers[v.k][(U(v.a)*i+v.b*j+v.c*k)%N];
       if(r){++failures[p];ok=false;break;}
       if(p==1){
         ++two;
         printf("TWO-Q CANDIDATE %u %u %u\n",i,j,k);
         unsigned a=4*i%N,degree=1;
         while(a!=i){a=4*a%N;++degree;}
         if(degree>__ORBIT__)return 4;
         ++two_degrees[degree];
         if(degree==__ORBIT__)++two_primitive;
       }
     }
     if(ok){++total;printf("Q WINNER %u %u %u\n",i,j,k);}
   }
 }
 for(unsigned p=1;p<failures.size();++p)if(failures[p])
   printf("FILTER F(%d,%d) rejects=%u\n",polys[p].g,polys[p].h,failures[p]);
 for(unsigned e=1;e<two_degrees.size();++e)if(two_degrees[e])
   printf("TWO-Q first-phase degree=%u count=%u\n",e,two_degrees[e]);
 printf("TWO QUADRATICS total=%u primitive=%u\n",two,two_primitive);
 printf("COMPLETE allQ=%u firstQ=%u\n",total,first);
}
'''


def field_parameters(n):
    degree = 4*n//3
    source = r'''
export_field()={
my(f=ffinit(2,DEG,'z),z=ffgen(f),g=ffprimroot(z),N=2^(DEG/2)+1,
 d=g^((2^DEG-1)/3),u=g^((2^DEG-1)/N));
print([sum(j=0,DEG,lift(polcoef(f,j))*2^j),
 sum(j=0,DEG-1,lift(polcoef(d.pol,j))*2^j),
 sum(j=0,DEG-1,lift(polcoef(u.pol,j))*2^j),Vec(factor(N)[,1])]);
};
iferr(export_field(),e,print(e);quit(1));quit;
'''.replace('DEG', str(degree))
    result = subprocess.run(['gp', '-q', '-f'], input=source, text=True,
                            capture_output=True, check=True)
    return degree, json.loads(result.stdout)


def search(n, directory, two_candidates=None):
    k = {3: 1, 9: 2, 27: 3}[n]
    degree, (modulus, d, alpha, factors) = field_parameters(n)
    orders = [4**(3**(k-s-1))+1 for s in range(k)]
    orders += [1]*(3-k)
    N = orders[0]
    coefficients = [(0, 0, 0)]*n
    for s in range(k):
        a, c = 3**s, N//orders[s]
        for _ in range(2*3**(k-s-1)):
            v = [0]*3
            v[s] = c
            coefficients[a] = tuple(v)
            a, c = 2*a % n, 4*c % N
    assert all(any(v) for v in coefficients[1:])
    polynomials = []
    for s in range(k):
        h = 3**s
        for g in range(1, n):
            terms = Counter()
            for m in range(n):
                indices = [m, (h-m) % n, (-m-g) % n, (m+g-h) % n]
                key = (2*sum(a != 0 for a in indices) % 3,) + tuple(
                    sum(coefficients[a][s] for a in indices) % N for s in range(3))
                terms[key] ^= 1
            terms = [key for key, value in terms.items() if value]
            polynomials.append('{'+f'{g},{h},'+'{'+','.join(
                '{'+','.join(map(str, term))+'}' for term in terms)+'}}')
    replacements = {'N': N, 'DEGREE': degree, 'LAST': orders[2],
                    'MIDDLE': orders[1], 'MODULUS': modulus,
                    'DELTA': d, 'ALPHA': alpha,
                    'FACTORS': ','.join(map(str, factors)),
                    'POLYS': ','.join(polynomials), 'ORBIT': 2*n//3}
    source = CPP
    for name, value in replacements.items():
        source = source.replace('__'+name+'__', str(value))
    path, executable = directory / 'search.cpp', directory / 'search'
    path.write_text(source)
    subprocess.run(['g++', '-O3', '-std=c++17', str(path), '-o', str(executable)],
                   check=True, capture_output=True, text=True)
    result = subprocess.run([str(executable)], capture_output=True, text=True, check=True)
    winners = {tuple(map(int, value)) for value in re.findall(
        r'Q WINNER (\d+) (\d+) (\d+)', result.stdout)}
    assert 'COMPLETE ' in result.stdout
    # This is a finite implication established by the exhaustive searches
    # at these three orders. It is not asserted uniformly in n.
    two, primitive = map(int, re.search(
        r'TWO QUADRATICS total=(\d+) primitive=(\d+)', result.stdout).groups())
    partial = {tuple(map(int, value)) for value in re.findall(
        r'TWO-Q CANDIDATE (\d+) (\d+) (\d+)', result.stdout)}
    assert len(partial) == two and winners <= partial
    if two_candidates is not None:
        two_candidates.extend(sorted(partial))
    assert primitive == len(winners)
    for seed in winners:
        value, phase_degree = 4*seed[0] % N, 1
        while value != seed[0]:
            value, phase_degree = 4*value % N, phase_degree+1
        assert phase_degree == 2*n//3
    print(f'n={n}; field degree={degree}; norm-torus orders={orders[:k]}; '
          f'candidates={orders[0]*orders[1]*orders[2]}', flush=True)
    for line in result.stdout.splitlines():
        if not line.startswith(('Q WINNER ', 'TWO-Q CANDIDATE ')):
            print(line, flush=True)
    remaining, representatives = set(winners), []
    while remaining:
        seed = min(remaining)
        orbit, value = set(), seed
        while value not in orbit:
            orbit.add(value)
            value = tuple(4*i % q for i, q in zip(value, orders))
        assert orbit <= remaining
        remaining -= orbit
        representatives.append(seed)
        print(f'Frobenius representative {seed[:k]}; orbit length={len(orbit)}', flush=True)
    if not representatives:
        raise ArithmeticError('No complete-quadratic candidates in this ansatz')
    return degree, modulus, d, alpha, orders, representatives


def export_certificates(n, parameters, output):
    degree, modulus, d, alpha, orders, representatives = parameters
    k = {3: 1, 9: 2, 27: 3}[n]
    N = orders[0]

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

    coefficients = lambda a: [(a >> j) & 1 for j in range(degree)]
    paths = []
    for index, seed in enumerate(representatives):
        w = [1]*n
        for s in range(k):
            a, value = 3**s, mul(d ^ 1, power(alpha, N//orders[s]*seed[s]))
            for _ in range(2*3**(k-s-1)):
                w[a] = value
                a, value = 2*a % n, power(value, 4)
        assert all(mul(w[a], w[-a]) == d for a in range(1, n))
        row = [1, 1] + [mul(mul(w[1], w[a-1]), power(w[a], (1 << degree)-2))
                        for a in range(2, n)]
        data = [n, 2, [(modulus >> j) & 1 for j in range(degree+1)],
                coefficients(d), list(map(coefficients, row))]
        path = output / f'hi_finite_field_{n}_char2_{index}.json'
        path.write_text(json.dumps(data)+'\n')
        paths.append(path)
    return paths


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', choices=[3, 9, 27], default=[3, 9, 27])
    parser.add_argument('--output', type=Path, default=Path('hi_finite_field_certificates'))
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='hi_char2_frobenius_') as temp:
        directory = Path(temp)
        for n in args.orders:
            parameters = search(n, directory)
            for path in export_certificates(n, parameters, args.output):
                verify(path, directory)
    print('ALL FROBENIUS-ORBIT REPRESENTATIVES PASSED COMPLETE INDEPENDENT CERTIFICATION')


if __name__ == '__main__':
    main()
