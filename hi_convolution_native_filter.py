"""Native exhaustive first-norm-obstruction search, followed by exact lifting.

Use the existing cyclic norm/Frobenius parametrization, but filter by
Section 99's quartics instead of Q. Recheck accepted Frobenius orbits
independently, then classify their norm lifts and all residue Q.
No uniform completion claim follows from a finite census.
"""

import argparse
from collections import Counter
import json
from math import lcm, prod
from pathlib import Path
import random
import resource
import subprocess
import tempfile
import time

from hi_char2_general_search import field_parameters, order2, seed_orbits
from hi_convolution_hensel import UnramifiedRing, lift_convolution
from hi_convolution_norm_obstruction import first_obstructions, residue_q


CPP = r'''
#include <array>
#include <cstdint>
#include <cstdio>
#include <vector>
using U=uint64_t;
constexpr unsigned degree=__DEG__, N=__N__, n0=__N0__, n1=__N1__, n2=__N2__;
constexpr U modulus=__MOD__ULL, delta=__DELTA__ULL, alpha=__ALPHA__ULL;
U mul(U a,U b){U r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a>>degree)a^=modulus;}return r;}
U power(U a,U b){U r=1;while(b){if(b&1)r=mul(r,a);a=mul(a,a);b>>=1;}return r;}
struct Term{unsigned k,a,b,c;};
std::vector<std::vector<Term>> polys={__POLYS__};
std::array<std::vector<U>,3> table;
int main(){
 if(power(alpha,N)!=1 || mul(delta,delta)!=(delta^1) || delta==1)return 2;
 for(auto p:{__FACTORS__})if(power(alpha,N/p)==1)return 3;
 for(auto& t:table)t.resize(N);
 table[0][0]=1;
 for(unsigned i=1;i<N;++i)table[0][i]=mul(table[0][i-1],alpha);
 for(unsigned i=0;i<N;++i){table[1][i]=mul(delta,table[0][i]);table[2][i]=table[0][i]^table[1][i];}
 U first=0,accepted=0;
 for(unsigned j=0;j<n1;++j)for(unsigned k=0;k<n2;++k){
  std::vector<unsigned> exponents;
  for(const auto& v:polys[0])exponents.push_back((U(v.b)*j+U(v.c)*k)%N);
  for(unsigned i=0;i<n0;++i){
   U residual=0;
   for(unsigned z=0;z<polys[0].size();++z){const auto& v=polys[0][z];
    residual^=table[v.k][exponents[z]];exponents[z]+=v.a;if(exponents[z]>=N)exponents[z]-=N;
   }
   if(residual)continue;
   ++first;bool ok=true;
   for(unsigned p=1;p<polys.size();++p){U q=0;
    for(const auto& v:polys[p])q^=table[v.k][(U(v.a)*i+U(v.b)*j+U(v.c)*k)%N];
    if(q){ok=false;break;}
   }
   if(ok){++accepted;std::printf("WIN %u %u %u\n",i,j,k);}
  }
 }
 std::printf("NATIVE_COMPLETE first=%llu accepted=%llu\n",(unsigned long long)first,(unsigned long long)accepted);
}
'''


def parameters(n, bits):
    orbits = seed_orbits(n)
    sizes = [s for _, _, s in orbits]
    if len(sizes) > 3 or max(sizes) > 300000 or 2*order2(n) >= 63:
        raise ValueError('This bounded native census exceeds its size or field limit')
    N = lcm(*sizes)
    if N > 300000 or prod(sizes) > 100000000:
        raise ValueError('This bounded native census exceeds its table or enumeration limit')
    degree = 2*order2(n)
    modulus, delta, alpha, factors = field_parameters(degree, N)
    ring = UnramifiedRing([(modulus >> i) & 1 for i in range(degree+1)], bits)
    coefficients = [(0, 0, 0)]*n
    for s, (orbit, paired, size) in enumerate(orbits):
        exponent = N//size
        for a in orbit:
            row = [0, 0, 0]
            row[s] = exponent
            coefficients[a] = tuple(row)
            if paired:
                row[s] = -exponent % N
                coefficients[-a % n] = tuple(row)
            exponent = 4*exponent % N
    polynomials = []
    for orbit, _, _ in orbits:
        r = orbit[0]
        terms = Counter({(2, 0, 0, 0): 1})
        if ((n-1)//2) % 2:
            terms[1, 0, 0, 0] ^= 1
        for repeated in (r, -r % n):
            target = -2*repeated % n
            for a in range(n):
                b = (target-a) % n
                if a >= b:
                    continue
                indices = [repeated, repeated, a, b]
                key = ((2+2*sum(a != 0 for a in indices)) % 3,) + tuple(
                    sum(coefficients[a][s] for a in indices) % N for s in range(3))
                terms[key] ^= 1
        polynomials.append([key for key, parity in sorted(terms.items()) if parity])
    return ring, delta, alpha, N, factors, coefficients, sizes+[1]*(3-len(sizes)), polynomials


def phases_from_seed(ring, delta, alpha, N, coefficients, seed):
    return [1]+[ring.ff_mul(delta ^ 1, ring.ff_pow(alpha, sum(a*b for a, b in zip(row, seed)) % N))
                for row in coefficients[1:]]


def run(n, bits, timeout, directory):
    ring, delta, alpha, N, factors, coefficients, sizes, polynomials = parameters(n, bits)
    # Compare compiled polynomials with the separate unordered-pair formula,
    # including rejected inputs rather than only final solutions.
    rng = random.Random(9900+n)
    for _ in range(32):
        seed = tuple(rng.randrange(size) for size in sizes)
        phases = phases_from_seed(ring, delta, alpha, N, coefficients, seed)
        values = []
        for terms in polynomials:
            value = 0
            for k, *exponents in terms:
                value ^= ring.ff_mul(ring.ff_pow(delta, k), ring.ff_pow(alpha,
                    sum(a*b for a, b in zip(exponents, seed)) % N))
            values.append(value)
        assert values == first_obstructions(n, ring, delta, phases)
    replacements = dict(DEG=ring.degree, N=N, N0=sizes[0], N1=sizes[1], N2=sizes[2],
                        MOD=ring.modulus, DELTA=delta, ALPHA=alpha,
                        FACTORS=','.join(map(str, factors)),
                        POLYS=','.join('{'+','.join('{'+','.join(map(str, term))+'}'
                            for term in terms)+'}' for terms in polynomials))
    source = CPP
    for key, value in replacements.items():
        source = source.replace('__'+key+'__', str(value))
    assert '__' not in source
    cpp, executable = directory / f'n{n}.cpp', directory / f'n{n}'
    cpp.write_text(source)
    subprocess.run(['g++', '-O3', '-std=c++17', str(cpp), '-o', str(executable)], check=True)
    print(f'START n={n}; candidates={prod(sizes)}; term_counts={list(map(len,polynomials))}; '
          f'table_MiB={3*N*8/1024**2:.2f}; field_degree={ring.degree}', flush=True)
    completed = subprocess.run([str(executable)], capture_output=True, text=True,
                               check=True, timeout=timeout)
    assert 'NATIVE_COMPLETE' in completed.stdout
    winners = {tuple(map(int, line.split()[1:])) for line in completed.stdout.splitlines()
               if line.startswith('WIN ')}
    print(completed.stdout.splitlines()[-1], flush=True)
    remaining, census, records = set(winners), Counter(), []
    while remaining:
        seed = min(remaining)
        orbit, point = set(), seed
        while point not in orbit:
            orbit.add(point)
            point = tuple(4*a % size for a, size in zip(point, sizes))
        assert point == seed and orbit <= remaining
        remaining -= orbit
        phases = phases_from_seed(ring, delta, alpha, N, coefficients, seed)
        assert all(ring.ff_mul(phases[a], phases[-a]) == delta and
                   ring.ff_pow(phases[a], 4) == phases[2*a % n] for a in range(1,n))
        assert not any(first_obstructions(n, ring, delta, phases))
        q, first_q = residue_q(n, ring, delta, phases)
        lifted_delta, lifted, _ = lift_convolution(ring, n, delta, phases)
        origin = ring.valuation(ring.add(lifted[0], ring.one))
        norm = min(ring.valuation(ring.sub(ring.mul(lifted[a], lifted[-a]), lifted_delta))
                   for a in range(1,n))
        assert norm >= 2 and origin >= min(bits, norm+1)
        census[q, origin, norm] += len(orbit)
        records.append(dict(seed=seed, orbit_length=len(orbit), phases=phases,
                            q=q, first_q=first_q, origin_valuation=origin, norm_valuation=norm))
        print(f'  ORBIT seed={seed}; length={len(orbit)}; Q={q}; origin_v={origin}; norm_v={norm}', flush=True)
    assert sum(census.values()) == len(winners)
    output = dict(n=n, modulus=ring.modulus, delta=delta, alpha=alpha, N=N,
                  sizes=sizes, coefficients=coefficients, bits=bits, records=records)
    Path(f'hi_convolution_native_{n}_certificates.json').write_text(json.dumps(output, indent=2)+'\n')
    print(f'COMPLETE n={n}; allO={len(winners)}; Q_among_O={sum(v for (q,_,_),v in census.items() if q)}; '
          f'norms_mod8={sum(v for (_,o,s),v in census.items() if min(o,s)>=3)}', flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[3, 5, 7, 9, 15, 27])
    parser.add_argument('--bits', type=int, default=4)
    parser.add_argument('--timeout', type=float, default=120)
    args = parser.parse_args()
    if not 3 <= args.bits <= 12:
        raise ValueError('Use 3..12 binary digits for this bounded comparison')
    start = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='hi_convolution_native_') as directory:
        for n in args.orders:
            run(n, args.bits, args.timeout, Path(directory))
    print(f'elapsed_seconds={time.monotonic()-start:.3f}', flush=True)
    print(f'parent_peak_RSS_MiB={resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024:.2f}', flush=True)
    print(f'child_peak_RSS_MiB={resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss/1024:.2f}', flush=True)
    print('COMPLETE: native norm-obstruction census; no uniform completion theorem claimed.')


if __name__ == '__main__':
    main()
