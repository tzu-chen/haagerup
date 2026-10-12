#!/usr/bin/env python3
"""Optional exact check of the printed transvectant reconstruction.

Does not import or run the lattice engine. Reads the saved113-field
tensor and checks all1,442,897 components via charge selection and
the multiplicity-one transvectant formula. Numerical/exact-algebra
validation should be coordinated by root through the permanent launcher.
Expected memory below128MiB; one process, no third-party libraries.
"""
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
import csv
import json
import math

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SRC=ROOT/'c8_physics_20260927'/'full_weight_two'

def falling(a,k):
    return 0 if k<0 or k>a else math.factorial(a)//math.factorial(a-k)

@lru_cache(None)
def K(a,b,c,p,q,r):
    if (a+b-c)%2: return Fraction(0)
    L=(a+b-c)//2
    if not 0<=L<=min(a,b) or r!=p+q-L or not 0<=r<=c:
        return Fraction(0)
    total=sum((-1)**t*math.comb(L,t)*falling(a-p,L-t)*falling(p,t)*falling(b-q,t)*falling(q,L-t) for t in range(L+1))
    return Fraction(falling(a,p)*falling(b,q)*total,falling(c,r))

def product_K(fi,fj,fk):
    value=Fraction(1)
    for axis in range(2):
        value*=K(fi['current_dimensions'][axis]-1,fj['current_dimensions'][axis]-1,fk['current_dimensions'][axis]-1,
                 fi['lowering_powers'][axis],fj['lowering_powers'][axis],fk['lowering_powers'][axis])
    return value

def main():
    basis=json.loads((SRC/'low_weight_basis.json').read_text())['fields']
    norm=[Fraction(f['norm_squared'][0]) for f in basis]
    summary=json.loads((SRC/'complete_primary_couplings.json').read_text())
    tensor={}
    with (SRC/'complete_primary_couplings.tsv').open(newline='') as f:
        for row in csv.DictReader(f,delimiter='\t'):
            key=tuple(int(row[x]) for x in ['i','j','k'])
            tensor[key]=tuple(map(Fraction,json.loads(row['numerator_K4'])))
    representatives={}
    for row in summary['selected_examples']:
        key=tuple(row['indices']);i,j,k=key
        kk=product_K(basis[i],basis[j],basis[k])
        assert kk
        representatives[tuple(row['multiplets'])]=tuple(x/norm[k]/kk for x in tensor[key])
    actual_nonzero=0
    compatible=0
    for i,fi in enumerate(basis):
        for j,fj in enumerate(basis):
            charges=tuple(fi['Cartan_weight'][a]+fj['Cartan_weight'][a] for a in range(2))
            for k,fk in enumerate(basis):
                key=(i,j,k)
                if charges!=tuple(fk['Cartan_weight']):
                    assert key not in tensor
                    continue
                compatible+=1
                rep=representatives.get((fi['multiplet'],fj['multiplet'],fk['multiplet']))
                factor=product_K(fi,fj,fk) if rep else Fraction(0)
                if not factor:
                    assert key not in tensor,('unexpected nonzero',key)
                    continue
                expected=tuple(x*norm[k]*factor for x in rep)
                assert tensor.get(key)==expected,('coefficient mismatch',key)
                actual_nonzero+=1
    assert actual_nonzero==len(tensor)==18365
    print(json.dumps({'status':'PASS','ordered_components_checked':113**3,'charge_compatible_components':compatible,
                      'nonzero_components':actual_nonzero,'nonzero_reduced_maps':len(representatives),
                      'formula':'raw projection = reduced coefficient * left K * right K; normalized by recorded positive norms',
                      'scope':'checks printed reconstruction against saved tensor; does not regenerate lattice products'},indent=2))

if __name__=='__main__':main()
