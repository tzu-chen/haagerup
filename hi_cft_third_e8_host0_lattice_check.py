"""Exact primitive E8/host0 candidate certificate; no numerical libraries.

This is a small standard-library check intended for a ROOT-coordinated
128 MiB safe launcher. It creates no processes, workers, or large arrays.
The candidate is categorical; no VOA action or chain identification is
asserted. This source has not been run by its author.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import argparse
import json

def dot(x,y):
    return sum(a*b for a,b in zip(x,y))

def gram(basis):
    return [[dot(x,y) for y in basis] for x in basis]

def det(a):
    a=[[F(x) for x in row] for row in a]
    out=F(1)
    for i in range(len(a)):
        p=next((j for j in range(i,len(a)) if a[j][i]),None)
        if p is None:
            return F(0)
        if p!=i:
            a[i],a[p]=a[p],a[i]
            out=-out
        v=a[i][i]
        out*=v
        for j in range(i+1,len(a)):
            scale=a[j][i]/v
            for k in range(i+1,len(a)):
                a[j][k]-=scale*a[i][k]
    return out

def add(x,y,a=1):
    return tuple(u+a*v for u,v in zip(x,y))

def in_e8(x):
    twice=[2*t for t in x]
    if any(t.denominator!=1 for t in twice):
        return False
    parity={int(t)%2 for t in twice}
    return len(parity)==1 and sum(x).denominator==1 and int(sum(x))%2==0

def b_class(x):
    value=x[0]+x[1]+x[2]-3*x[7]
    assert value.denominator==1
    return int(value)%3

def roots_e8():
    for i,j in combinations(range(8),2):
        for s,t in product((-1,1),repeat=2):
            x=[F(0)]*8
            x[i],x[j]=F(s),F(t)
            yield tuple(x)
    for signs in product((-1,1),repeat=8):
        x=tuple(F(s,2) for s in signs)
        if in_e8(x):
            yield x

def main(output):
    v=tuple(map(F,(0,0,0,2,1,1,0,0)))
    w=tuple(map(F,(2,2,2,0,0,0,0,0)))
    K=[tuple(map(F,x)) for x in (
        (1,-1,0,0,0,0,0,0),
        (0,1,-1,0,0,0,0,0),
        (0,0,0,1,0,-2,1,0),
        (0,0,0,0,1,-1,0,0),
        (0,0,0,0,0,0,1,1),
        (0,0,0,0,0,0,1,-1))]
    q=lambda x: int(x[1]+2*x[2]+x[4]+x[6])%3
    M=[add(K[0],K[3]),add(K[1],K[3]),add(K[2],K[3],-1),
       tuple(3*x for x in K[3]),add(K[4],K[3],-1),add(K[5],K[3],-1)]
    roots=list(roots_e8())
    Kr=[r for r in roots if dot(r,v)==0 and dot(r,w)==0]
    Mr=[r for r in Kr if q(r)==0]
    all_basis=[v,w]+K
    checks={
        "E8_root_count_240":len(roots)==240,
        "L_Gram_diag6_12":gram([v,w])==[[6,0],[0,12]],
        "L_basis_in_E8_and_B":all(in_e8(x) and b_class(x)==0 for x in (v,w)),
        "K_basis_in_E8_and_B":all(in_e8(x) and b_class(x)==0 for x in K),
        "K_L_orthogonal":all(dot(x,y)==0 for x in K for y in (v,w)),
        "K_determinant72":det(gram(K))==72,
        "full_rank_lattice_index72":det(gram(all_basis))==72**2,
        "K_roots12":len(Kr)==12,
        "M_basis_in_E8_and_B":all(in_e8(x) and b_class(x)==0 for x in M),
        "M_basis_in_kernel":all(q(x)==0 for x in M),
        "character_surjective":q(K[3])==1,
        "M_determinant648":det(gram(M))==648,
        "M_index3":det(gram(M))==9*det(gram(K)),
        "M_rootless":len(Mr)==0,
        "three_primary_quadratic_form":dot(v,v)/18==F(1,3) and dot(w,w)/18==F(2,3),
    }
    assert all(checks.values()), checks
    # The primitivity proof is recorded separately because it is simpler
    # than an E8 integral-coordinate Smith computation:
    # zeros in coordinates7,8 exclude half-integral E8 vectors in spanL;
    # coordinates5,6 force coefficient(v) integral; coefficients(w) may
    # be half-integral, but E8 even total sum forces them integral.
    result={
        "scope":"Exact lattice/category consistency only; no VOA action or continuum identification.",
        "checks":checks,
        "L_basis":[list(x) for x in (v,w)],
        "K_basis":[list(x) for x in K],
        "M_basis":[list(x) for x in M],
        "K_Gram":gram(K),"M_Gram":gram(M),
        "K_roots":[list(x) for x in Kr],
        "root_character_values":[q(x) for x in Kr],
        "L_discriminant_group":"C6 x C12",
        "three_primary_metric":"q(a,b)=(a^2+2b^2)/3 mod1; hyperbolic",
        "two_primary_metric":"C2 x C4, q generators3/4 and3/8",
        "K_root_system":"A2 + A1^3",
        "M_character":"x2+2*x3+x5+x7 mod3",
        "primitivity_proof":"Coordinate integrality plus E8 even-sum parity; see source comment and companion note.",
        "conditional_indices":{"E8_over_B":"3","B_over_K_times_L":"24",
            "K_over_M":"3","E8_over_M_times_D0":"216 I","W_over_M_times_D0":"72"},
    }
    def encode(x):
        if isinstance(x,F):
            return int(x) if x.denominator==1 else str(x)
        raise TypeError(type(x).__name__)
    Path(output).write_text(json.dumps(result,default=encode,indent=2)+"\n")
    print(json.dumps(checks))
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--output",default="hi_cft_third_e8_host0_lattice_results.json")
    a=p.parse_args()
    main(a.output)

