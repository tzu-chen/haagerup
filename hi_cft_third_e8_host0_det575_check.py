"""Exact determinant575 E8 lattice certificate, standard library only.

Prepared for ROOT's coordinated safe launcher at128MiB. No run by this
author, no numerical libraries, no workers. At most240 roots and streamed
shells through norm8 (17520 vectors); expected live memory below40MiB.
Checks lattice/glue/primitivity and necessary low-grade character bounds.
No VOA action or continuum identification is asserted.
"""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import argparse
import hashlib
import json
import resource

from hi_cft_third_e8_host0_lattice_check import dot, gram, det, add, in_e8, roots_e8

def solve(a,b):
    rows=[[F(x) for x in row]+[F(y)] for row,y in zip(a,b)]
    n=len(rows)
    for j in range(n):
        pivot=next(i for i in range(j,n) if rows[i][j])
        rows[j],rows[pivot]=rows[pivot],rows[j]
        scale=rows[j][j]
        rows[j]=[x/scale for x in rows[j]]
        for i in range(n):
            if i!=j:
                scale=rows[i][j]
                rows[i]=[x-scale*y for x,y in zip(rows[i],rows[j])]
    return [row[-1] for row in rows]

def lincomb(basis,coeff):
    return tuple(sum(c*v[i] for c,v in zip(coeff,basis)) for i in range(8))

def simple_system(roots):
    zero=(F(0),)*8
    positive=sorted(r for r in roots if r>zero)
    lookup=set(positive)
    simple=[r for r in positive if not any(add(r,a,-1) in lookup for a in positive)]
    return positive,simple

def components(simple):
    pending=set(range(len(simple)))
    result=[]
    while pending:
        stack=[pending.pop()]
        found=[]
        while stack:
            i=stack.pop()
            found.append(i)
            adjacent={j for j in pending if dot(simple[i],simple[j])}
            pending-=adjacent
            stack.extend(adjacent)
        result.append(sorted(found))
    return sorted(result,key=len)

def signed_vectors(pattern):
    """Distinct placements of positive magnitudes, with all signs."""
    nonzero=[x for x in pattern if x]
    # The patterns used have at mosttwo nonzero magnitudes.
    magnitudes=sorted(set(nonzero),reverse=True)
    def place(j,available,assigned):
        if j==len(magnitudes):
            positions=sorted(assigned)
            for signs in product((-1,1),repeat=len(positions)):
                vector=[F(0)]*8
                for i,s in zip(positions,signs):
                    vector[i]=s*assigned[i]
                vector=tuple(vector)
                if in_e8(vector):
                    yield vector
            return
        value=magnitudes[j]
        count=nonzero.count(value)
        for chosen in combinations(available,count):
            remaining=tuple(i for i in available if i not in chosen)
            update=dict(assigned)
            update.update((i,value) for i in chosen)
            yield from place(j+1,remaining,update)
    yield from place(0,tuple(range(8)),{})

def shell(norm):
    patterns={
        2:[(F(1),)*2,(F(1,2),)*8],
        4:[(F(2),),(F(1),)*4,(F(3,2),)+(F(1,2),)*7],
        6:[(F(2),)+(F(1),)*2,(F(1),)*6,(F(3,2),)*2+(F(1,2),)*6],
        8:[(F(2),)*2,(F(2),)+(F(1),)*4,(F(1),)*8,
           (F(3,2),)*3+(F(1,2),)*5,(F(5,2),)+(F(1,2),)*7],
    }
    for pattern in patterns[norm]:
        yield from signed_vectors(pattern)

def colored_partitions(colors,degree):
    out=[1]+[0]*degree
    for mode in range(1,degree+1):
        for _ in range(colors):
            for n in range(mode,degree+1):
                out[n]+=out[n-mode]
    return out

def main(output):
    source=Path(__file__).read_bytes()
    h=tuple(map(F,(2,0,1,1,0,0,0,0)))
    roots=list(roots_e8())
    perpendicular=[a for a in roots if dot(h,a)==0]
    fixed=[a for a in roots if dot(h,a).denominator==1 and int(dot(h,a))%3==0]
    positive,simple=simple_system(perpendicular)
    comps=components(simple)
    a1=[simple[i] for i in comps[0]]
    e6=[simple[i] for i in comps[1]]
    positive_e6=[a for a in positive if dot(a,a1[0])==0]
    rho_e6=lincomb(positive_e6,[F(1,2)]*len(positive_e6))
    rho_a1=tuple(x/2 for x in a1[0])
    cartan=gram(e6)
    candidates=[]
    minuscule=[]
    for i in range(6):
        fundamental=lincomb(e6,solve(cartan,[int(j==i) for j in range(6)]))
        if dot(fundamental,fundamental)==F(4,3):
            minuscule.append(fundamental)
            r=add(add(rho_e6,rho_a1),fundamental)
            k=add(r,h,F(1,6))
            if in_e8(k):
                candidates.append((k,r,fundamental,i))
    assert candidates, "No actual E8 glue orientation found"
    k,r,omega,chosen=candidates[0]
    lb=(h,tuple(3*x for x in k))
    rootless=[a for a in roots if dot(a,h)==0 and dot(a,k)==0]
    alpha=next(a for a in simple if dot(h,a)==0 and dot(k,a)==1)
    beta=next(a for a in roots if dot(h,a)==1)
    unit_minor=dot(h,beta)*dot(k,alpha)-dot(h,alpha)*dot(k,beta)
    dual_h=add(beta,alpha,-dot(k,beta))
    _,e8_basis=simple_system(roots)
    generators=[add(add(x,dual_h,-dot(h,x)),alpha,-dot(k,x)) for x in e8_basis]
    basis=None
    for indices in combinations(range(8),6):
        subset=[generators[i] for i in indices]
        if det(gram(subset))==575:
            basis=subset
            break
    fixed_positive,fixed_simple=simple_system(fixed)
    fixed_components=components(fixed_simple)
    checks={
        "E8_240_roots":len(roots)==240,
        "h_norm6":dot(h,h)==6,
        "h_perpendicular_74_roots":len(perpendicular)==74,
        "h_perpendicular_E6_A1_components":sorted(map(len,comps))==[1,6],
        "h_perpendicular_root_lattice_det6":det(gram(simple))==6,
        "E6_72_roots":len(positive_e6)==36,
        "E6_Cartan_det3":det(cartan)==3,
        "rho_E6_norm78":dot(rho_e6,rho_e6)==78,
        "rho_A1_norm_half":dot(rho_a1,rho_a1)==F(1,2),
        "two_minuscule_weights":len(minuscule)==2,
        "rho_omega_pairing8":dot(rho_e6,omega)==8,
        "projection_norm575_over6":dot(r,r)==F(575,6),
        "actual_k_in_E8":in_e8(k),
        "L_Gram_6_1_96":gram((h,k))==[[6,1],[1,96]],
        "L_determinant575":det(gram((h,k)))==575,
        "primitive_unit_pairing_minor":unit_minor==1,
        "K_rootless":len(rootless)==0,
        "K_generators_integral":all(in_e8(x) for x in generators),
        "K_generators_orthogonal":all(dot(x,h)==dot(x,k)==0 for x in generators),
        "alpha_fixed_78_roots":len(fixed)==78,
        "alpha_fixed_E6_A2_components":sorted(map(len,fixed_components))==[2,6],
        "alpha_fixed_lattice_det9":det(gram(fixed_simple))==9,
        "alpha_nontrivial_on_L":int(dot(h,k))%3!=0,
        "LB_Gram_6_3_864":gram(lb)==[[6,3],[3,864]],
        "LB_det5175":det(gram(lb))==9*575,
        "LB_basis_alpha_fixed":all(int(dot(h,x))%3==0 for x in lb),
        "K_regular_projection":all(dot(r,a)>0 for a in positive),
        "E8_simple_Gram_det1":det(gram(e8_basis))==1,
    }
    assert all(checks.values()), checks
    counts={}
    full_expected={2:240,4:2160,6:6720,8:17520}
    kept={}
    for norm in (2,4,6,8):
        total=0
        selected=[]
        for x in shell(norm):
            assert dot(x,x)==norm
            total+=1
            if dot(x,h)==0 and dot(x,k)==0:
                selected.append(x)
        assert total==full_expected[norm], (norm,total)
        counts[str(norm)]={"E8_count":total,"K_count":len(selected)}
        kept[norm]=selected
    assert len(kept[2])==0
    oscillator=colored_partitions(6,4)
    theta=[1]+[len(kept[2*j]) for j in range(1,5)]
    vacuum=[sum(theta[j]*oscillator[n-j] for j in range(n+1)) for n in range(5)]
    # c=2 Virasoro vacuum, through grade4: 1,0,1,1,2.
    vir=[1,0,1,1,2]
    lower=[sum(vacuum[j]*vir[n-j] for j in range(n+1)) for n in range(5)]
    bounds={
        "Gamma0_W_grade2":120,
        "Gamma0_W_grade3":956,
        "K_VOA_grade2_pass":vacuum[2]<=120,
        "K_VOA_grade3_pass":vacuum[3]<=956,
        "K_times_Vir2_grade2_pass":lower[2]<=120,
        "K_times_Vir2_grade3_pass":lower[3]<=956,
        "scope":"Necessary character lower bounds only; no actual D0/W construction.",
    }
    def encode(x):
        if isinstance(x,F):
            return int(x) if x.denominator==1 else str(x)
        raise TypeError(type(x).__name__)
    result={
        "status":"Exact certificate; no VOA action or continuum identification",
        "source_sha256":hashlib.sha256(source).hexdigest(),
        "checks":checks,
        "h":h,"k":k,"regular_projection":r,
        "E6_simple_roots":e6,"A1_simple_root":a1[0],
        "E6_rho":rho_e6,"minuscule_omega":omega,"chosen_simple_index":chosen,
        "primitive_pairing_witness":{"alpha":alpha,"beta":beta,"minor":unit_minor},
        "L_Gram":gram((h,k)),"LB_Gram":gram(lb),
        "K_generators":generators,"K_basis":basis,
        "K_Gram":gram(basis) if basis else None,
        "shell_counts":counts,
        "K_VOA_vacuum_coefficients_0_to_4":vacuum,
        "K_times_Vir2_coefficients_0_to_4":lower,
        "character_bounds":bounds,
        "K_norm4_vectors":kept[4],
        "peak_RSS_KiB":resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    }
    Path(output).write_text(json.dumps(result,default=encode,indent=2)+"\n")
    print(json.dumps({"checks":checks,"shell_counts":counts,"K_vacuum":vacuum,
                      "K_times_Vir2":lower,"character_bounds":bounds}))
if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",default="hi_cft_third_e8_host0_det575_results.json")
    args=parser.parse_args()
    main(args.output)

