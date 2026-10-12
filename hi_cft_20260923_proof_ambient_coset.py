"""A rational conformal frame in the ambient commutant of T.

The finite-index lattice need not be primitive for this certificate.
This proves an ambient rationality statement, not rationality of U.
"""
import json,resource,signal,hashlib
from pathlib import Path
from fractions import Fraction as Q
import sympy as sp
import hi_cft_20260923_c8_exact as x
from hi_cft_20260923_proof_potts import exact_axis,ALPHA,BETA,s2
from hi_cft_20260923_proof_potts_exact import serialize

def stress(basis):
    G=[[x.dot(a,b) for b in basis] for a in basis];inverse=x.inverse(G)
    return x.vadd(*[(Q(inverse[i][j],2),x.mode(x.cartan(a),-1,x.cartan(b))) for i,a in enumerate(basis) for j,b in enumerate(basis)])

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(180)
    p=exact_axis();a=(0,0,0,0,0,-1,1,1);t=tuple(3*a[i]+2*ALPHA[i]+BETA[i] for i in range(8))
    R=[x.A0,t,ALPHA,BETA];constraints=sp.Matrix(R)*sp.Matrix(x.G)
    complement=[]
    for v in constraints.nullspace():
        den=sp.ilcm(*[z.q for z in v]);complement.append(tuple(int(den*z) for z in v))
    assert len(complement)==4 and all(x.dot(a,b)==0 for a in R for b in complement)
    full=sp.Matrix(R+complement);index=abs(int(full.det()));assert index>0
    q=x.vadd((Q(1,16),x.mode(x.cartan(ALPHA),-1,x.cartan(ALPHA))),
             (-Q(5,4),{(a,()):p[a,()] for a in (ALPHA,tuple(-z for z in ALPHA))}))
    r=x.vadd((1,stress([ALPHA,BETA])),(-1,p),(-1,q))
    for v,c in ((p,Q(4,5)),(q,Q(1,2)),(r,Q(7,10))):
        assert not x.vadd((1,x.mode(v,1,v)),(-2,v))
        assert x.mode(v,3,v)=={(x.ZERO,()):x.A(c/2)}
    for u,v in ((p,q),(p,r),(q,r)):
        for n in (1,2,3):assert not x.mode(u,n,v)
    lattice_stress=stress([x.A0,t]);other=stress(complement)
    assert not x.vadd((1,lattice_stress),(1,p),(1,q),(1,r),(1,other),(-1,x.omega()))
    S=s2();q_in=not S.reduce(q);r_in=not S.reduce(r)
    out={'ambient_central_charge':8,'rational_core_central_charge':'14/5',
         'ambient_commutant_central_charge':'26/5',
         'commutant_conformal_subalgebra':'V_M tensor L(1/2,0) tensor L(7/10,0)',
         'rank_four_lattice_basis':complement,'rank_four_lattice_Gram':[[x.dot(a,b) for b in complement] for a in complement],
         'index_of_L_plus_sqrt2A2_plus_M_in_E6A2':index,
         'exact_commuting_Virasoro_and_total_stress_checks':True,
         'Ising_stress_in_S2':q_in,'tricritical_stress_in_S2':r_in,
         'Ising_stress':serialize(q),'tricritical_stress':serialize(r),
         'scope':'The ambient commutant Com(T,B) is a finite conformal extension of the displayed strongly rational frame. This does not imply Com(T,U) or U is rational.',
         'source_sha256':{str(z):hashlib.sha256(z.read_bytes()).hexdigest() for z in (Path(__file__),Path(x.__file__))}}
    path=Path('hi_cft_20260923_proof_ambient_coset.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ('Ising_stress','tricritical_stress')},flush=True)

if __name__=='__main__':main()
