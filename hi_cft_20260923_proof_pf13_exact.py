"""Recognize and certify the c=8/5 stress and its weight-three primary.

Floating reconstruction is used only to propose coefficients. Exact
Virasoro, primary, and membership checks are separate certificates.
"""
import json,resource,signal
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from math import sqrt
import numpy as np
import mpmath as mp
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_grade3_action as act
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_exact4 as ex
from hi_cft_20260923_proof_potts import s2,exact_axis
from hi_cft_20260923_proof_potts_exact import serialize

def convert(v,grade):
    inverse=np.linalg.inv(lat.ROOT_COORD);scale=np.array([1/sqrt(c) for c in (5,8,9,8,5,1,2,2)])
    out={}
    for i,c in lat.vector_dict(v).items():
        alpha,osc=lat.BASES[grade][i];c=c*np.prod(scale**np.array(alpha))/lat.osc_norm(osc)
        if not osc:lat.add_term(out,(alpha,()),c);continue
        for js in product(range(8),repeat=len(osc)):
            coefficient=c
            for k,j in zip(osc,js):coefficient*=inverse[k%8,j]
            mon=tuple(sorted(j+8*(k//8) for k,j in zip(osc,js)))
            lat.add_term(out,(alpha,mon),coefficient)
    return {s:c for s,c in out.items() if abs(c)>1e-8*max(map(abs,out.values()))}

def recognize(z,tol):
    if abs(z)<tol:return Q(0),Q(0)
    candidates=[]
    for root in (1.,sqrt(13)):
        for den in (100,1000,10000,100000):
            q=Q(float(z/root)).limit_denominator(den)
            if abs(float(q)*root-z)<tol:
                candidates.append((max(abs(q.numerator),q.denominator),q,Q(0)) if root==1 else (max(abs(q.numerator),q.denominator),Q(0),q))
    for eps in (tol/10,tol,tol*10):
        rel=mp.pslq(mp.matrix([1,mp.sqrt(13),mp.mpf(float(z))]),tol=mp.mpf(eps),maxcoeff=1000000,maxsteps=1000)
        if rel is None or rel[2]==0:continue
        a,b=Q(-int(rel[0]),int(rel[2])),Q(-int(rel[1]),int(rel[2]))
        if abs(float(a)+float(b)*sqrt(13)-z)<tol:candidates.append((max(map(abs,rel)),a,b))
    if not candidates:raise ValueError(z)
    _,a,b=min(candidates);return a,b

def reconstruct(v,grade,normalize,tol):
    out=convert(v,grade)
    if normalize:
        zero={s:c for s,c in out.items() if s[0]==lat.ZERO};scale=max(zero.values(),key=abs)
        out={s:c/scale for s,c in out.items()}
    return {s:x.A((*recognize(c.real,tol),*recognize(c.imag/sqrt(3),tol))) for s,c in out.items()}

def exact_primary_kernel(e,support):
    pivots={};kernels=[]
    for j,state in enumerate(sorted(support)):
        unit={state:x.ONE};image={}
        for n in (1,2,3,4):
            v=x.mode(e,n,unit)
            if n==1:v=x.vadd((1,v),(-3,unit))
            image.update({(n,s):c for s,c in v.items()})
        pre=unit
        while image:
            pivot=max(image)
            if pivot not in pivots:
                scale=image[pivot].inv();pivots[pivot]=({s:c*scale for s,c in image.items()},{s:c*scale for s,c in pre.items()});break
            v,w=pivots[pivot];factor=image[pivot]
            image=x.vadd((1,image),(-factor,v));pre=x.vadd((1,pre),(-factor,w))
        else:kernels.append(pre)
        if j%25==0:print({'primary_kernel_column':j,'pivots':len(pivots),'nullity':len(kernels)},flush=True)
    assert len(kernels)==1,len(kernels)
    return kernels[0]

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(600)
    mp.mp.dps=35;act.setup();ex.install();D=np.load('hi_cft_20260923_proof_pf13_primary.npz')
    e=reconstruct(D['axis'],2,False,2e-10);w=exact_primary_kernel(e,convert(D['W3'][:,0],3))
    assert not x.vadd((1,x.mode(e,1,e)),(-2,e)),'stress reconstruction'
    assert x.mode(e,3,e)=={(x.ZERO,()):x.A(Q(4,5))}
    assert not s2().reduce(e)
    failures={str(n):len(x.vadd((1,x.mode(e,n,w)),(-3,w))) if n==1 else len(x.mode(e,n,w)) for n in (1,2,3,4)}
    assert not any(failures.values()),failures
    assert not x.mode(x.omega(),2,w)
    p=exact_axis();assert not x.mode(p,1,e);assert not x.mode(p,1,w)
    for h in (x.LEFT[0],x.RIGHT[0]):
        for n in range(4):assert not x.mode(h,n,w)
    source=json.loads(Path('hi_cft_20260923_c8_exact_fields.json').read_text());ec=x.read_field(source['fields'][-1]);kl=x.sugawara(x.LEFT,1);kr=x.sugawara(x.RIGHT,39);fc=x.vadd((1,x.omega()),(-1,kl),(-1,kr),(-1,ec))
    projections={name:[str(z) for z in x.mode(e,3,v).get((x.ZERO,()),x.A(0))/x.mode(v,3,v)[(x.ZERO,())]] for name,v in [('left',kl),('right',kr),('e',ec),('f',fc)]}
    out={'stress':serialize(e),'primary':serialize(w),'central_charge':'8/5',
         'exact_stress_membership':True,'exact_primary_equations':True,
         'primary_membership_in_U':'not certified by this producer',
         'K_invariant_stress_projection_coefficients':projections,
         'scope':'Exact Virasoro field and exact weight-three primary; parafermion identification still requires OPE verification.'}
    path=Path('hi_cft_20260923_proof_pf13_exact.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k not in ('stress','primary')},flush=True)

if __name__=='__main__':main()
