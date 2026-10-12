"""Certify the c=8/5 weight-three field belongs to U and stress control.

The positive stress decomposition is unconditional. Its C2-cofiniteness
consequence is conditional on identifying the generated c=8/5 algebra
as the rational level-13 parafermion algebra.
"""
import json,resource,signal,hashlib
from pathlib import Path
from fractions import Fraction as Q
from time import monotonic
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_exact4 as ex
from hi_cft_20260923_proof_pf13_ope import read
from hi_cft_20260923_proof_potts import exact_axis

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(900)
    start=monotonic();ex.install();D=json.loads(Path('hi_cft_20260923_proof_pf13_exact.json').read_text());w=read(D['primary']);z=read(D['stress']);p=exact_axis()
    source=Path('hi_cft_20260923_c8_exact_fields.json');data=json.loads(source.read_text());S2=x.Span();vectors=[]
    def add2(v):
        if S2.reduce(v,True):vectors.append(v)
    for c in x.LEFT+x.RIGHT:
        add2(x.mode(c,-2,x.VAC))
        for d in x.LEFT+x.RIGHT:add2(x.mode(c,-1,d))
    add2(x.omega());add2(x.read_field(data['fields'][-1]))
    for row in data['fields'][:-1]:
        for v in x.descendants(x.read_field(row),*row['dimensions']):add2(v)
    def wt(v):return x.weight(next(iter(v)))
    S3=x.Span();count=0
    for c in x.LEFT+x.RIGHT:
        target=tuple(-j for j in wt(c))
        for v in vectors:
            if wt(v)==target:S3.reduce(x.mode(c,-1,v),True)
    for v in vectors:
        if wt(v)==(0,0):S3.reduce(x.mode(x.omega(),0,v),True)
    for a in sorted(vectors,key=len):
        target=tuple(-j for j in wt(a))
        for b in vectors:
            if wt(b)==target:
                S3.reduce(x.mode(a,0,b),True);count+=1
                if count%10==0:print({'pairs':count,'rank':S3.dimension,'seconds':monotonic()-start},flush=True)
                if not S3.reduce(w):break
        if not S3.reduce(w):break
    assert not S3.reduce(w),'Exact membership failed'
    # The invariant S2 space consists of these four pairwise orthogonal stresses.
    e=x.read_field(data['fields'][-1]);kl=x.sugawara(x.LEFT,1);kr=x.sugawara(x.RIGHT,39);f=x.vadd((1,x.omega()),(-1,kl),(-1,kr),(-1,e))
    stresses=[kl,kr,e,f]
    def average(v):
        return x.vadd(*[(x.mode(v,3,t).get((x.ZERO,()),x.A(0))/x.mode(t,3,t)[(x.ZERO,())],t) for t in stresses])
    co=[Q(1),Q(3403,4563),Q(25,6),Q(25,26)]
    assert not x.vadd((co[0],kl),(co[1],kr),(co[2],average(p)),(co[3],average(z)),(-1,x.omega()))
    # PCT stability of the weight-three line gives a unitary generated algebra.
    theta=ex.pct(w);key=next(iter(w));factor=theta[key]/w[key];assert not x.vadd((1,theta),(-factor,w))
    out={'exact_membership_in_generated_S3':True,'Cartan_zero_span_rank_at_membership':S3.dimension,'zero_weight_pairs':count,
         'positive_stress_decomposition_coefficients':list(map(str,co)),
         'decomposition_order':['omega_A1_1','omega_A1_39','SU2_average_Potts_stress','SU2_average_c8over5_stress'],
         'PCT_stable_weight_three_line':True,
         'conditional_consequence':'If <z,w> is the rational K(sl2,13), the positive-stress argument of Dong-Wang proves U is C2-cofinite.',
         'parafermion_identification_proved':False,'seconds':monotonic()-start,
         'scope':'Exact membership and positive stress control. The C2 conclusion is conditional, not established.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path('hi_cft_20260923_proof_pf13_exact.json'),source)}}
    path=Path('hi_cft_20260923_proof_pf13_membership.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
