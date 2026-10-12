"""Exact Potts extension and its membership in the generated algebra.

The standard sqrt(2) A2 weight-three primary is written in our cocycle
and torus gauge. Membership is proved using only explicit S2 products.
"""
import hashlib,json,resource,signal
from fractions import Fraction as Q
from pathlib import Path
from time import monotonic
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_exact4 as ex
from hi_cft_20260923_proof_potts import exact_axis,ALPHA,BETA

def scale(a,n):return tuple(n*z for z in a)

def exact_primary():
    p=exact_axis();gamma=x.plus(ALPHA,BETA)
    A=x.plus(ALPHA,scale(BETA,-1));B=x.plus(ALPHA,scale(BETA,2));C=x.plus(scale(ALPHA,-2),scale(BETA,-1))
    w=x.mode(x.cartan(A),-1,x.mode(x.cartan(B),-1,x.cartan(C)))
    for h,r in ((A,gamma),(B,ALPHA),(C,BETA)):
        pair={(a,()):5*p[a,()] for a in (r,scale(r,-1))}
        w=x.vadd((1,w),(-9,x.mode(x.cartan(h),-1,pair)))
    return w

def serialize(v):
    return [{'momentum':list(a),'oscillators':list(o),'coefficient':[str(z) for z in c]} for (a,o),c in sorted(v.items())]

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second cap')));signal.alarm(600)
    start=monotonic();ex.install();p=exact_axis();w=exact_primary()
    assert not x.vadd((1,x.mode(p,1,w)),(-3,w)),'p weight'
    for n in (2,3,4):assert not x.mode(p,n,w),('primary',n)
    assert not x.mode(x.omega(),2,w),'ambient quasi-primary'
    source=Path('hi_cft_20260923_c8_exact_fields.json');data=json.loads(source.read_text());S2=x.Span();vectors=[]
    def add2(v):
        if S2.reduce(v,True):vectors.append(v)
    for c in x.LEFT+x.RIGHT:
        add2(x.mode(c,-2,x.VAC))
        for d in x.LEFT+x.RIGHT:add2(x.mode(c,-1,d))
    add2(x.omega());add2(x.read_field(data['fields'][-1]))
    for row in data['fields'][:-1]:
        for v in x.descendants(x.read_field(row),*row['dimensions']):add2(v)
    assert S2.dimension==120
    def wt(v):return x.weight(next(iter(v)))
    span=x.Span();count=0;history=[]
    def add3(v):
        if v:assert wt(v)==(0,0)
        span.reduce(v,True)
        assert span.dimension<=58
    for c in x.LEFT+x.RIGHT:
        target=tuple(-z for z in wt(c))
        for v in vectors:
            if wt(v)==target:add3(x.mode(c,-1,v))
    for v in vectors:
        if wt(v)==(0,0):add3(x.mode(x.omega(),0,v))
    history.append({'stage':'descendants','rank':span.dimension})
    for a in sorted(vectors,key=len):
        target=tuple(-z for z in wt(a))
        for b in vectors:
            if wt(b)==target:
                add3(x.mode(a,0,b));count+=1
                if not span.reduce(w):break
        if not span.reduce(w):break
    assert not span.reduce(w),'Potts primary has not been generated'
    # Zero modes on currents, obtained by skew symmetry; derivative of a
    # vacuum scalar vanishes, so w_2 J = -J_2 w.
    eig=[]
    for J in x.RIGHT:
        v=x.vadd((-1,x.mode(J,2,w)))
        if not v:eig.append(['0']*4);continue
        pivot=next(iter(J));c=v[pivot]/J[pivot]
        assert not x.vadd((1,v),(-c,J))
        eig.append([str(z) for z in c])
    out={'arithmetic':'Q(sqrt(13),sqrt(-3))','exact_p_central_charge':'4/5',
         'exact_weight_three_primary':True,'exact_membership_in_generated_S3':True,
         'Cartan_zero_span_rank_at_membership':span.dimension,'tested_zero_weight_pairs':count,'history':history,
         'w2_eigenvalues_on_H_E_F':eig,'weight_three_primary':serialize(w),'potts_stress':serialize(p),
         'seconds':monotonic()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'An actual rational three-state Potts subVOA lies in U, by the standard sqrt(2) A2 realization and exact membership. This does not make U rational.',
         'source_sha256':{str(z):hashlib.sha256(z.read_bytes()).hexdigest() for z in (Path(__file__),Path(x.__file__),Path(ex.__file__),source)}}
    path=Path('hi_cft_20260923_proof_potts_exact.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k not in ('weight_three_primary','potts_stress')}),flush=True)

if __name__=='__main__':main()
