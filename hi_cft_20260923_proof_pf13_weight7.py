"""Exact weight-six truncation and the W3-W5 nonlinear OPE relation."""
import json,resource,signal,hashlib
from pathlib import Path
from fractions import Fraction as Q
from time import monotonic
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_general_modes_v2 as gen
from hi_cft_20260923_proof_pf13_ope import read
from hi_cft_20260923_proof_potts_exact import serialize
from hi_cft_20260923_proof_pf13_nonlinear import D,mode

def powerD(v,n):
    for _ in range(n):v=D(v)
    return v

def coordinates(target,vectors):
    pivots={}
    for j,v in enumerate(vectors):
        image=dict(v);pre={j:x.ONE}
        while image:
            p=max(image)
            if p not in pivots:
                scale=image[p].inv();pivots[p]=({s:c*scale for s,c in image.items()},{s:c*scale for s,c in pre.items()});break
            a,b=pivots[p];scale=image[p];image=x.vadd((1,image),(-scale,a));pre=x.vadd((1,pre),(-scale,b))
        else:raise AssertionError('Dependent comparison fields')
    image=dict(target);result={}
    while image:
        p=max(image)
        if p not in pivots:return None
        a,b=pivots[p];scale=image[p];image=x.vadd((1,image),(-scale,a));result=x.vadd((1,result),(scale,b))
    return [result.get(i,x.A(0)) for i in range(len(vectors))]

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(1800)
    start=monotonic();gen.install(7)
    A=json.loads(Path('hi_cft_20260923_proof_pf13_exact.json').read_text());B=json.loads(Path('hi_cft_20260923_proof_pf13_ope.json').read_text())
    e=read(A['stress']);w=read(A['primary']);W4=read(B['W4']);scale=x.A(B['scale_squared']);lam=Q(14,473);c=Q(8,5)
    v5=read(json.loads(Path('hi_cft_20260923_proof_pf13_W5.json').read_text())['field'])
    path6=Path('hi_cft_20260923_proof_pf13_W6.json')
    if path6.exists():W6=read(json.loads(path6.read_text())['field'])
    else:
        W6=x.vadd((scale,mode(w,1,v5,'canonical W6')))
        path6.write_text(json.dumps({'field':serialize(W6),'normalization':'canonical W6','source_sha256':hashlib.sha256(Path(gen.__file__).read_bytes()).hexdigest()},indent=2)+'\n')
    # The parafermion truncation removes W6 as an independent generator.
    fields=[mode(e,-1,W4,'L W4'),x.vadd((scale,mode(w,-1,w,'W3 W3'))),
            mode(e,-1,mode(e,-1,e,'L L'),'L L L'),
            mode(D(D(e)),-1,e,'d2L L'),mode(D(e),-1,D(e),'dL dL'),D(D(W4)),powerD(e,4)]
    names=[':L W4:',':W3 W3:',':L(:LL:):',':d2L L:',':dL dL:','d2W4','d4L']
    coeff=coordinates(W6,fields);assert coeff is not None,'W6 truncation failed'
    trunc={'exact_W6_truncation':True,'basis':names,'coefficients':[list(map(str,a)) for a in coeff],
           'W6_support':len(W6),'seconds':monotonic()-start,
           'scope':'An exact weight-six decoupling identity in the candidate subalgebra; not by itself a universal-algebra isomorphism.'}
    p=Path('hi_cft_20260923_proof_pf13_truncation.json');assert not p.exists();p.write_text(json.dumps(trunc,indent=2)+'\n');print(json.dumps(trunc),flush=True)
    target=x.vadd((scale,mode(w,0,v5,'W3_0 W5')))
    rhs=x.vadd((Q(1,3),D(W6)),(Q(32,3)*lam,mode(e,-1,D(W4),'L dW4')),
               (-Q(64,3)*lam,mode(D(e),-1,W4,'dL W4')),
               (-Q(16,3)*lam,mode(powerD(e,3),-1,e,'d3L L')),
               (-Q(5,4)+Q(2,3)*lam*(1+c),powerD(W4,3)),
               (Q(5,72)-lam*(13+5*c)/45,powerD(e,5)))
    residual=x.vadd((1,target),(-1,rhs));assert not residual,('A2 simple-pole residual',len(residual))
    out={'exact_Linshaw_A2_simple_pole':True,'exact_weight_six_truncation':True,
         'c':'8/5','lambda':'14/473','seconds':monotonic()-start,
         'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'Additional finite OPE identities; the complete hypotheses of Linshaw Theorem 5.2 still need a final audit.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(gen.__file__),path6)}}
    path=Path('hi_cft_20260923_proof_pf13_weight7.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
