"""The first full nonlinear W3-W4 OPE relation, tested exactly.

Fields are streamed; no grade-five or grade-six ambient basis is built.
Canonical odd generators carry a common square-root scale, canceled in
all displayed identities. Each completed field is checkpointed.
"""
import json,resource,signal,hashlib
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
from time import monotonic
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_general_modes_v2 as gen
from hi_cft_20260923_proof_pf13_ope import read
from hi_cft_20260923_proof_potts_exact import serialize

def D(v):
    out={}
    for (a,o),c in v.items():
        for i,b in enumerate(a):
            if b:x.add(out,(a,tuple(sorted(o+(i,)))),b*c)
        for k,m in Counter(o).items():
            p=list(o);p.remove(k);p.append(k+8);p.sort();x.add(out,(a,tuple(p)),(k//8+1)*m*c)
    return out

def mode(u,n,v,label):
    out={};start=monotonic()
    for j,(s,a) in enumerate(u.items()):
        for t,b in v.items():
            terms=gen.basis_mode(s,n,t)
            if terms:
                ab=a*b
                for r,c in terms:x.add(out,r,ab*c)
        assert len(out)<=250000,('sparse output cap',label,len(out))
        if j%50==0:print({'mode':label,'row':j,'rows':len(u),'support':len(out),'seconds':monotonic()-start},flush=True)
    return out

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(900)
    gen.install(6);start=monotonic();A=json.loads(Path('hi_cft_20260923_proof_pf13_exact.json').read_text());B=json.loads(Path('hi_cft_20260923_proof_pf13_ope.json').read_text())
    e=read(A['stress']);w=read(A['primary']);W4=read(B['W4']);lam=Q(14,473);c=Q(8,5)
    # This repeats the nontrivial low-target control after the cache/guard change.
    a0=x.A(B['a0']);assert not x.vadd((1,mode(w,3,W4,'leading control')),(-a0,w))
    path5=Path('hi_cft_20260923_proof_pf13_W5.json')
    if path5.exists():v5=read(json.loads(path5.read_text())['field'])
    else:
        v5=mode(w,1,W4,'W5/s');path5.write_text(json.dumps({'field':serialize(v5),'normalization':'W5/s where W3=s*w','source_sha256':hashlib.sha256(Path(gen.__file__).read_bytes()).hexdigest()},indent=2)+'\n')
    target=mode(w,0,W4,'W3_0 W4/s')
    rhs=x.vadd((Q(2,5),D(v5)),(Q(32,5)*lam,mode(e,-1,D(w),'L dW3/s')),
               (-Q(48,5)*lam,mode(D(e),-1,w,'dL W3/s')),
               (Q(2,15)*(-5+2*lam*(c-1)),D(D(D(w)))))
    residual=x.vadd((1,target),(-1,rhs));assert not residual,('nonlinear relation residual',len(residual))
    out={'exact_Linshaw_5_7_simple_pole':True,'c':'8/5','lambda':'14/473',
         'W5_over_s_support':len(v5),'weight_six_product_support':len(target),
         'seconds':monotonic()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'One nonlinear relation is certified. The remaining initial relations in Theorem 5.2 still require verification.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(gen.__file__),Path('hi_cft_20260923_proof_pf13_exact.json'),Path('hi_cft_20260923_proof_pf13_ope.json'))}}
    path=Path('hi_cft_20260923_proof_pf13_nonlinear.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
