"""Exact low OPE invariant for the c=8/5 weight-three generator.

First checks the new recursive mode engine on the independently known
Potts algebra. This invariant is necessary, not sufficient, for an
isomorphism with the level-13 parafermion algebra.
"""
import json,resource,signal,hashlib
from pathlib import Path
from fractions import Fraction as Q
from time import monotonic
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_exact4 as old
import hi_cft_20260923_proof_general_modes as gen
from hi_cft_20260923_proof_potts import exact_axis
from hi_cft_20260923_proof_potts_exact import exact_primary,serialize

def read(rows):return {(tuple(r['momentum']),tuple(r['oscillators'])):x.A(r['coefficient']) for r in rows}

def invariant(e,w,c,label):
    start=monotonic();norm=x.mode(w,5,w)[(x.ZERO,())];scale=x.A(c/3)/norm
    print({'stage':label,'w_support':len(w),'w_norm':list(map(str,norm)),'scale_squared':list(map(str,scale))},flush=True)
    assert not x.vadd((scale,x.mode(w,3,w)),(-2,e))
    W4=x.vadd((scale,x.mode(w,1,w)))
    # W3_1 adjoint is W3_3 for the chosen physical normalization.
    # Hence a0 = ||W4||^2 / ||W3||^2.
    n4=gen.inner(W4,W4);a0=n4/(c/3);lam=(31-a0)/(16*(2+c))
    direct=x.mode(w,3,W4);assert not x.vadd((1,direct),(-a0,w))
    print({'stage':label,'lambda':list(map(str,lam)),'seconds':monotonic()-start},flush=True)
    return {'norm':list(map(str,norm)),'scale_squared':list(map(str,scale)),
            'W4_norm':list(map(str,n4)),'a0':list(map(str,a0)),'lambda':list(map(str,lam)),
            'W4_support':len(W4),'seconds':monotonic()-start},W4

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(900)
    old.install();p=exact_axis();v=exact_primary();control=old.basis_mode
    pairs=[(a,b) for a in p for b in list(v)[:3]][:100]
    gen.install(4)
    for a,b in pairs:
        for n in (1,2,3):assert dict(gen.basis_mode(a,n,b))==dict(control(a,n,b))
    pc,_=invariant(p,v,Q(4,5),'Potts control');assert pc['lambda']==['4/13','0','0','0'],pc
    D=json.loads(Path('hi_cft_20260923_proof_pf13_exact.json').read_text());e=read(D['stress']);w=read(D['primary'])
    result,W4=invariant(e,w,Q(8,5),'candidate parafermion13')
    result.update({'control_Potts':pc,'target_lambda':'14/473','matches_level13':result['lambda']==['14/473','0','0','0'],
                   'scope':'Exact weight-three self-OPE and W3-W4 leading invariant only; full universal-algebra relations are not certified.',
                   'W4':serialize(W4),'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(gen.__file__),Path('hi_cft_20260923_proof_pf13_exact.json'))}})
    path=Path('hi_cft_20260923_proof_pf13_ope.json');assert not path.exists();path.write_text(json.dumps(result,indent=2)+'\n')
    print({k:v for k,v in result.items() if k!='W4'},flush=True)

if __name__=='__main__':main()
