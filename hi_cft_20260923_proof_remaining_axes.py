"""Exact splitting of the remaining c=18/5 stress, without VOA guesses."""
import json,resource,signal,hashlib
from pathlib import Path
from fractions import Fraction as Q
import numpy as np
import mpmath as mp
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_general_modes_v2 as gen
from hi_cft_20260923_proof_pf13_exact import reconstruct
from hi_cft_20260923_proof_pf13_ope import read
from hi_cft_20260923_proof_potts import s2,exact_axis
from hi_cft_20260923_proof_potts_exact import serialize


def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(120)
    mp.mp.dps=35;gen.install(3)
    data=np.load('hi_cft_20260923_proof_cartan_axes.npz');cs=2*np.sum(data['axes']**2,axis=1)
    pn=data['basis'].conj().T@np.load('hi_cft_20260923_proof_potts.npz')['p']
    zn=data['basis'].conj().T@np.load('hi_cft_20260923_proof_pf13_primary.npz')['axis']
    candidates=[a for a,c in zip(data['axes'],cs) if abs(c-32/19)<1e-7 and
                all(np.linalg.norm(np.einsum('kij,i,j->k',data['product'],a,b))<1e-7 for b in (pn,zn))]
    assert len(candidates)==1,len(candidates)
    q=reconstruct(data['basis']@candidates[0],2,False,2e-10)
    X=read(json.loads(Path('hi_cft_20260923_proof_remaining_coset.json').read_text())['stress'])
    z=read(json.loads(Path('hi_cft_20260923_proof_pf13_exact.json').read_text())['stress']);p=exact_axis()
    r=x.vadd((1,X),(-1,q));S=s2()
    for e,c in ((q,Q(32,19)),(r,Q(182,95))):
        assert not S.reduce(e)
        assert not x.vadd((1,gen.old.pct(e)),(-1,e))
        assert not x.vadd((1,x.mode(e,1,e)),(-2,e))
        assert not x.mode(e,2,e)
        assert x.mode(e,3,e)=={(x.ZERO,()):x.A(c/2)}
        assert not x.mode(p,1,e)
        for h in (x.LEFT[0],x.RIGHT[0]):
            for n in range(3):assert not x.mode(h,n,e)
        for n in range(4):assert not x.mode(z,n,e)
    for n in range(4):assert not x.mode(q,n,r)
    out={'exact_commuting_stresses_in_U':True,'central_charges':['32/19','182/95'],
         'first_stress':serialize(q),'second_stress':serialize(r),
         'scope':'Exact Virasoro fields, membership and commutation. These central charges do not identify their generated or extended VOAs, and no rationality is asserted.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(gen.__file__))}}
    path=Path('hi_cft_20260923_proof_remaining_axes.json');assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if 'stress' not in k or k=='exact_commuting_stresses_in_U'}))


if __name__=='__main__':main()
