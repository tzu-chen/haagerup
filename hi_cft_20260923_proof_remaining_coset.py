"""Exact remaining stress tensor and finite-space commutant diagnostics."""
import json,resource,signal,hashlib
from pathlib import Path
from fractions import Fraction as Q
from collections import Counter
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_general_modes_v2 as gen
from hi_cft_20260923_proof_pf13_ope import read
from hi_cft_20260923_proof_potts import exact_axis
from hi_cft_20260923_proof_potts_exact import serialize
from hi_cft_20260923_proof_pf13_nonlinear import D


def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(180)
    gen.install(4);p=exact_axis()
    fields=json.loads(Path('hi_cft_20260923_proof_pf13_exact.json').read_text())
    z=read(fields['stress']);w=read(fields['primary'])
    assert not x.vadd((1,gen.old.pct(z)),(-1,z))
    assert not x.mode(x.omega(),2,z) and not x.mode(z,2,z)
    assert not x.vadd((1,x.mode(z,0,w)),(-1,D(w)))
    T=x.vadd((Q(1,4),x.mode(x.LEFT[0],-1,x.LEFT[0])),
             (Q(1,156),x.mode(x.RIGHT[0],-1,x.RIGHT[0])),(1,p))
    X=x.vadd((1,x.omega()),(-1,T),(-1,z))
    assert not x.vadd((1,x.mode(X,1,X)),(-2,X))
    assert not x.mode(X,2,X)
    assert x.mode(X,3,X)=={(x.ZERO,()):x.A(Q(9,5))}
    for e in (T,z):
        for n in range(4):assert not x.mode(e,n,X)
    for e,h in ((T,Q(6,65)),(z,Q(7,65)),(X,Q(4,5))):
        for v in x.RIGHT[1:]:
            assert not x.vadd((1,x.mode(e,1,v)),(-h,v))
            assert not x.mode(e,2,v)
    # This is a finite-space numerical diagnostic, not a coset character.
    import numpy as np
    data=np.load('hi_cft_20260923_proof_cartan_axes.npz')
    core=np.load('hi_cft_20260923_proof_core_coset.npz')['C2']
    znum=np.load('hi_cft_20260923_proof_pf13_primary.npz')['axis']
    base=data['basis'];v=base.conj().T@znum;V=base.conj().T@core
    M=np.einsum('kij,i->kj',data['product'],v)
    action=V.conj().T@M@V
    vals=np.linalg.eigvalsh((action+action.conj().T)/2)
    out={'remaining_central_charge':'18/5','stress':serialize(X),
         'PF13_stress_PCT_and_ambient_quasiprimary_exact':True,
         'PF13_translation_on_generator_exact':True,
         'commutes_exactly_with_core_and_PF13_stress':True,
         'right_E_F_conformal_weights':{'core':'6/65','PF13':'7/65','remaining':'4/5'},
         'numerical_PF13_L0_spectrum_on_core_commutant_S2':dict(Counter(str(Q(float(t)).limit_denominator(100000)) for t in vals)),
         'numerical_remaining_commutant_S2_dimension':int(sum(abs(vals)<1e-7)),
         'invariance_residual':float(np.linalg.norm(M@V-V@action)),
         'scope':'The commuting stress and current weights are exact; dimensions refer only to the saved finite spans. No identification or rationality claim for the remaining coset.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(gen.__file__))}}
    path=Path('hi_cft_20260923_proof_remaining_coset.json');assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='stress'}))


if __name__=='__main__':main()
