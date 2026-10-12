"""Numerical weight-three primary test for the c=8/5 axis."""
import json,resource,signal
from pathlib import Path
from collections import Counter
from fractions import Fraction
import numpy as np
from scipy.linalg import eigh,svd
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_ope as ope
import hi_cft_20260923_c8_grade3 as g
import hi_cft_20260923_c8_grade3_action as act

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(300)
    act.setup();D=np.load('hi_cft_20260923_proof_cartan_axes.npz');cs=2*np.sum(D['axes']**2,axis=1)
    axis=D['basis']@D['axes'][np.argmin(abs(cs-1.6))];V=np.load('hi_cft_20260923_proof_core_coset.npz')['C3']
    def action(v,n):
        out=np.zeros(len(lat.BASES[4-n]),complex)
        for i,a in lat.vector_dict(axis).items():
            for j,b in lat.vector_dict(v).items():
                for s,c in g.basis_mode(lat.BASES[2][i],n,lat.BASES[3][j]).items():out[lat.INDICES[4-n][s]]+=a*b*c
        return out
    images=np.column_stack([action(v,1) for v in V.T]);M=V.conj().T@images
    ev,R=eigh((M+M.conj().T)/2);E=V@R[:,abs(ev-3)<1e-8]
    if E.shape[1]:
        constraint=np.column_stack([action(v,2) for v in E.T]);_,s,vh=svd(constraint,full_matrices=False)
        W=E@vh[s<1e-8].conj().T
    else:W=E
    out={'central_charge':'8/5','coset_grade3_space':V.shape[1],
         'spectrum':dict(Counter(str(Fraction(float(t)).limit_denominator(100000)) for t in ev)),
         'weight_three_multiplicity':E.shape[1],'primary_weight_three_multiplicity':W.shape[1],
         'space_invariance_residual':float(np.linalg.norm(images-V@M))}
    path=Path('hi_cft_20260923_proof_pf13_primary.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n')
    np.savez_compressed(path.with_suffix('.npz'),axis=axis,W3=W);print(json.dumps(out),flush=True)

if __name__=='__main__':main()
