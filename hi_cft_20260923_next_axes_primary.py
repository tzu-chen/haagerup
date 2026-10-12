"""Explore the two remaining commuting stresses on a saved finite S3 span."""
import hashlib,json,resource,signal
from pathlib import Path
from time import monotonic
from fractions import Fraction
from collections import Counter
import numpy as np
from scipy.linalg import eigh,svd
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_grade3 as g
import hi_cft_20260923_c8_grade3_action as act

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second cap')))
    signal.alarm(600);start=monotonic();act.setup()
    data=np.load('hi_cft_20260923_proof_cartan_axes.npz')
    cs=2*np.sum(data['axes']**2,axis=1)
    pn=data['basis'].conj().T@np.load('hi_cft_20260923_proof_potts.npz')['p']
    zn=data['basis'].conj().T@np.load('hi_cft_20260923_proof_pf13_primary.npz')['axis']
    found=[a for a,c in zip(data['axes'],cs) if abs(c-32/19)<1e-7 and
           all(np.linalg.norm(np.einsum('kij,i,j->k',data['product'],a,b))<1e-7 for b in (pn,zn))]
    assert len(found)==1
    q=found[0];r=data['total']-pn-zn-q
    V=np.load('hi_cft_20260923_proof_core_coset.npz')['C3']
    frames={};records=[]
    for label,c,coeff in [('PF17',Fraction(32,19),q),('GKO13_4',Fraction(182,95),r)]:
        axis=data['basis']@coeff
        def action(v,n):
            out=np.zeros(len(lat.BASES[4-n]),complex)
            for i,a in lat.vector_dict(axis).items():
                for j,b in lat.vector_dict(v).items():
                    for s,t in g.basis_mode(lat.BASES[2][i],n,lat.BASES[3][j]).items():
                        out[lat.INDICES[4-n][s]]+=a*b*t
            return out
        images=np.column_stack([action(v,1) for v in V.T]);M=V.conj().T@images
        ev,R=eigh((M+M.conj().T)/2);E=V@R[:,abs(ev-3)<1e-8]
        if E.shape[1]:
            constraints=np.vstack([np.column_stack([action(v,n) for v in E.T]) for n in (2,3,4)])
            _,s,vh=svd(constraints,full_matrices=False);W=E@vh[s<1e-8].conj().T
        else:W=E;s=np.array([])
        row={'label':label,'central_charge':str(c),'space_dimension':V.shape[1],
             'spectrum':dict(Counter(str(Fraction(float(t)).limit_denominator(100000)) for t in ev)),
             'weight_three_multiplicity':E.shape[1],'primary_multiplicity':W.shape[1],
             'invariance_residual':float(np.linalg.norm(images-V@M)),
             'primary_constraint_singular_values':s.tolist(),'seconds':monotonic()-start}
        records.append(row);frames[label+'_axis']=axis;frames[label+'_W3']=W
        print(json.dumps(row),flush=True)
    out={'records':records,'scope':'Numerical diagnostics within a saved finite generated span only; central-charge labels are hypotheses, not VOA identifications.',
         'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(g.__file__),Path('hi_cft_20260923_proof_core_coset.npz'),Path('hi_cft_20260923_proof_cartan_axes.npz'))}}
    path=Path('hi_cft_20260923_next_axes_primary.json');assert not path.exists()
    path.write_text(json.dumps(out,indent=2)+'\n');np.savez_compressed(path.with_suffix('.npz'),**frames)

if __name__=='__main__':main()
