"""Low weights in the c=26/5 commutant of the rational core."""
import hashlib,json,resource,signal
from pathlib import Path
from time import monotonic
import numpy as np
from scipy.linalg import svd
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_ope as ope
import hi_cft_20260923_c8_grade3 as g
import hi_cft_20260923_c8_grade3_action as act

def null_space(matrix,rcond):
    # All constraints here are tall: economy SVD avoids a quadratic left factor.
    assert matrix.shape[0] >= matrix.shape[1]
    _,singular,vh=svd(matrix,full_matrices=False)
    rank=np.count_nonzero(singular > rcond*singular[0]) if len(singular) else 0
    return vh[rank:].conj().T

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('180-second cap')));signal.alarm(180)
    start=monotonic();idx=act.setup();saved=np.load('hi_cft_20260923_c8_grade3_span.npz');block=saved['weight_0_0'];ids=idx[(0,0)]
    constraints=np.vstack([lat.current_matrix(h,n,3)[:,ids]@block for h in (lat.KLEFT[0],lat.KRIGHT[0]) for n in (1,2,3)])
    ker=null_space(constraints,rcond=1e-9);V=np.zeros((len(lat.BASES[3]),ker.shape[1]),complex);V[ids]=block@ker
    print({'Heisenberg_commutant_grade3':V.shape[1]},flush=True)
    p=np.load('hi_cft_20260923_proof_potts.npz')['p'];images=[]
    for v in V.T:
        out=np.zeros(len(lat.BASES[3]),complex)
        for i,a in lat.vector_dict(p).items():
            for j,b in lat.vector_dict(v).items():
                for s,c in g.basis_mode(lat.BASES[2][i],1,lat.BASES[3][j]).items():out[lat.INDICES[3][s]]+=a*b*c
        images.append(out)
    image=np.column_stack(images);kernel=null_space(image,rcond=1e-8);C3=V@kernel
    data=np.load('hi_cft_20260923_proof_cartan_axes.npz');axes=data['axes'];cs=2*np.sum(axes*axes,axis=1);pc=axes[np.argmin(abs(cs-.8))]
    P=np.einsum('kij,i->kj',data['product'],pc);ker2=null_space(P,rcond=1e-8);C2=data['basis']@ker2
    out={'numerical_commutant_S2_dimension':C2.shape[1],'numerical_commutant_S3_dimension':C3.shape[1],
         'Heisenberg_commutant_S3_dimension':V.shape[1],'core_central_charge':'14/5','coset_central_charge':'26/5',
         'p1_kernel_residual':float(np.linalg.norm(image@kernel)),'seconds':monotonic()-start,
         'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'Dimensions inside the certified S2 and finite product span S3, not all-weight coset characters.'}
    path=Path('hi_cft_20260923_proof_core_coset.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n');np.savez_compressed(path.with_suffix('.npz'),C2=C2,C3=C3);print(json.dumps(out),flush=True)

if __name__=='__main__':main()
