"""Well-conditioned real multiplicity bases and full-equation refinement."""
import hashlib,json,resource,signal
from pathlib import Path
from time import monotonic
from math import comb,sqrt
import numpy as np
from scipy.sparse.linalg import expm_multiply
import hi_cft_20260923_c8_fields as f
import hi_cft_20260923_c8_ope as ope
import hi_cft_20260923_c8_lattice as lat

def real_highest(U,n,m,FL,FR):
    rotation=(FL-FL.getH()+FR-FR.getH())*(np.pi/2)
    def tau(v):return ope.conjugate(expm_multiply(rotation,v),2)
    V=np.column_stack([tau(U[:,j]) for j in range(U.shape[1])])
    A=np.column_stack(((U+V)/2,(U-V)/(2j)))
    gram=A.conj().T@A
    assert np.max(abs(gram.imag))<1e-12
    eig,rot=np.linalg.eigh(gram.real);mask=eig>1e-8
    assert sum(mask)==U.shape[1]
    R=(A@rot[:,mask])/np.sqrt(eig[mask])
    assert np.max(abs(R.conj().T@R-np.eye(U.shape[1])))<1e-12
    assert max(np.linalg.norm(tau(R[:,j])-R[:,j]) for j in range(R.shape[1]))<1e-12
    return R

def descendants(U,n,m,FL,FR):
    # A unitary rotation plus weight projection avoids error amplification
    # from many successive lowering operations on approximate highest vectors.
    rotated=expm_multiply((FL-FL.getH()+FR-FR.getH())*(np.pi/4),U)
    H1=np.rint(lat.current_matrix(lat.KLEFT[0],0,2).diagonal().real).astype(int)
    H2=np.rint(lat.current_matrix(lat.KRIGHT[0],0,2).diagonal().real).astype(int)
    parts=[]
    for i in range(n):
        for j in range(m):
            A=np.zeros_like(U);mask=(H1==n-1-2*i)&(H2==m-1-2*j)
            A[mask]=rotated[mask]*2**((n+m-2)/2)/sqrt(comb(n-1,i)*comb(m-1,j))
            parts.append(A)
    return np.column_stack(parts)

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('120-second cap')));signal.alarm(120)
    t=monotonic();f.real_highest=real_highest;f.descendants=descendants
    C,M,records,labels=f.prepare(Path('hi_cft_20260923_c8_ope_control.json'))
    best,history,error=f.run_search(M,12,200);theta=best['theta'].copy()
    refinements=[]
    for step in range(3):
        F,D=f.frame(theta);MF=M@F;value=F.T@MF
        jac=np.stack([d.T@MF+F.T@(M@d) for d in D],axis=-1).reshape(-1,9)
        A=np.concatenate((jac.real,jac.imag));b=np.concatenate((value.real.ravel(),value.imag.ravel()))
        delta,res,rank,s=np.linalg.lstsq(A,-b,rcond=1e-12)
        refinements.append({'residual':float(np.linalg.norm(b)),'singular_values':s.tolist(),'rank':int(rank)})
        theta+=delta
    F,_=f.frame(theta);W=C@F
    path=Path('hi_cft_20260923_c8_fields_precise.npz');assert not path.exists()
    np.savez_compressed(path,field_pool=C,b_current_matrices=M,theta=theta,frame=F,W2=W)
    out={'history':history,'refinements':refinements,'final_residual':float(np.linalg.norm(F.T@(M@F))),
         'frame_orthogonality':float(np.linalg.norm(W.conj().T@W-np.eye(120))),
         'theta':theta.tolist(),'seconds':monotonic()-t,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(f.__file__),Path(ope.__file__),Path('hi_cft_20260923_c8_ope_control.npz'))}}
    path.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
