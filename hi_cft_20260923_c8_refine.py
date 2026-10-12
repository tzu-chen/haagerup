"""Refine the saved constructive frame using every current equation."""
import hashlib,json,resource,signal
from pathlib import Path
from time import monotonic
import numpy as np
import hi_cft_20260923_c8_fields as f

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('120-second cap')));signal.alarm(120)
    t=monotonic();source=Path('hi_cft_20260923_c8_fields_attempt.npz');z=np.load(source)
    theta=z['theta'].copy();M=z['b_current_matrices'];history=[]
    for step in range(5):
        F,D=f.frame(theta);MF=M@F;value=F.T@MF
        jac=np.stack([d.T@MF+F.T@(M@d) for d in D],axis=-1).reshape(-1,9)
        A=np.concatenate((jac.real,jac.imag));b=np.concatenate((value.real.ravel(),value.imag.ravel()))
        delta,res,rank,s=np.linalg.lstsq(A,-b,rcond=1e-12)
        history.append({'step':step,'residual':float(np.linalg.norm(b)),'singular_values':s.tolist(),'rank':int(rank),'step_norm':float(np.linalg.norm(delta))})
        theta+=delta
    F,_=f.frame(theta);W=z['field_pool']@F
    path=Path('hi_cft_20260923_c8_fields_refined.npz');assert not path.exists()
    np.savez_compressed(path,**{k:z[k] for k in ('field_pool','b_current_matrices')},theta=theta,frame=F,W2=W)
    out={'history':history,'final_residual':float(np.linalg.norm(F.T@(M@F))),
         'theta':theta.tolist(),'seconds':monotonic()-t,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,Path(__file__),Path(f.__file__))}}
    path.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)

if __name__=='__main__':main()
