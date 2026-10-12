"""Check generator modes on the entire proposed weight-three space.

Sparse three-vertex modes are streamed into Cartan blocks; no dense
11586-square matrix is formed. The test is numerical, not a certificate.
"""
import hashlib,json,resource,signal
from itertools import combinations_with_replacement
from pathlib import Path
from time import monotonic
import numpy as np
from scipy import sparse
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_ope as ope
import hi_cft_20260923_c8_grade3 as g

def setup():
    n6=g.momenta6()
    zo=[(i+16,) for i in range(8)]+[tuple(sorted((i+8,j))) for i in range(8) for j in range(8)]+list(combinations_with_replacement(range(8),3))
    o2=[(i+8,) for i in range(8)]+list(combinations_with_replacement(range(8),2))
    lat.BASES[3]=[(lat.ZERO,o) for o in zo]+[(a,o) for a in lat.ROOTS for o in o2]+[(a,(i,)) for a in lat.NORM4 for i in range(8)]+[(a,()) for a in n6]
    lat.INDICES[3]={s:i for i,s in enumerate(lat.BASES[3])};lat.vertex_action=g.vertex;lat.creation=g.creation
    M1=lat.current_matrix(lat.KLEFT[0],0,3);M2=lat.current_matrix(lat.KRIGHT[0],0,3)
    H1=np.rint(M1.diagonal().real).astype(int);H2=np.rint(M2.diagonal().real).astype(int)
    return {w:np.flatnonzero((H1==w[0])&(H2==w[1])) for w in set(zip(H1,H2))}

def matrix(u,mode):
    target=4-mode;rows=[];cols=[];values=[]
    for j,state in enumerate(lat.BASES[3]):
        for i,a in lat.vector_dict(u).items():
            alpha,osc=lat.BASES[2][i];assert not osc
            for s,c in g.vertex(alpha,mode,state):rows.append(lat.INDICES[target][s]);cols.append(j);values.append(a*c)
    return sparse.csc_matrix((values,(rows,cols)),shape=(len(lat.BASES[target]),len(lat.BASES[3])))

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('120-second cap')));signal.alarm(120)
    t=monotonic();indices=setup();saved=np.load('hi_cft_20260923_c8_grade3_span.npz')
    spaces={tuple(map(int,key.split('_')[1:])):saved[key] for key in saved.files}
    W=np.load('hi_cft_20260923_c8_fields_precise.npz')['W2'];u=W[:,92]
    K=np.linalg.qr(np.column_stack([ope.current_vector(c) for c in lat.KLEFT+lat.KRIGHT]))[0]
    records=[]
    for mode in (1,2,3):
        M=matrix(u,mode);leak=0.;peak=0.;relative=0.;total=0.
        for w,Q in spaces.items():
            result=M[:,indices[w]]@Q
            if mode==1:
                target=(w[0]+1,w[1]+13)
                if target in spaces:
                    idx=indices[target];R=spaces[target];residual=result.copy()
                    residual[idx]-=R@(R.conj().T@result[idx])
                else:residual=result
            else:
                R=W if mode==2 else K;residual=result-R@(R.conj().T@result)
            n=np.linalg.norm(result);r=np.linalg.norm(residual)
            leak+=r*r;total+=n*n;peak=max(peak,lat.max_abs(residual));relative=max(relative,float(r/max(1,n)))
        record={'generator_mode':mode,'target_grade':4-mode,'total_leakage':float(np.sqrt(leak)),
                'total_image_norm':float(np.sqrt(total)),'max_entry':peak,'max_block_relative_leakage':relative}
        records.append(record);print(record,flush=True)
    assert max(r['max_block_relative_leakage'] for r in records)<1e-6,'Generator leaks outside proposed grades'
    path=Path('hi_cft_20260923_c8_grade3_action.json');assert not path.exists()
    out={'generator':'the single (2,14) three-vertex highest field','tested_source_dimension':956,
         'modes':records,'seconds':monotonic()-t,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'Numerical generator-mode stability through weight three; no conclusion about higher composites.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(g.__file__),Path('hi_cft_20260923_c8_grade3_span.npz'),Path('hi_cft_20260923_c8_fields_precise.npz'))}}
    path.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
