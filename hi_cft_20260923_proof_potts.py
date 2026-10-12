"""An exact c=4/5 axis and exploratory test of its weight-three extension."""
import hashlib,json,resource,signal
from fractions import Fraction as Q
from itertools import combinations_with_replacement
from pathlib import Path
from time import monotonic
import numpy as np
from scipy.linalg import eigh,null_space
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_exact4 as ex
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_ope as ope
import hi_cft_20260923_c8_grade3 as g3
import hi_cft_20260923_c8_grade3_action as act3

ALPHA=(0,0,0,1,1,0,-1,-1)
BETA=(1,1,0,-1,-1,0,0,0)

def exact_axis():
    h=x.cartan(ALPHA);k=x.cartan(BETA);gamma=x.plus(ALPHA,BETA)
    p=x.vadd((Q(1,15),x.mode(h,-1,h)),(Q(1,15),x.mode(k,-1,k)),(Q(1,15),x.mode(h,-1,k)))
    coefficients={ALPHA:x.A((0,Q(-1,100),Q(-3,100),0)),
                  tuple(-a for a in ALPHA):x.A((0,Q(-1,10),Q(3,10),0)),
                  BETA:x.A((Q(7,100),0,0,Q(3,100))),
                  tuple(-a for a in BETA):x.A((Q(7,100),0,0,Q(-3,100))),
                  gamma:x.A((0,Q(-1,100),Q(3,100),0)),
                  tuple(-a for a in gamma):x.A((0,Q(-1,10),Q(-3,10),0))}
    return x.vadd((1,p),(1,{(a,()):c for a,c in coefficients.items()}))

def s2():
    data=json.loads(Path('hi_cft_20260923_c8_exact_fields.json').read_text());S=x.Span();fields=[x.read_field(r) for r in data['fields']]
    for c in x.LEFT+x.RIGHT:
        S.reduce(x.mode(c,-2,x.VAC),True)
        for d in x.LEFT+x.RIGHT:S.reduce(x.mode(c,-1,d),True)
    S.reduce(x.omega(),True);S.reduce(fields[-1],True)
    for row,u in zip(data['fields'][:-1],fields[:-1]):
        for v in x.descendants(u,*row['dimensions']):S.reduce(v,True)
    assert S.dimension==120
    return S

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second cap')));signal.alarm(600)
    start=monotonic();p=exact_axis();S=s2()
    assert not S.reduce(p),'Axis is not in the generated weight-two space'
    assert not x.vadd((1,x.mode(p,1,p)),(-2,p))
    assert not x.mode(p,2,p)
    assert x.mode(p,3,p)=={(x.ZERO,()):x.A(Q(2,5))}
    assert ex.pct(p)==p
    for c in x.LEFT:assert not x.mode(p,1,c)
    assert not x.mode(p,1,x.RIGHT[0])
    for c in x.RIGHT[1:]:assert not x.vadd((1,x.mode(p,1,c)),(-Q(1,15),c))
    print({'exact_c':'4/5','membership_in_generated_S2':True,'right_EF_weight':'1/15'},flush=True)
    idx3=act3.setup();saved=np.load('hi_cft_20260923_proof_cartan_axes.npz');axes=saved['axes'];cs=2*np.sum(axes*axes,axis=1)
    pn=saved['basis']@axes[np.argmin(abs(cs-.8))]
    directions=np.linalg.qr(np.column_stack((lat.coordinates(ALPHA),lat.coordinates(BETA))))[0]
    vectors=[]
    def oscillator_state(alpha,ops):
        v={(alpha,()):1.}
        for direction,n in ops:
            out={}
            for s,c in v.items():
                for r,d in lat.heisenberg_action(directions[:,direction],-n,s):lat.add_term(out,r,c*d)
            v=out
        result=np.zeros(len(lat.BASES[3]),complex)
        for s,c in v.items():result[lat.INDICES[3][s]]=c
        return result/np.linalg.norm(result)
    for i in range(2):vectors.append(oscillator_state(lat.ZERO,[(i,3)]))
    for i in range(2):
        for j in range(2):vectors.append(oscillator_state(lat.ZERO,[(i,2),(j,1)]))
    for ijk in combinations_with_replacement(range(2),3):vectors.append(oscillator_state(lat.ZERO,[(i,1) for i in ijk]))
    gamma=lat.plus(ALPHA,BETA)
    for a in (ALPHA,BETA,gamma,lat.neg(ALPHA),lat.neg(BETA),lat.neg(gamma)):
        for i in range(2):vectors.append(oscillator_state(a,[(i,1)]))
    V=np.column_stack(vectors);assert np.linalg.norm(V.conj().T@V-np.eye(22))<1e-12
    def mode_on(v,n):
        target=4-n;out=np.zeros(len(lat.BASES[target]),complex)
        for i,a in lat.vector_dict(pn).items():
            for j,b in lat.vector_dict(v).items():
                for s,c in g3.basis_mode(lat.BASES[2][i],n,lat.BASES[3][j]).items():out[lat.INDICES[target][s]]+=a*b*c
        return out
    image=np.column_stack([mode_on(v,1) for v in vectors]);matrix=V.conj().T@image
    assert np.linalg.norm(image-V@matrix)<1e-9
    ev,rot=eigh((matrix+matrix.conj().T)/2);E=V@rot[:,abs(ev-3)<1e-8]
    constraints=np.column_stack([mode_on(E[:,i],2) for i in range(E.shape[1])]);kernel=null_space(constraints,rcond=1e-9)
    w=E@kernel;assert w.shape[1]==1,w.shape
    frame=np.load('hi_cft_20260923_c8_grade3_span.npz')['weight_0_0'];ids=idx3[(0,0)]
    residual=w.copy();residual[ids]-=frame@(frame.conj().T@w[ids])
    out={'exact_axis_central_charge':'4/5','exact_axis_membership_in_S2':True,
         'exact_PCT_and_Virasoro_checks':True,'right_raising_and_lowering_current_p_weight':'1/15',
         'lattice_plane_Gram':[[x.dot(a,b) for b in (ALPHA,BETA)] for a in (ALPHA,BETA)],
         'plane_grade3_dimension':22,'p_weight3_multiplicity':int(E.shape[1]),'p_primary_weight3_multiplicity':1,
         'numerical_Potts_extension_vector_distance_from_S3':float(np.linalg.norm(residual)),
         'numerical_p3_w_norm':float(np.linalg.norm(mode_on(w[:,0],3))),
         'seconds':monotonic()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'The c=4/5 Virasoro subalgebra and its membership are exact. Membership of its weight-three Potts extension is only tested numerically here.',
         'source_sha256':{str(z):hashlib.sha256(z.read_bytes()).hexdigest() for z in (Path(__file__),Path(x.__file__),Path(ex.__file__),Path('hi_cft_20260923_c8_exact_fields.json'),Path('hi_cft_20260923_c8_grade3_span.npz'))}}
    path=Path('hi_cft_20260923_proof_potts.json');assert not path.exists();path.write_text(json.dumps(out,indent=2)+'\n')
    np.savez_compressed(path.with_suffix('.npz'),p=pn,w=w[:,0]);print(json.dumps(out),flush=True)

if __name__=='__main__':main()
