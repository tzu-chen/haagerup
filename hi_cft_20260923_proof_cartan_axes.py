"""Search for a rational conformal core in the Cartan commutant.

This exploratory search is not an exhaustive classification of axes.
"""
import hashlib,json,resource,signal
from pathlib import Path
from time import monotonic
from fractions import Fraction
import numpy as np
from scipy.linalg import null_space
from scipy.optimize import root
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_ope as ope

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second cap')));signal.alarm(600)
    start=monotonic();source=Path('hi_cft_20260923_c8_fields_precise.npz');W=np.load(source)['W2']
    constraints=np.vstack([lat.current_matrix(h,n,2)@W for h in (lat.KLEFT[0],lat.KRIGHT[0]) for n in (0,1,2)])
    C=ope.real_form(W@null_space(constraints,rcond=1e-10));d=C.shape[1];assert d==7,d
    g=np.zeros((d,d,d));leak=0.
    for i in range(d):
        for j in range(i,d):
            v=ope.mode_action(C[:,i],1,C[:,j]);c=C.conj().T@v
            leak=max(leak,np.linalg.norm(v-C@c),np.max(abs(c.imag)));g[:,i,j]=g[:,j,i]=c.real
    print({'commutant_dimension':d,'Griess_closure_residual':leak,'seconds':monotonic()-start},flush=True)
    assert leak<1e-8
    omega=ope.ambient_stress()
    for h,k in ((lat.KLEFT[0],1),(lat.KRIGHT[0],39)):
        omega-=lat.current_matrix(h,-1,1)@ope.current_vector(h)/(4*k)
    t=(C.conj().T@omega).real;assert np.linalg.norm(omega-C@t)<1e-10
    assert abs(2*np.dot(t,t)-6)<1e-10
    def product(a,b):return np.einsum('kij,i,j->k',g,a,b)
    def residual(a):return product(a,a)-2*a
    def jac(a):return 2*np.einsum('kij,i->kj',g,a)-2*np.eye(d)
    rng=np.random.default_rng(230926);axes=[np.zeros(d),t]
    for trial in range(2000):
        seed=t/2+rng.normal(size=d)*(.3+(trial%8)*.3)
        sol=root(residual,seed,jac=jac,tol=1e-11)
        if np.linalg.norm(residual(sol.x))<1e-8 and all(np.linalg.norm(sol.x-a)>1e-6 for a in axes):axes.append(sol.x)
    charges=[2*np.dot(a,a) for a in axes]
    rows=[{'central_charge':float(c),'rational_guess':str(Fraction(float(c)).limit_denominator(20000)),
           'coordinates':a.tolist(),'idempotency_residual':float(np.linalg.norm(residual(a)))} for a,c in sorted(zip(axes,charges),key=lambda ac:ac[1])]
    path=Path('hi_cft_20260923_proof_cartan_axes.json');assert not path.exists()
    out={'dimension':d,'total_central_charge':6,'Griess_closure_residual':float(leak),
         'search_trials':2000,'located_axes':rows,'exhaustive':False,'seconds':monotonic()-start,
         'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'Numerical search for Virasoro axes in the seven-dimensional Cartan-commutant Griess algebra; no rationality claim.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(lat.__file__),Path(ope.__file__),source)}}
    path.write_text(json.dumps(out,indent=2)+'\n');np.savez_compressed(path.with_suffix('.npz'),basis=C,product=g,total=t,axes=np.array(axes))
    print({'axes':len(axes),'charges':sorted(float(c) for c in charges),'seconds':out['seconds']},flush=True)

if __name__=='__main__':main()
