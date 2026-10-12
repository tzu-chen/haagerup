"""Locate actual c=8 candidate fields by current OPE compatibility.

Nine real angles remain in a constructive, spectrally selected ansatz.
All failures are numerical search outcomes, not nonexistence proofs.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import sqrt
from pathlib import Path
import resource
import signal
from time import monotonic

import numpy as np
from scipy import sparse
from scipy.linalg import null_space
from scipy.optimize import least_squares

import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_ope as ope


SPECS=[(1,5,798,2),(1,9,200,2),(1,9,1512,2),(1,13,420,2),
       (2,2,192,2),(2,6,1830,2),(2,8,752,3),(2,14,180,2)]


def lower_to_bottom(v,n,m,FL,FR):
    for j in range(n-1):v=FL@v/sqrt((n-1-j)*(j+1))
    for j in range(m-1):v=FR@v/sqrt((m-1-j)*(j+1))
    return v


def real_highest(U,n,m,FL,FR):
    def tau(v):return ope.conjugate(lower_to_bottom(v,n,m,FL,FR),2)
    ans=[]
    for j in range(U.shape[1]):
        v=U[:,j];w=tau(v)
        for q in ((v+w)/2,(v-w)/(2j)):
            for a in ans:q=q-np.vdot(a,q)*a
            z=np.linalg.norm(q)
            if z>1e-9:ans.append(q/z)
    R=np.column_stack(ans)
    assert R.shape==U.shape,(R.shape,U.shape)
    assert max(np.linalg.norm(tau(R[:,j])-R[:,j]) for j in range(R.shape[1]))<1e-8
    return R


def descendants(U,n,m,FL,FR):
    rows=[];left=U
    for i in range(n):
        right=left
        for j in range(m):
            rows.append(right)
            if j+1<m:right=FR@right/sqrt((m-1-j)*(j+1))
        if i+1<n:left=FL@left/sqrt((n-1-i)*(i+1))
    return np.column_stack(rows)


def affine_vacuum():
    currents=lat.KLEFT+lat.KRIGHT
    v=[]
    for c in currents:v.append(np.asarray(lat.current_matrix(c,-2,0).todense())[:,0])
    for c in currents:
        a=lat.current_matrix(c,-1,1)
        for d in currents:v.append(a@ope.current_vector(d))
    u,s,_=np.linalg.svd(np.column_stack(v),full_matrices=False)
    assert sum(s>1e-9)==22
    return u[:,:22]


def b_highest():
    from hi_cft_third_gamma0_grade2_check import B80
    currents=lat.KLEFT+lat.KRIGHT
    M=[lat.current_matrix(c,0,1) for c in currents]
    P=[lat.current_matrix(c,1,1) for c in currents]
    h1=np.rint(M[0].diagonal().real).astype(int);h2=np.rint(M[3].diagonal().real).astype(int)
    vectors=[];labels=[]
    for (n,m),count in sorted(B80[1,39].items()):
        cols=np.flatnonzero((h1==n-1)&(h2==m-1))
        A=sparse.vstack([M[1][:,cols],M[4][:,cols]]+[p[:,cols] for p in P]).toarray()
        u=null_space(A,rcond=1e-10);assert u.shape[1]==count,((n,m),u.shape,count)
        for j in range(count):
            full=np.zeros(86,complex);full[cols]=u[:,j]
            vectors.append(full);labels.append([n,m,j])
    assert len(vectors)==9
    return vectors,labels


def prepare(source):
    data=json.loads(source.read_text());saved=np.load(source.with_suffix('.npz'))
    e=saved['stress'];total=ope.ambient_stress()-ope.sugawara(lat.KLEFT,1)-ope.sugawara(lat.KRIGHT,39)
    fixed=np.column_stack((affine_vacuum(),e/sqrt(1200/1271),(total-e)/sqrt(35/31)))
    FL=lat.current_matrix(lat.KLEFT[2],0,2);FR=lat.current_matrix(lat.KRIGHT[2],0,2)
    parts=[fixed];records=[];omega=ope.ambient_stress()
    for n,m,value,degree in SPECS:
        row=next(r for r in data['primary_spectra'] if r['dimensions']==[n,m])
        ev=np.array(row['e_weights']);columns=np.flatnonzero(abs(ev-value/1271)<1e-8)
        assert len(columns)==degree
        U=saved[f'eig_{n}_{m}'][:,columns]
        U=real_highest(U,n,m,FL,FR)
        errors=[np.linalg.norm(ope.mode_action(stress,2,U[:,j])) for stress in (e,omega) for j in range(degree)]
        assert max(errors)<1e-8,((n,m),errors)
        D=descendants(U,n,m,FL,FR);parts.append(D)
        records.append({'dimensions':[n,m],'e_weight':str(Q(value,1271)),
                        'real_multiplicity':degree,'positive_mode_max_residual':max(errors)})
    C=np.column_stack(parts)
    assert C.shape==(1370,232)
    assert lat.max_abs(C.conj().T@C-np.eye(232))<1e-8
    b,labels=b_highest();operators=[]
    for v in b:
        M=lat.current_matrix(lat.vector_dict(v),0,2)
        operators.append(C.conj().T@(M@C))
    operators=np.asarray(operators)
    return C,operators,records,labels


def frame(theta):
    F=np.zeros((232,120));F[:24,:24]=np.eye(24)
    derivatives=[];ir=24;ic=24;ip=0
    for n,m,_,degree in SPECS:
        if degree==2:
            a=theta[ip];v=np.array([np.cos(a),np.sin(a)])
            ds=[np.array([-np.sin(a),np.cos(a)])]
        else:
            a,b=theta[ip:ip+2]
            v=np.array([np.sin(a)*np.cos(b),np.sin(a)*np.sin(b),np.cos(a)])
            ds=[np.array([np.cos(a)*np.cos(b),np.cos(a)*np.sin(b),-np.sin(a)]),
                np.array([-np.sin(a)*np.sin(b),np.sin(a)*np.cos(b),0.])]
        size=n*m;F[ir:ir+size*degree,ic:ic+size]=np.kron(np.eye(size),v[:,None])
        for d in ds:
            D=np.zeros_like(F);D[ir:ir+size*degree,ic:ic+size]=np.kron(np.eye(size),d[:,None]);derivatives.append(D)
        ir+=size*degree;ic+=size;ip+=len(ds)
    assert (ir,ic,ip)==(232,120,9)
    return F,np.asarray(derivatives)


def run_search(operators,starts,max_nfev):
    rng=np.random.default_rng(83154);history=[];best=None
    # A tiny fixed projection produces a fast square-ish fitting problem.
    # Its prospective solutions must then pass the entire original residual.
    size=9*120*120
    selected=rng.choice(size,size=1600,replace=False)
    def all_values(theta,derivative=False):
        F,D=frame(theta);MF=operators@F
        values=F.T@MF
        if not derivative:return values
        jac=[]
        for d in D:jac.append(d.T@MF+F.T@(operators@d))
        return values,np.stack(jac,axis=-1)
    def fun(x):
        z=all_values(x).reshape(-1)[selected]
        return np.concatenate((z.real,z.imag))
    def jac(x):
        _,z=all_values(x,True);z=z.reshape(size,9)[selected]
        return np.concatenate((z.real,z.imag),axis=0)
    x=rng.normal(size=9)
    # Analytic derivative against an independent directional difference.
    direction=rng.normal(size=9);eps=1e-6
    error=np.max(abs(jac(x)@direction-(fun(x+eps*direction)-fun(x-eps*direction))/(2*eps)))
    assert error<1e-6,error
    for attempt in range(starts):
        initial=rng.uniform(-np.pi,np.pi,size=9)
        sol=least_squares(fun,initial,jac=jac,max_nfev=max_nfev,gtol=1e-11,ftol=1e-12,xtol=1e-12)
        full=all_values(sol.x);value=float(np.linalg.norm(full))
        row={'attempt':attempt,'projected_residual':float(np.linalg.norm(sol.fun)),
             'full_residual':value,'full_max_entry':lat.max_abs(full),'nfev':sol.nfev,'optimality':float(sol.optimality)}
        history.append(row);print(row,flush=True)
        if best is None or value<best['residual']:best={'residual':value,'theta':sol.x,'max_entry':lat.max_abs(full)}
        if value<1e-8:break
    return best,history,error


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',default='hi_cft_20260923_c8_ope_control.json')
    ap.add_argument('--output',required=True);ap.add_argument('--starts',type=int,default=12)
    ap.add_argument('--max-nfev',type=int,default=200);args=ap.parse_args()
    path=Path(args.output);assert not path.exists()
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second computation cap')))
    signal.alarm(600);start=monotonic()
    C,M,records,labels=prepare(Path(args.source))
    print({'field_pool':C.shape,'b_current_matrices':M.shape,'preparation_seconds':monotonic()-start},flush=True)
    best,history,error=run_search(M,args.starts,args.max_nfev)
    F,_=frame(best['theta']);W=C@F
    archive=path.with_suffix('.npz');assert not archive.exists()
    np.savez_compressed(archive,field_pool=C,b_current_matrices=M,theta=best['theta'],W2=W,frame=F)
    sources=[Path(__file__),Path(lat.__file__),Path(ope.__file__),Path(args.source),Path(args.source).with_suffix('.npz')]
    out={'field_multiplicities':records,'b_highest_labels':labels,'best_full_current_residual':best['residual'],
         'best_full_current_max_entry':best['max_entry'],'theta':best['theta'].tolist(),'search_history':history,
         'analytic_jacobian_directional_error':error,'seconds':monotonic()-start,
         'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
         'scope':'Constructive low-grade current-OPE fit in one explicit spectral ansatz. A failed fit is not an exclusion; passing would still require weight-two OPE closure and higher sewing.'}
    path.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n')
    print(json.dumps({'output':str(path),'full_residual':best['residual'],'seconds':out['seconds']}),flush=True)


if __name__=='__main__':main()
