"""Test whether the c=8/5 axis is a level-13 parafermion in E8_1.

The E8 cocycle is explicitly gauge-matched to the existing E6+A2 basis.
This exploratory producer uses only 248-dimensional current matrices.
"""
import json,resource,signal
from pathlib import Path
from fractions import Fraction
from collections import Counter
import numpy as np
import sympy as sp
import hi_cft_20260923_c8_lattice as lat

def setup():
    G=sp.Matrix(lat.G.tolist());lam=G.inv()[:,0]+G.inv()[:,6]
    M=sp.eye(8);M[7,:]=lam.T;N=M.inv();GN=M*G*M.T
    assert M.det()==sp.Rational(1,3) and GN.det()==1
    assert all(x.q==1 for x in GN)
    old=np.tril(np.array(G).astype(int));np.fill_diagonal(old,1)
    new=np.tril(np.array(GN).astype(int));np.fill_diagonal(new,np.diag(np.array(GN).astype(int))//2)
    N=np.array(N).astype(int);Q=N@new@N.T-old
    assert not np.any((Q-Q.T)%2)
    def gauge(a):
        a=np.array(a,dtype=int);v=sum(Q[i,i]*a[i]*(a[i]-1)//2 for i in range(8))+sum(Q[i,j]*a[i]*a[j] for i in range(8) for j in range(i+1,8))
        return (-1)**int(v%2)
    def coords(a):
        q=sp.Matrix([list(a)])*sp.Matrix(N);assert all(x.q==1 for x in q)
        return np.array(list(q)).astype(int)
    def cocycle(a,b):return (-1)**int((coords(a)@new@coords(b))%2)
    roots=set(map(tuple,lat.ROOTS));todo=[tuple(lam)];coset=set(todo)
    while todo:
        a=todo.pop()
        for i in range(8):
            m=sum(a[j]*int(lat.G[j,i]) for j in range(8));b=list(a);b[i]-=m;b=tuple(b)
            if b not in coset:coset.add(b);todo.append(b)
    assert len(coset)==81
    roots|=coset|{tuple(-v for v in a) for a in coset};roots=sorted(roots);assert len(roots)==240
    return roots,gauge,cocycle

def main():
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError()));signal.alarm(180)
    roots,gauge,cocycle=setup();lookup={a:i for i,a in enumerate(roots)}
    D=np.load('hi_cft_20260923_proof_cartan_axes.npz');cs=2*np.sum(D['axes']**2,axis=1);axis=D['basis']@D['axes'][np.argmin(abs(cs-1.6))]
    entries=[(lat.BASES[2][i],v) for i,v in enumerate(axis) if abs(v)>1e-10]
    A=np.zeros((240,240),complex)
    for j,beta in enumerate(roots):
        b=np.array(beta,dtype=float)@lat.ROOT_COORD
        for (a,osc),v in entries:
            if a==lat.ZERO:
                if len(osc)==1:A[j,j]-=v*b[osc[0]%8]
                else:A[j,j]+=v*b[osc[0]]*b[osc[1]]/lat.osc_norm(osc)
            elif sum(a[i]*int(lat.G[i,k])*beta[k] for i in range(8) for k in range(8))==-2:
                dest=tuple(a[i]+beta[i] for i in range(8));A[lookup[dest],j]+=v*gauge(a)*cocycle(a,beta)
    # A non-orthonormal cocycle gauge can make the adjoint signs differ by root.
    # All lattice root vectors nevertheless have unit positive Hermitian norm.
    assert np.linalg.norm(A-A.conj().T)<1e-8,np.linalg.norm(A-A.conj().T)
    ev,V=np.linalg.eigh(A);target=abs(ev-12/13)<1e-8
    out={'axis_c':1.6,'E8_root_count':240,'target_parafermion_EF_weight':'12/13',
         'target_multiplicity':int(sum(target)),
         'spectrum':dict(Counter(str(Fraction(float(t)).limit_denominator(10000)) for t in ev)),
         'hermiticity_error':float(np.linalg.norm(A-A.conj().T))}
    p=Path('hi_cft_20260923_proof_e8_pf13.json');assert not p.exists();p.write_text(json.dumps(out,indent=2)+'\n')
    np.savez_compressed(p.with_suffix('.npz'),eigenvectors=V[:,target],roots=np.array(roots,dtype=float),axis=axis)
    print(json.dumps(out),flush=True)

if __name__=='__main__':main()
