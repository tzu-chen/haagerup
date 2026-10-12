"""Lattice VOA E6+A2 through grade two; constructive floating controls.

All states use an orthonormal oscillator basis. Lattice momenta and the
cocycle are exact integers. Floating coefficients are exploratory, not a
replacement for a final exact VOA construction. Run only through safe_run.
"""
from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement
import argparse
import hashlib
import json
from math import factorial, sqrt
from pathlib import Path
import resource
import signal
from time import monotonic

import numpy as np
from scipy import sparse
from scipy.linalg import null_space, eigh

RANK=8
ZERO=(0,)*RANK
G=np.eye(RANK,dtype=int)*2
for i,j in ((0,1),(1,2),(2,3),(3,4),(2,5),(6,7)):
    G[i,j]=G[j,i]=-1
ROOT_COORD=np.linalg.cholesky(G.astype(float))
SIMPLE=[tuple(int(i==j) for i in range(RANK)) for j in range(RANK)]


def plus(a,b):return tuple(x+y for x,y in zip(a,b))
def neg(a):return tuple(-x for x in a)
def dot(a,b):return int(np.asarray(a,dtype=int)@G@np.asarray(b,dtype=int))
def norm(a):return dot(a,a)


@lru_cache(maxsize=8192)
def coordinates(a):return np.asarray(a)@ROOT_COORD


@lru_cache(maxsize=131072)
def cocycle(a,b):
    n=sum(a[i]*b[i] for i in range(RANK))
    n+=sum(a[i]*b[j]*int(G[i,j]) for i in range(RANK) for j in range(i))
    return -1 if n%2 else 1


def roots():
    result=set(SIMPLE); todo=list(SIMPLE)
    while todo:
        a=todo.pop()
        for i in range(RANK):
            b=list(a);b[i]-=dot(a,SIMPLE[i]);b=tuple(b)
            if b not in result:result.add(b);todo.append(b)
    assert len(result)==78 and all(norm(a)==2 for a in result)
    return sorted(result)


ROOTS=roots()
NORM4=sorted({plus(a,b) for a in ROOTS for b in ROOTS if dot(a,b)==0})
assert len(NORM4)==702


def osc_grade(osc):return sum(k//RANK+1 for k in osc)


@lru_cache(maxsize=512)
def osc_norm(osc):
    v=1
    for k,m in Counter(osc).items():v*=((k//RANK+1)**m)*factorial(m)
    return sqrt(v)


BASES={0:[(ZERO,())],1:[(ZERO,(i,)) for i in range(RANK)]+[(a,()) for a in ROOTS]}
BASES[2]=([(ZERO,(i+RANK,)) for i in range(RANK)]
          +[(ZERO,(i,j)) for i,j in combinations_with_replacement(range(RANK),2)]
          +[(a,(i,)) for a in ROOTS for i in range(RANK)]
          +[(a,()) for a in NORM4])
INDICES={n:{s:i for i,s in enumerate(b)} for n,b in BASES.items()}
assert [len(BASES[n]) for n in range(3)]==[1,86,1370]


def add_term(out,key,value):
    if abs(value)>1e-14:out[key]=out.get(key,0)+value


@lru_cache(maxsize=8192)
def creation(alpha,grade):
    a=coordinates(alpha)
    if grade==0:return (((),1.),)
    if grade==1:return tuple(((i,),a[i]) for i in range(RANK) if abs(a[i])>1e-14)
    assert grade==2
    v=[((i+RANK,),a[i]/2) for i in range(RANK) if abs(a[i])>1e-14]
    for i,j in combinations_with_replacement(range(RANK),2):
        x=a[i]*a[j]/(2 if i==j else 1)
        if abs(x)>1e-14:v.append(((i,j),x))
    return tuple(v)


@lru_cache(maxsize=80000)
def vertex_action(alpha,mode,state):
    """Coefficient of z^(-mode-1) in Y(e^alpha,z) on one Fock monomial."""
    beta,osc=state; gamma=plus(alpha,beta)
    target=norm(alpha)//2+norm(beta)//2+osc_grade(osc)-mode-1
    if target<0 or target>2:return ()
    final_osc=target-norm(gamma)//2
    if final_osc<0:return ()
    a=coordinates(alpha); out={}
    for mask in range(1<<len(osc)):
        remain=[];power=0;coefficient=cocycle(alpha,beta)/osc_norm(osc)
        for i,k in enumerate(osc):
            if mask>>i&1:
                coefficient*=-a[k%RANK];power-=k//RANK+1
            else:remain.append(k)
        if abs(coefficient)<1e-14:continue
        degree=-mode-1-dot(alpha,beta)-power
        if degree<0 or degree>2:continue
        for created,value in creation(alpha,degree):
            mon=tuple(sorted(tuple(remain)+created))
            if osc_grade(mon)!=final_osc:raise AssertionError('Vertex grading')
            add_term(out,(gamma,mon),coefficient*value*osc_norm(mon))
    return tuple((s,v) for s,v in out.items() if abs(v)>1e-13)


def heisenberg_action(direction,mode,state):
    beta,osc=state; out={}
    if mode==0:
        add_term(out,state,np.dot(direction,coordinates(beta)))
    elif mode<0:
        for i,c in enumerate(direction):
            k=(-mode-1)*RANK+i
            mon=tuple(sorted(osc+(k,)))
            add_term(out,(beta,mon),c*osc_norm(mon)/osc_norm(osc))
    else:
        counts=Counter(osc)
        for k,m in counts.items():
            if k//RANK+1!=mode:continue
            rem=list(osc);rem.remove(k);rem=tuple(rem)
            add_term(out,(beta,rem),direction[k%RANK]*mode*m*osc_norm(rem)/osc_norm(osc))
    return out.items()


def current_action(current,mode,state):
    out={}
    for i,c in current.items():
        alpha,osc=BASES[1][i]
        if alpha==ZERO:
            h=np.zeros(RANK);h[osc[0]]=1
            terms=heisenberg_action(h,mode,state)
        else:terms=vertex_action(alpha,mode,state)
        for s,v in terms:add_term(out,s,c*v)
    return out


def vector_dict(v,tol=1e-12):return {i:complex(c) for i,c in enumerate(v) if abs(c)>tol}


def current_matrix(current,mode,grade):
    target=grade-mode
    assert target in BASES
    rows=[];cols=[];data=[]
    for j,state in enumerate(BASES[grade]):
        for s,v in current_action(current,mode,state).items():
            if s not in INDICES[target]:raise AssertionError(('Missing state',mode,grade,s))
            rows.append(INDICES[target][s]);cols.append(j);data.append(v)
    out=sparse.csc_matrix((data,(rows,cols)),shape=(len(BASES[target]),len(BASES[grade])),dtype=complex)
    out.eliminate_zeros()
    return out


def cartan(a):
    return {INDICES[1][ZERO,(i,)]:complex(c) for i,c in enumerate(coordinates(a)) if abs(c)>1e-13}


def root_current(a,c=1):return {INDICES[1][a,()]:complex(c)}


def sum_currents(*terms):
    out={}
    for factor,cur in terms:
        for i,v in cur.items():add_term(out,i,factor*v)
    return out


def principal(indices,coefficients):
    e=sum_currents(*[(sqrt(c),root_current(SIMPLE[i])) for i,c in zip(indices,coefficients)])
    f=sum_currents(*[(-sqrt(c),root_current(neg(SIMPLE[i]))) for i,c in zip(indices,coefficients)])
    h=cartan(tuple(sum(c*SIMPLE[i][j] for i,c in zip(indices,coefficients)) for j in range(RANK)))
    return h,e,f


A0=(-1,-2,-3,-2,-1,-2,0,0)
KLEFT=(cartan(A0),root_current(A0),root_current(neg(A0),-1))
KA5=principal(range(5),(5,8,9,8,5))
KA2=principal((6,7),(2,2))
KRIGHT=tuple(sum_currents((1,a),(1,b)) for a,b in zip(KA5,KA2))


def max_abs(matrix):
    if sparse.issparse(matrix):return float(np.max(np.abs(matrix.data))) if matrix.nnz else 0.
    return float(np.max(np.abs(matrix))) if matrix.size else 0.


def controls():
    worst=0.
    for a in ROOTS:
        assert cocycle(a,neg(a))==-1
        for b in ROOTS:
            assert cocycle(a,b)*cocycle(b,a)==(-1 if dot(a,b)%2 else 1)
    for cur,level in ((KLEFT,1),(KA5,35),(KA2,4),(KRIGHT,39)):
        h,e,f=cur
        matrices=[current_matrix(c,0,1) for c in cur]
        H,E,F=matrices
        for residual in (H@E-E@H-2*E,H@F-F@H+2*F,E@F-F@E-H,E.getH()-F,H.getH()-H):
            worst=max(worst,max_abs(residual))
        hv=np.zeros(86,complex);ev=hv.copy();fv=hv.copy()
        for v,c in ((hv,h),(ev,e),(fv,f)):
            for i,z in c.items():v[i]=z
        assert abs(np.vdot(hv,hv)-2*level)<1e-10
        assert abs(np.vdot(ev,ev)-level)<1e-10
        worst=max(worst,max_abs(current_matrix(e,1,2)-current_matrix(f,-1,1).getH()))
    assert worst<1e-10,worst
    return {'ambient_dimensions':[len(BASES[n]) for n in range(3)],'roots':78,'norm4_vectors':702,
            'cocycle_commutators_exact':True,'current_algebra_and_adjoint_max_error':worst}


def highest_spaces():
    currents=KLEFT+KRIGHT
    matrices0=[current_matrix(c,0,2) for c in currents]
    matrices1=[current_matrix(c,1,2) for c in currents]
    hleft=np.rint(matrices0[0].diagonal().real).astype(int)
    hright=np.rint(matrices0[3].diagonal().real).astype(int)
    assert max_abs(matrices0[0]-sparse.diags(hleft))<1e-10
    assert max_abs(matrices0[3]-sparse.diags(hright))<1e-10
    from hi_cft_third_gamma0_grade2_check import ambient
    caps=ambient(1,39)[3]
    spaces={};records=[]
    for (n,m),expected in sorted(caps.items()):
        columns=np.flatnonzero((hleft==n-1)&(hright==m-1))
        constraints=sparse.vstack([matrices0[1][:,columns],matrices0[4][:,columns]]+[v[:,columns] for v in matrices1]).tocsr()
        constraints=constraints[np.unique(constraints.nonzero()[0]),:].toarray()
        u=null_space(constraints,rcond=1e-11)
        assert u.shape[1]==expected,((n,m),u.shape,expected)
        full=np.zeros((1370,expected),complex);full[columns]=u
        spaces[n,m]=full
        records.append({'dimensions':[n,m],'ambient_multiplicity':expected,'weight_space_dimension':len(columns),
                        'kernel_max_residual':max_abs(constraints@u)})
    return spaces,records


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);args=ap.parse_args()
    path=Path(args.output);assert not path.exists()
    cap=resource.getrlimit(resource.RLIMIT_AS)[0];assert 0<cap<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second computation cap')))
    signal.alarm(600);start=monotonic()
    out=controls();print(out,flush=True)
    spaces,records=highest_spaces();out['host125_affine_primary_spaces']=records
    archive=path.with_suffix('.npz');assert not archive.exists()
    np.savez_compressed(archive,**{f'hw_{n}_{m}':u for (n,m),u in spaces.items()})
    out.update(seconds=monotonic()-start,peak_rss_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
               source_sha256={__file__:hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},
               scope='Explicit ambient lattice states and affine highest vectors. No Haagerup VOA or OPE closure claimed.')
    path.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n');print(json.dumps(out,indent=2),flush=True)


if __name__=='__main__':main()
