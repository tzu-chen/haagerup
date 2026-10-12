"""Bounded generator closure through ambient weight four, numerically.

All actions are streamed in Cartan blocks. This gives a finite truncation
of the generated algebra, not an all-weight properness proof.
"""
import argparse,hashlib,json,resource,signal
from collections import Counter,deque
from functools import lru_cache
from math import ceil,floor,sqrt,factorial
from pathlib import Path
from time import monotonic
import numpy as np
from scipy import sparse
from scipy.linalg import svd
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_ope as ope
import hi_cft_20260923_c8_grade3 as old
import hi_cft_20260923_c8_grade3_action as action3

@lru_cache(maxsize=8)
def oscillators(g):
    out=[]
    def rec(rem,start,items):
        if rem==0:out.append(tuple(items));return
        for k in range(start,8*g):
            n=k//8+1
            if n>rem:break
            rec(rem-n,k,items+[k])
    rec(g,0,[]);return tuple(out)

def momenta(n):
    result=[];a=np.zeros(8,dtype=int);R=lat.ROOT_COORD
    def visit(j,remaining):
        if j<0:
            if lat.norm(tuple(a))==n:result.append(tuple(int(x) for x in a))
            return
        shift=np.dot(a[j+1:],R[j+1:,j]);rad=sqrt(max(0,remaining))
        for v in range(ceil((-rad-shift)/R[j,j]-1e-9),floor((rad-shift)/R[j,j]+1e-9)+1):
            a[j]=v;rest=remaining-(v*R[j,j]+shift)**2
            if rest>=-1e-8:visit(j-1,rest)
    visit(7,float(n));return sorted(set(result))

@lru_cache(maxsize=4096)
def creation(alpha,g):
    a=lat.coordinates(alpha);out=[]
    for osc in oscillators(g):
        c=1.
        for k,m in Counter(osc).items():c*=a[k%8]**m/((k//8+1)**m*factorial(m))
        if abs(c)>1e-14:out.append((osc,c))
    return tuple(out)

@lru_cache(maxsize=10000)
def vertex(alpha,mode,state):
    beta,osc=state;gamma=lat.plus(alpha,beta)
    target=lat.norm(alpha)//2+lat.norm(beta)//2+lat.osc_grade(osc)-mode-1
    if not 0<=target<=4 or target<lat.norm(gamma)//2:return ()
    a=lat.coordinates(alpha);out={}
    for mask in range(1<<len(osc)):
        remain=[];power=0;c=lat.cocycle(alpha,beta)/lat.osc_norm(osc)
        for i,k in enumerate(osc):
            if mask>>i&1:c*=-a[k%8];power-=k//8+1
            else:remain.append(k)
        if abs(c)<1e-14:continue
        degree=-mode-1-lat.dot(alpha,beta)-power
        if not 0<=degree<=4:continue
        for created,d in creation(alpha,degree):
            mon=tuple(sorted(tuple(remain)+created))
            assert lat.osc_grade(mon)+lat.norm(gamma)//2==target
            lat.add_term(out,(gamma,mon),c*d*lat.osc_norm(mon))
    return tuple(out.items())

def weights(grade):
    c=np.array((5,8,9,8,5,0,2,2));a=np.array(lat.A0)
    values=np.array([(lat.dot(tuple(a),s[0]),lat.dot(tuple(c),s[0])) for s in lat.BASES[grade]])
    return {w:np.flatnonzero(np.all(values==w,axis=1)) for w in set(map(tuple,values))}

def pure_matrix(u,n,grade):
    target=grade+1-n;rows=[];cols=[];vals=[]
    for j,state in enumerate(lat.BASES[grade]):
        for alpha,c in u.items():
            for s,d in vertex(alpha,n,state):rows.append(lat.INDICES[target][s]);cols.append(j);vals.append(c*d)
    return sparse.csc_matrix((vals,(rows,cols)),shape=(len(lat.BASES[target]),len(lat.BASES[grade])))

def translation(grade):
    rows=[];cols=[];vals=[]
    for j,(alpha,osc) in enumerate(lat.BASES[grade]):
        out={}
        for s,c in lat.heisenberg_action(lat.coordinates(alpha),-1,(alpha,osc)):lat.add_term(out,s,c)
        for k,m in Counter(osc).items():
            rem=list(osc);rem.remove(k);rem.append(k+8);rem=tuple(sorted(rem))
            lat.add_term(out,(alpha,rem),m*(k//8+1)*lat.osc_norm(rem)/lat.osc_norm(osc))
        for s,c in out.items():rows.append(lat.INDICES[grade+1][s]);cols.append(j);vals.append(c)
    return sparse.csc_matrix((vals,(rows,cols)),shape=(len(lat.BASES[grade+1]),len(lat.BASES[grade])))

class Span:
    def __init__(self,idx,tol):
        self.idx=idx;self.Q={w:np.zeros((len(i),0),complex) for w,i in idx.items()}
        self.todo=deque();self.dimension=0;self.tol=tol;self.accepted=[];self.rejected=[]
    def add(self,w,M):
        if not M.size:return
        if M.ndim==1:M=M[:,None]
        size=np.linalg.norm(M)
        if size<1e-12:return
        R=M.copy();Q=self.Q[w]
        for _ in range(2):R-=Q@(Q.conj().T@R)
        left,s,_=svd(R,full_matrices=False,check_finite=False)
        keep=s>self.tol*max(1,size)
        self.accepted.extend((s[keep]/max(1,size)).tolist());self.rejected.extend((s[~keep]/max(1,size)).tolist())
        if np.any(keep):
            new=left[:,keep];self.Q[w]=np.column_stack((Q,new));self.todo.append((w,new));self.dimension+=new.shape[1]
            assert self.dimension<=7000,('rank cap',self.dimension)
    def image(self,M,source,source_idx,shift):
        for w,Q in source.items():
            target=(w[0]+shift[0],w[1]+shift[1])
            if target in self.idx:self.add(target,M[self.idx[target]][:,source_idx[w]]@Q)
    def close(self,ops):
        count=0
        while self.todo:
            w,Q=self.todo.popleft();count+=Q.shape[1]
            for M,shift in ops:
                target=(w[0]+shift[0],w[1]+shift[1])
                if target in self.idx:self.add(target,M[self.idx[target]][:,self.idx[w]]@Q)
        return count

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);ap.add_argument('--tol',type=float,default=1e-7);args=ap.parse_args()
    path=Path(args.output);assert not path.exists()
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=3*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('900-second cap')));signal.alarm(900)
    start=monotonic();idx3=action3.setup();n6=old.momenta6();n8=momenta(8)
    lat.BASES[4]=[(a,o) for norm,aa in ((0,[lat.ZERO]),(2,lat.ROOTS),(4,lat.NORM4),(6,n6),(8,n8)) for a in aa for o in oscillators(4-norm//2)]
    assert len(lat.BASES[4])==71052 and len(n8)==5694
    lat.INDICES[4]={s:i for i,s in enumerate(lat.BASES[4])};lat.creation=creation;lat.vertex_action=vertex
    idx4=weights(4);idx2=weights(2)
    saved=np.load('hi_cft_20260923_c8_grade3_span.npz');S3={tuple(map(int,key.split('_')[1:])):saved[key] for key in saved.files}
    W=np.load('hi_cft_20260923_c8_fields_precise.npz')['W2'];S2={}
    for w,idx in idx2.items():
        q,s,_=svd(W[idx],full_matrices=False);keep=s>1e-8
        if any(keep):S2[w]=q[:,keep]
    a=(0,0,0,0,0,-1,1,1);b=(0,0,0,1,1,-1,0,0);c=(1,1,0,0,0,-1,0,0)
    z=(sqrt(13)+3j*sqrt(3))/sqrt(40);u={a:1.,b:z,c:z.conjugate()}
    span=Span(idx4,args.tol);history=[]
    def record(stage):
        row={'stage':stage,'dimension':span.dimension,'seconds':monotonic()-start,
             'accepted_min':min(span.accepted,default=0),'rejected_max':max(span.rejected,default=0),
             'orthogonality_error':max((np.linalg.norm(Q.conj().T@Q-np.eye(Q.shape[1])) for Q in span.Q.values()),default=0)}
        history.append(row);print(row,flush=True)
    print({'ambient':len(lat.BASES[4]),'max_Cartan_block':max(map(len,idx4.values()))},flush=True)
    currents=lat.KLEFT+lat.KRIGHT;shifts=((0,0),(2,0),(-2,0),(0,0),(0,2),(0,-2))
    for cur,shift in zip(currents,shifts):span.image(lat.current_matrix(cur,-1,3),S3,idx3,shift)
    span.image(translation(3),S3,idx3,(0,0));record('current_and_translation_descendants')
    F=[(lat.current_matrix(currents[i],0,4),shifts[i]) for i in (2,5)]
    span.close(F);record('current_lowering_closure')
    span.image(pure_matrix(u,-1,2),S2,idx2,(1,13));span.close(F);record('normal_ordered_u_S2')
    span.image(pure_matrix(u,0,3),S3,idx3,(1,13));span.close(F);record('u_zero_S3')
    Uzero=pure_matrix(u,1,4)
    for w,Q in list(span.Q.items()):
        if Q.shape[1]:span.todo.append((w,Q))
    span.close(F+[(Uzero,(1,13))]);record('generator_zero_mode_closure')
    # Lowering u modes must preserve the earlier proposed spaces.
    leakage=[];K=np.linalg.qr(np.column_stack([ope.current_vector(c) for c in currents]))[0]
    for mode in (2,3,4):
        M=pure_matrix(u,mode,4);total=0.;size=0.;peak=0.
        for w,Q in span.Q.items():
            if not Q.shape[1]:continue
            target=(w[0]+1,w[1]+13);v=M[:,idx4[w]]@Q
            if mode==2:
                r=v.copy()
                if target in S3:
                    ind=idx3[target];q=S3[target];r[ind]-=q@(q.conj().T@v[ind])
            else:
                q=W if mode==3 else K;r=v-q@(q.conj().T@v)
            nr=np.linalg.norm(r);nv=np.linalg.norm(v);total+=nr*nr;size+=nv*nv;peak=max(peak,nr/max(1,nv))
        leakage.append({'mode':mode,'total_leakage':sqrt(total),'total_image_norm':sqrt(size),'max_relative_block_leakage':peak})
        print(leakage[-1],flush=True)
    out={'ambient_grade4':71052,'finite_truncation_grade4_dimension':span.dimension,'Haagerup_target':6010,
         'history':history,'lowering_checks':leakage,'tolerance':args.tol,
         'minimum_accepted_relative_singular_value':min(span.accepted),'maximum_rejected_relative_singular_value':max(span.rejected,default=0),
         'weight_multiplicities':{f'{w[0]},{w[1]}':Q.shape[1] for w,Q in span.Q.items() if Q.shape[1]},
         'seconds':monotonic()-start,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'Numerical closure under the specified generator modes through grade four; higher intermediate grades remain untested.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(lat.__file__),Path(old.__file__),Path('hi_cft_20260923_c8_grade3_span.npz'),Path('hi_cft_20260923_c8_fields_precise.npz'))}}
    path.write_text(json.dumps(out,indent=2)+'\n')
    np.savez_compressed(path.with_suffix('.npz'),**{f'weight_{w[0]}_{w[1]}':Q for w,Q in span.Q.items() if Q.shape[1]})
    print({'output':str(path),'seconds':out['seconds']},flush=True)

if __name__=='__main__':main()
