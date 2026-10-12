"""Numerical grade-three span of the explicit weight-one/two generators.

Products u_0 v and affine descendants are followed by finite-current
closure. This is a finite-grade span test, not an all-grade VOA character.
"""
import argparse,hashlib,json,resource,signal
from collections import Counter,deque
from functools import lru_cache
from itertools import combinations_with_replacement
from math import factorial,ceil,floor,sqrt
from pathlib import Path
from time import monotonic
import numpy as np
from scipy import sparse
import hi_cft_20260923_c8_lattice as lat
import hi_cft_20260923_c8_ope as ope
import hi_cft_20260923_c8_fields as fields

def momenta6():
    result=[];a=np.zeros(8,dtype=int);R=lat.ROOT_COORD
    def visit(j,remaining):
        if j<0:
            if lat.norm(tuple(a))==6:result.append(tuple(int(x) for x in a))
            return
        shift=np.dot(a[j+1:],R[j+1:,j]);rad=sqrt(max(0,remaining))
        for v in range(ceil((-rad-shift)/R[j,j]-1e-9),floor((rad-shift)/R[j,j]+1e-9)+1):
            a[j]=v;rest=remaining-(v*R[j,j]+shift)**2
            if rest>=-1e-8:visit(j-1,rest)
    visit(7,6.)
    return sorted(set(result))

OLD_CREATION=lat.creation
@lru_cache(maxsize=8192)
def creation(alpha,g):
    if g<3:return OLD_CREATION(alpha,g)
    assert g==3;a=lat.coordinates(alpha);out=[]
    for i in range(8):
        if abs(a[i])>1e-14:out.append(((i+16,),a[i]/3))
        for j in range(8):
            c=a[i]*a[j]/2
            if abs(c)>1e-14:out.append((tuple(sorted((i+8,j))),c))
    for osc in combinations_with_replacement(range(8),3):
        c=np.prod(a[list(osc)])
        for m in Counter(osc).values():c/=factorial(m)
        if abs(c)>1e-14:out.append((osc,c))
    return tuple(out)

@lru_cache(maxsize=80000)
def vertex(alpha,mode,state):
    beta,osc=state;gamma=lat.plus(alpha,beta)
    target=lat.norm(alpha)//2+lat.norm(beta)//2+lat.osc_grade(osc)-mode-1
    if not 0<=target<=3:return ()
    final_osc=target-lat.norm(gamma)//2
    if final_osc<0:return ()
    a=lat.coordinates(alpha);out={}
    for mask in range(1<<len(osc)):
        remain=[];power=0;c=lat.cocycle(alpha,beta)/lat.osc_norm(osc)
        for i,k in enumerate(osc):
            if mask>>i&1:c*=-a[k%8];power-=k//8+1
            else:remain.append(k)
        if abs(c)<1e-14:continue
        degree=-mode-1-lat.dot(alpha,beta)-power
        if not 0<=degree<=3:continue
        for created,d in creation(alpha,degree):
            mon=tuple(sorted(tuple(remain)+created));assert lat.osc_grade(mon)==final_osc
            lat.add_term(out,(gamma,mon),c*d*lat.osc_norm(mon))
    return tuple(out.items())

def basis_mode(u,mode,v):
    alpha,osc=u
    target=lat.norm(alpha)//2+lat.osc_grade(osc)+lat.norm(v[0])//2+lat.osc_grade(v[1])-mode-1
    if target<0:return {}
    assert target<=3
    if not osc:return dict(ope.elementary(alpha,(),mode,v))
    if alpha==lat.ZERO and len(osc)==1:
        return {s:-mode*c/np.sqrt(2) for s,c in lat.heisenberg_action(np.eye(8)[osc[0]-8],mode-1,v)}
    i=osc[0];restosc=osc[1:] if alpha==lat.ZERO else ();out={}
    for n in range(-target,0):
        for s,c in ope.elementary(alpha,restosc,mode-n-1,v):
            for t,d in lat.heisenberg_action(np.eye(8)[i],n,s):lat.add_term(out,t,c*d/lat.osc_norm(osc))
    vg=lat.norm(v[0])//2+lat.osc_grade(v[1])
    for n in range(vg+1):
        for s,c in lat.heisenberg_action(np.eye(8)[i],n,v):
            for t,d in ope.elementary(alpha,restosc,mode-n-1,s):lat.add_term(out,t,c*d/lat.osc_norm(osc))
    return out

def mode_matrix(u,mode):
    rows=[];cols=[];values=[];us=lat.vector_dict(u);target=3-mode
    for j,state in enumerate(lat.BASES[2]):
        out={}
        for i,a in us.items():
            for s,c in basis_mode(lat.BASES[2][i],mode,state).items():lat.add_term(out,s,a*c)
        for s,c in out.items():rows.append(lat.INDICES[target][s]);cols.append(j);values.append(c)
    return sparse.csc_matrix((values,(rows,cols)),shape=(len(lat.BASES[target]),1370))

class Span:
    def __init__(self,H1,H2):
        weights=list(zip(H1,H2));self.indices={w:np.array([i for i,z in enumerate(weights) if z==w]) for w in set(weights)}
        self.bases={w:np.zeros((len(idx),0),complex) for w,idx in self.indices.items()}
        self.queue=deque();self.dimension=0;self.accepted=[];self.rejected=[]
    def block(self,w,v):
        n=np.linalg.norm(v)
        if n<1e-9:return
        Q=self.bases[w];r=v.copy()
        for _ in range(2):r-=Q@(Q.conj().T@r)
        nr=np.linalg.norm(r)
        if nr>1e-8*max(1.,n):
            r/=nr;self.bases[w]=np.column_stack((Q,r));self.queue.append((w,r));self.dimension+=1
            self.accepted.append(float(nr/max(1.,n)))
            assert self.dimension<=1600,'Grade-three dimension exceeds safe test cap'
        else:self.rejected.append(float(nr/max(1.,n)))
    def add(self,M):
        if M.ndim==1:M=M[:,None]
        for w,idx in self.indices.items():
            block=M[idx]
            for j in range(block.shape[1]):self.block(w,block[:,j])
    def close(self,operators):
        while self.queue:
            w,v=self.queue.popleft();full=np.zeros(len(lat.BASES[3]),complex);full[self.indices[w]]=v
            for M in operators:self.add(M@full)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',required=True);args=ap.parse_args();path=Path(args.output);assert not path.exists()
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second cap')));signal.alarm(600)
    t=monotonic();n6=momenta6()
    zeroosc=[(i+16,) for i in range(8)]+[tuple(sorted((i+8,j))) for i in range(8) for j in range(8)]+list(combinations_with_replacement(range(8),3))
    osc2=[(i+8,) for i in range(8)]+list(combinations_with_replacement(range(8),2))
    lat.BASES[3]=[(lat.ZERO,o) for o in zeroosc]+[(a,o) for a in lat.ROOTS for o in osc2]+[(a,(i,)) for a in lat.NORM4 for i in range(8)]+[(a,()) for a in n6]
    assert len(lat.BASES[3])<=20000
    lat.INDICES[3]={s:i for i,s in enumerate(lat.BASES[3])};lat.vertex_action=vertex;lat.creation=creation
    currents=lat.KLEFT+lat.KRIGHT;M=[lat.current_matrix(c,0,3) for c in currents]
    H1=np.rint(M[0].diagonal().real).astype(int);H2=np.rint(M[3].diagonal().real).astype(int)
    span=Span(H1,H2);source=Path('hi_cft_20260923_c8_fields_precise.npz');W=np.load(source)['W2'];history=[]
    print({'ambient_grade3':len(lat.BASES[3]),'norm6_vectors':len(n6)},flush=True)
    for c in currents:span.add(lat.current_matrix(c,-1,2)@W)
    span.add(mode_matrix(ope.ambient_stress(),0)@W)
    span.close([M[2],M[5]])
    history.append({'stage':'affine_and_translation_descendants','dimension':span.dimension});print(history[-1],flush=True)
    pos=24
    for n,m,h,_ in fields.SPECS:
        span.add(mode_matrix(W[:,pos],0)@W);span.close([M[2],M[5]]);pos+=n*m
        history.append({'stage':f'{n},{m};e={h}/1271','dimension':span.dimension});print(history[-1],flush=True)
    # Raising closure is an independent check of covariance used above.
    before=span.dimension
    for w,Q in list(span.bases.items()):
        for j in range(Q.shape[1]):
            full=np.zeros(len(lat.BASES[3]),complex);full[span.indices[w]]=Q[:,j]
            for op in (M[1],M[4]):span.add(op@full)
    span.close([M[2],M[5]]);assert span.dimension==before,'Missing current covariance'
    weights={f'{a},{b}':Q.shape[1] for (a,b),Q in span.bases.items() if Q.shape[1]}
    out={'ambient_grade3':len(lat.BASES[3]),'norm6_vectors':len(n6),'generated_grade3_dimension':span.dimension,
         'Haagerup_character_target':956,'target_matches':span.dimension==956,'history':history,'weight_multiplicities':weights,
         'minimum_accepted_relative_residual':min(span.accepted),'maximum_rejected_relative_residual':max(span.rejected),
         'seconds':monotonic()-t,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'Numerical span of generator products in grade three. Higher composites could enlarge the generated subalgebra; rationality and category are not established.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(lat.__file__),Path(ope.__file__),source)}}
    path.write_text(json.dumps(out,indent=2)+'\n')
    np.savez_compressed(path.with_suffix('.npz'),**{f'weight_{w[0]}_{w[1]}':Q for w,Q in span.bases.items() if Q.shape[1]})
    print(json.dumps({'output':str(path),'dimension':span.dimension,'seconds':out['seconds']}),flush=True)

if __name__=='__main__':main()
