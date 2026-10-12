"""Exact or finite-field grade-three span of the explicit generators.

A split-prime rank is a rigorous characteristic-zero lower bound, not an
upper-bound certificate. A rational-number-field run certifies the span.
Neither identifies the entire generated VOA in all grades.
"""
import argparse,hashlib,json,resource,signal
from collections import Counter,deque
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations_with_replacement
from math import factorial
from pathlib import Path
from time import monotonic
import hi_cft_20260923_c8_exact as x

OLD_CREATION=x.creation
@lru_cache(maxsize=2048)
def creation(alpha,g):
    if g<3:return OLD_CREATION(alpha,g)
    assert g==3;out=[]
    for i,a in enumerate(alpha):
        if a:out.append(((i+16,),Q(a,3)))
        for j,b in enumerate(alpha):
            if a and b:out.append((tuple(sorted((i+8,j))),Q(a*b,2)))
    for osc in combinations_with_replacement(range(8),3):
        a=Q(1)
        for i in osc:a*=alpha[i]
        for m in Counter(osc).values():a/=factorial(m)
        if a:out.append((osc,a))
    return tuple(out)

@lru_cache(maxsize=12000)
def vertex(alpha,mode,state):
    beta,osc=state;gamma=x.plus(alpha,beta);target=x.norm(alpha)//2+x.grade(state)-mode-1
    if not 0<=target<=3 or target<x.norm(gamma)//2:return ()
    out={}
    for mask in range(1<<len(osc)):
        remain=[];power=0;c=x.cocycle(alpha,beta)
        for i,k in enumerate(osc):
            if mask>>i&1:c*=-x.dot(x.SIMPLE[k%8],alpha);power-=k//8+1
            else:remain.append(k)
        if not c:continue
        degree=-mode-1-x.dot(alpha,beta)-power
        if not 0<=degree<=3:continue
        for created,d in creation(alpha,degree):
            mon=tuple(sorted(tuple(remain)+created));assert x.oscgrade(mon)+x.norm(gamma)//2==target
            x.add(out,(gamma,mon),c*d)
    return tuple(out.items())

@lru_cache(maxsize=12000)
def basis_mode(u,mode,v):
    alpha,osc=u;wt=x.grade(u);target=wt+x.grade(v)-mode-1
    if target<0:return ()
    assert target<=3
    if not osc or wt==1:return x.elementary(alpha,osc,mode,v)
    assert wt==2
    if alpha==x.ZERO and len(osc)==1:return tuple((s,-mode*c) for s,c in x.heis(osc[0]-8,mode-1,v))
    i=osc[0];restosc=osc[1:] if alpha==x.ZERO else ();out={}
    for k in range(-target,0):
        for s,c in x.elementary(alpha,restosc,mode-k-1,v):
            for r,d in x.heis(i,k,s):x.add(out,r,c*d)
    for k in range(x.grade(v)+1):
        for s,c in x.heis(i,k,v):
            for r,d in x.elementary(alpha,restosc,mode-k-1,s):x.add(out,r,c*d)
    return tuple(out.items())

def install_prime(p):
    assert p>3 and all(p%d for d in range(2,int(p**.5)+1)) and p%4==3
    roots=[pow(a,(p+1)//4,p) for a in (13,p-3)]
    assert roots[0]**2%p==13 and roots[1]**2%p==p-3
    class F(int):
        def __new__(cls,a=0):
            if isinstance(a,str):a=Q(a)
            if isinstance(a,(tuple,list)):
                a=sum((F(c)*r for c,r in zip(a,(1,roots[0],roots[1],roots[0]*roots[1]))),F(0))
            elif isinstance(a,Q):
                assert a.denominator%p
                a=a.numerator*pow(a.denominator,-1,p)
            return int.__new__(cls,int(a)%p)
        def __add__(a,b):return F(int(a)+int(F(b)))
        __radd__=__add__
        def __neg__(a):return F(-int(a))
        def __sub__(a,b):return F(int(a)-int(F(b)))
        def __rsub__(a,b):return F(b)-a
        def __mul__(a,b):return F(int(a)*int(F(b)))
        __rmul__=__mul__
        def inv(a):return F(pow(int(a),-1,p))
        def __truediv__(a,b):return a*F(b).inv()
        def __rtruediv__(a,b):return F(b)*a.inv()
    x.LEFT=tuple({s:F(c) for s,c in v.items()} for v in x.LEFT)
    x.RIGHT=tuple({s:F(c) for s,c in v.items()} for v in x.RIGHT)
    x.A=F;x.ONE=F(1);x.ZERO_A=F(0);x.VAC={(x.ZERO,()):F(1)}
    return roots

class GeneratedSpan(x.Span):
    def __init__(self):super().__init__();self.queue=deque()
    def add(self,v):
        r=self.reduce(v,True)
        if r:self.queue.append(r)
        assert self.dimension<=1600,'Safe span-size cap'
    def close(self):
        while self.queue:
            v=self.queue.popleft()
            for c in (x.LEFT[2],x.RIGHT[2]):self.add(x.mode(c,0,v))
    def vectors(self):return [v for block in self.blocks.values() for v in block.values()]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--prime',type=int,default=0);ap.add_argument('--output',required=True)
    ap.add_argument('--audit-raising',action='store_true');args=ap.parse_args()
    path=Path(args.output);assert not path.exists()
    assert 0<resource.getrlimit(resource.RLIMIT_AS)[0]<=2*1024**3
    signal.signal(signal.SIGALRM,lambda *_:(_ for _ in ()).throw(TimeoutError('600-second cap')));signal.alarm(600)
    t=monotonic();source=Path('hi_cft_20260923_c8_exact_fields.json');data=json.loads(source.read_text())
    roots=install_prime(args.prime) if args.prime else None
    x.creation=creation;x.vertex=vertex;x.basis_mode=basis_mode
    fields=[x.read_field(r) for r in data['fields']];currents=x.LEFT+x.RIGHT
    W=x.Span();vectors=[];omega=x.omega();T=x.vadd((1,omega),(-1,x.sugawara(x.LEFT,1)),(-1,x.sugawara(x.RIGHT,39)))
    def add_weight_two(v):
        # Retain the original sparse representation vectors for products;
        # echelon combinations have unnecessarily complicated coefficients.
        if W.reduce(v,True):vectors.append(v)
    for c in currents:
        add_weight_two(x.mode(c,-2,x.VAC))
        for d in currents:add_weight_two(x.mode(c,-1,d))
    add_weight_two(fields[-1]);add_weight_two(x.vadd((1,T),(-1,fields[-1])))
    for row,u in zip(data['fields'][:-1],fields[:-1]):
        for v in x.descendants(u,*row['dimensions']):add_weight_two(v)
    assert W.dimension==120
    assert len(vectors)==120
    span=GeneratedSpan();history=[]
    for c in currents:
        for v in vectors:span.add(x.mode(c,-1,v))
    for v in vectors:span.add(x.mode(omega,0,v))
    span.close();history.append({'stage':'affine_and_translation_descendants','dimension':span.dimension,'seconds':monotonic()-t});print(history[-1],flush=True)
    for row,u in sorted(zip(data['fields'][:-1],fields[:-1]),key=lambda pair:len(pair[1])):
        for v in vectors:span.add(x.mode(u,0,v))
        span.close();history.append({'stage':str(row['dimensions'])+';e='+row['e_weight'],'dimension':span.dimension,'seconds':monotonic()-t});print(history[-1],flush=True)
    # The initial space is raising-stable because its first charged entry
    # is highest and its second entry ranges over all of S2. Its lowering
    # closure is therefore K-stable by the sl2 commutators. A redundant
    # direct raising audit is optional and runs only after saving.
    weights={f'{w[0]},{w[1]}':len(block) for w,block in span.blocks.items() if block}
    reference=json.loads(Path('hi_cft_20260923_c8_grade3_span.json').read_text())
    assert weights==reference['weight_multiplicities'],'Weight-resolved cross-check'
    out={'arithmetic':'finite field' if args.prime else 'Q(sqrt(13),sqrt(-3))','prime':args.prime,'square_roots_mod_prime':roots,
         'grade_three_span_dimension':span.dimension,'history':history,'weight_multiplicities':weights,
         'characteristic_zero_lower_bound':span.dimension,'characteristic_zero_span_dimension_certified':not bool(args.prime),
         'seconds':monotonic()-t,'peak_rss_KiB':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
         'scope':'A finite-field rank proves only a lower bound in characteristic zero. A number-field run proves the stated finite span dimension; neither identifies the full generated VOA.',
         'source_sha256':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__),Path(x.__file__),source)}}
    path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'output':str(path),'dimension':span.dimension,'seconds':out['seconds']}),flush=True)
    if args.audit_raising:
        before=span.dimension
        for v in span.vectors():
            for c in (x.LEFT[1],x.RIGHT[1]):span.add(x.mode(c,0,v))
        span.close();assert span.dimension==before
        out['independent_raising_audit_passed']=True
        out['seconds_with_audit']=monotonic()-t
        path.write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':main()
