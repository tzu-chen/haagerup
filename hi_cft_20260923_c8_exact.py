"""Exact low-grade lattice VOA in a simple-root Heisenberg basis.

No NumPy, floating arithmetic, or numerical coefficients are used here.
The coefficient field has generators s^2=13 and t^2=-3. Oscillators are
unnormalized. The principal Chevalley gauge has e=sum(e_i), f=sum(c_i f_i).
"""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations_with_replacement


class A(tuple):
    def __new__(cls,x=0):
        if isinstance(x,A):return x
        if isinstance(x,(tuple,list)):return tuple.__new__(cls,tuple(Q(v) for v in x))
        return tuple.__new__(cls,(Q(x),Q(0),Q(0),Q(0)))
    def __bool__(self):return any(x for x in self)
    def __add__(self,b):
        b=A(b);return A(tuple(x+y for x,y in zip(self,b)))
    __radd__=__add__
    def __neg__(self):return A(tuple(-x for x in self))
    def __sub__(self,b):return self+-A(b)
    def __rsub__(self,b):return A(b)+-self
    def __mul__(self,b):
        b=A(b)
        if not self or not b:return ZERO_A
        out=[Q(0)]*4
        for i,x in enumerate(self):
            if not x:continue
            for j,y in enumerate(b):
                if y:out[i^j]+=x*y*(13 if i&j&1 else 1)*(-3 if i&j&2 else 1)
        return A(out)
    __rmul__=__mul__
    def conj(self,mask):return A(tuple((-x if (i&mask).bit_count()%2 else x) for i,x in enumerate(self)))
    def inv(self):
        if not self:raise ZeroDivisionError
        numerator=self.conj(1)*self.conj(2)*self.conj(3)
        norm=self*numerator
        assert norm[1:]==(0,0,0)
        return A(tuple(x/norm[0] for x in numerator))
    def __truediv__(self,b):return self*A(b).inv()
    def __rtruediv__(self,b):return A(b)*self.inv()


ZERO_A=A(0);ONE=A(1);ZERO=(0,)*8
SIMPLE=[tuple(int(i==j) for j in range(8)) for i in range(8)]
G=[[2*int(i==j) for j in range(8)] for i in range(8)]
for i,j in ((0,1),(1,2),(2,3),(3,4),(2,5),(6,7)):G[i][j]=G[j][i]=-1

@lru_cache(maxsize=16384)
def dot(a,b):return sum(a[i]*G[i][j]*b[j] for i in range(8) for j in range(8) if a[i] and b[j])
def plus(a,b):return tuple(x+y for x,y in zip(a,b))
def norm(a):return dot(a,a)
def oscgrade(o):return sum(k//8+1 for k in o)
def grade(state):return norm(state[0])//2+oscgrade(state[1])

@lru_cache(maxsize=16384)
def cocycle(a,b):
    parity=sum(a[i]*b[i] for i in range(8))+sum(a[i]*b[j]*G[i][j] for i in range(8) for j in range(i))
    return (-1)**(parity%2)

def add(out,state,value):
    if value:
        c=out.get(state,0)+value
        if c:out[state]=c
        elif state in out:del out[state]

def vadd(*terms):
    out={}
    for coefficient,v in terms:
        for s,c in v.items():add(out,s,A(coefficient)*c)
    return out

@lru_cache(maxsize=2048)
def creation(alpha,g):
    if g==0:return (((),Q(1)),)
    if g==1:return tuple(((i,),Q(a)) for i,a in enumerate(alpha) if a)
    assert g==2
    out=[((i+8,),Q(a,2)) for i,a in enumerate(alpha) if a]
    for i,j in combinations_with_replacement(range(8),2):
        if alpha[i] and alpha[j]:out.append(((i,j),Q(alpha[i]*alpha[j],2 if i==j else 1)))
    return tuple(out)

@lru_cache(maxsize=12000)
def vertex(alpha,mode,state):
    beta,osc=state;gamma=plus(alpha,beta)
    target=norm(alpha)//2+grade(state)-mode-1
    if not 0<=target<=2 or target<norm(gamma)//2:return ()
    out={}
    for mask in range(1<<len(osc)):
        remain=[];power=0;coefficient=cocycle(alpha,beta)
        for i,k in enumerate(osc):
            if mask>>i&1:
                coefficient*=-dot(SIMPLE[k%8],alpha);power-=k//8+1
            else:remain.append(k)
        if not coefficient:continue
        degree=-mode-1-dot(alpha,beta)-power
        if not 0<=degree<=2:continue
        for created,c in creation(alpha,degree):
            mon=tuple(sorted(tuple(remain)+created))
            assert oscgrade(mon)+norm(gamma)//2==target
            add(out,(gamma,mon),coefficient*c)
    return tuple(out.items())

def heis(i,mode,state):
    beta,osc=state
    if mode==0:
        c=dot(SIMPLE[i],beta);return ((state,c),) if c else ()
    if mode<0:return (((beta,tuple(sorted(osc+(i+8*(-mode-1),)))),1),)
    out=[]
    for k,m in Counter(osc).items():
        if k//8+1==mode and G[i][k%8]:
            rem=list(osc);rem.remove(k);out.append(((beta,tuple(rem)),mode*m*G[i][k%8]))
    return tuple(out)

def elementary(alpha,osc,mode,state):
    if alpha!=ZERO:return vertex(alpha,mode,state)
    if not osc:return ((state,1),) if mode==-1 else ()
    assert len(osc)==1 and osc[0]<8
    return heis(osc[0],mode,state)

@lru_cache(maxsize=12000)
def basis_mode(u,mode,v):
    alpha,osc=u;wt=grade(u);target=wt+grade(v)-mode-1
    if target<0:return ()
    assert target<=2
    if not osc or wt==1:return elementary(alpha,osc,mode,v)
    assert wt==2
    if alpha==ZERO and len(osc)==1:return tuple((s,-mode*c) for s,c in heis(osc[0]-8,mode-1,v))
    i=osc[0];restosc=osc[1:] if alpha==ZERO else ()
    out={}
    for k in range(-target,0):
        for s,c in elementary(alpha,restosc,mode-k-1,v):
            for r,d in heis(i,k,s):add(out,r,c*d)
    for k in range(grade(v)+1):
        for s,c in heis(i,k,v):
            for r,d in elementary(alpha,restosc,mode-k-1,s):add(out,r,c*d)
    return tuple(out.items())

def mode(u,n,v):
    out={}
    for s,a in u.items():
        for t,b in v.items():
            terms=basis_mode(s,n,t)
            if not terms:continue
            ab=a*b
            for r,c in terms:add(out,r,ab*c)
    return out

def cartan(alpha):return {(ZERO,(i,)):A(c) for i,c in enumerate(alpha) if c}
def root(alpha,c=1):return {(tuple(alpha),()):A(c)}
VAC={(ZERO,()):ONE}
A0=(-1,-2,-3,-2,-1,-2,0,0)
LEFT=(cartan(A0),root(A0),root(tuple(-x for x in A0),-1))
COEFF=(5,8,9,8,5,0,2,2)
RIGHT=(cartan(COEFF),vadd(*[(1,root(SIMPLE[i])) for i,c in enumerate(COEFF) if c]),
       vadd(*[(-c,root(tuple(-x for x in SIMPLE[i]))) for i,c in enumerate(COEFF) if c]))

def inverse(matrix):
    n=len(matrix);rows=[[Q(c) for c in row]+[Q(i==j) for j in range(n)] for i,row in enumerate(matrix)]
    for i in range(n):
        pivot=next(j for j in range(i,n) if rows[j][i]);rows[i],rows[pivot]=rows[pivot],rows[i]
        a=rows[i][i];rows[i]=[x/a for x in rows[i]]
        for j in range(n):
            if i!=j:
                a=rows[j][i];rows[j]=[x-a*y for x,y in zip(rows[j],rows[i])]
    return [row[n:] for row in rows]

def omega():
    gi=inverse(G)
    return {(ZERO,(i,j)):A(gi[i][j]/(2 if i==j else 1)) for i,j in combinations_with_replacement(range(8),2) if gi[i][j]}

def sugawara(currents,k):
    h,e,f=currents
    return vadd((Q(1,4*(k+2)),mode(h,-1,h)),(Q(1,2*(k+2)),mode(e,-1,f)),(Q(1,2*(k+2)),mode(f,-1,e)))

def read_field(row):
    out={}
    for item in row['coefficients']:
        parts=item['Qsqrt13_sqrtminus3'];assert all(p is not None for p in parts)
        out[tuple(item['momentum']),tuple(item['oscillators'])]=A(parts[0]+parts[1])
    return out

def weight(state):return dot(A0,state[0]),dot(COEFF,state[0])

class Span:
    def __init__(self):self.blocks={};self.dimension=0
    def reduce(self,vector,insert=False):
        if not vector:return {}
        weights={weight(s) for s in vector}
        assert len(weights)==1,weights
        w=next(iter(weights));block=self.blocks.setdefault(w,{})
        out=vector.copy()
        for pivot,v in sorted(block.items()):
            if pivot in out:out=vadd((1,out),(-out[pivot],v))
        if insert and out:
            pivot=min(out);scale=out[pivot].inv();out={s:c*scale for s,c in out.items()}
            block[pivot]=out;self.dimension+=1
        return out

def descendants(u,n,m):
    result=[];left=u
    for i in range(n):
        right=left
        for j in range(m):
            result.append(right)
            right=mode(RIGHT[2],0,right)
        assert not right
        left=mode(LEFT[2],0,left)
    assert not left
    return result
