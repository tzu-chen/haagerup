"""Exact lattice modes with targets through weight four."""
from collections import Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import factorial
import hi_cft_20260923_c8_exact as x

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

@lru_cache(maxsize=2048)
def creation(alpha,g):
    out=[]
    for osc in oscillators(g):
        c=Q(1)
        for k,m in Counter(osc).items():c*=Q(alpha[k%8]**m,(k//8+1)**m*factorial(m))
        if c:out.append((osc,c))
    return tuple(out)

@lru_cache(maxsize=12000)
def vertex(alpha,mode,state):
    beta,osc=state;gamma=x.plus(alpha,beta);target=x.norm(alpha)//2+x.grade(state)-mode-1
    if not 0<=target<=4 or target<x.norm(gamma)//2:return ()
    out={}
    for mask in range(1<<len(osc)):
        remain=[];power=0;c=x.cocycle(alpha,beta)
        for i,k in enumerate(osc):
            if mask>>i&1:c*=-x.dot(x.SIMPLE[k%8],alpha);power-=k//8+1
            else:remain.append(k)
        if not c:continue
        degree=-mode-1-x.dot(alpha,beta)-power
        if not 0<=degree<=4:continue
        for created,d in creation(alpha,degree):
            mon=tuple(sorted(tuple(remain)+created));assert x.oscgrade(mon)+x.norm(gamma)//2==target
            x.add(out,(gamma,mon),c*d)
    return tuple(out.items())

@lru_cache(maxsize=12000)
def basis_mode(u,mode,v):
    alpha,osc=u;wt=x.grade(u);target=wt+x.grade(v)-mode-1
    if target<0:return ()
    assert target<=4
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

def pct(v):
    out={};coeff=(5,8,9,8,5,1,2,2)
    for (alpha,osc),a in v.items():
        factor=Q((-1)**len(osc))
        for c,power in zip(coeff,alpha):factor*=Q(c)**power
        out[tuple(-i for i in alpha),osc]=a.conj(2)*factor
    return out

def install():
    x.creation=creation;x.vertex=vertex;x.basis_mode=basis_mode
