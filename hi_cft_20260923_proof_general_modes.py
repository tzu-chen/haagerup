"""Bounded recursive exact lattice modes and the physical Hermitian form.

No ambient bases are allocated. Callers must set a target-grade ceiling
and run under the repository resource launcher.
"""
from collections import Counter,defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from math import comb,factorial
import hi_cft_20260923_c8_exact as x
import hi_cft_20260923_proof_exact4 as old

MAX_GRADE=4

def binomial(n,k):
    if n>=0:return comb(n,k) if n>=k else 0
    return (-1)**k*comb(k-n-1,k)

@lru_cache(maxsize=12000)
def vertex(alpha,mode,state):
    beta,osc=state;gamma=x.plus(alpha,beta);target=x.norm(alpha)//2+x.grade(state)-mode-1
    if not 0<=target<=MAX_GRADE or target<x.norm(gamma)//2:return ()
    out={}
    for mask in range(1<<len(osc)):
        remain=[];power=0;c=x.cocycle(alpha,beta)
        for i,k in enumerate(osc):
            if mask>>i&1:c*=-x.dot(x.SIMPLE[k%8],alpha);power-=k//8+1
            else:remain.append(k)
        if not c:continue
        degree=-mode-1-x.dot(alpha,beta)-power
        if not 0<=degree<=MAX_GRADE:continue
        for created,d in old.creation(alpha,degree):
            mon=tuple(sorted(tuple(remain)+created));assert x.oscgrade(mon)+x.norm(gamma)//2==target
            x.add(out,(gamma,mon),c*d)
    return tuple(out.items())

@lru_cache(maxsize=15000)
def basis_mode(u,mode,v):
    alpha,osc=u;target=x.grade(u)+x.grade(v)-mode-1
    if target<0:return ()
    assert target<=MAX_GRADE,(target,MAX_GRADE)
    if not osc:return vertex(alpha,mode,v)
    i=osc[0]%8;n=osc[0]//8+1;rest=(alpha,osc[1:]);out={}
    for k in range(-target,0):
        factor=(-1)**(n-1)*binomial(k+n-1,n-1)
        if not factor:continue
        for s,c in basis_mode(rest,mode-n-k,v):
            for r,d in x.heis(i,k,s):x.add(out,r,factor*c*d)
    for k in range(x.grade(v)+1):
        factor=(-1)**(n-1)*binomial(k+n-1,n-1)
        if not factor:continue
        for s,c in x.heis(i,k,v):
            for r,d in basis_mode(rest,mode-n-k,s):x.add(out,r,factor*c*d)
    return tuple(out.items())

@lru_cache(maxsize=20000)
def oscillator_inner(a,b):
    if not a:return int(not b)
    first=a[0];out=0
    for j,last in enumerate(b):
        if first//8==last//8:
            out+=(first//8+1)*x.G[first%8][last%8]*oscillator_inner(a[1:],b[:j]+b[j+1:])
    return out

def inner(v,w):
    by_momentum=defaultdict(list)
    for (a,o),c in w.items():by_momentum[a].append((o,c))
    out=x.A(0);coeff=(5,8,9,8,5,1,2,2)
    for (a,o),c in v.items():
        scale=Q(1)
        for k,p in zip(coeff,a):scale*=Q(k)**p
        for p,d in by_momentum[a]:
            z=oscillator_inner(o,p)
            if z:out+=c.conj(2)*d*scale*z
    return out

def install(max_grade=4):
    global MAX_GRADE
    MAX_GRADE=max_grade;x.vertex=vertex;x.creation=old.creation;x.basis_mode=basis_mode
