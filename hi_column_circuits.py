"""Scalar completion from the explicit critical-algebra circuit operators.

The prime-order construction is uniform. Its integral reduction gives an
upper bound on the characteristic-zero H quotient. Exact lower bounds
from the full-Q algebra (3,5,7,11) or a fully certified orbit (13) match it.
The order-11 lower bound uses the previously certified hi_row11_basis.txt;
hi_row11_verify.py supplies its independent exact Q-to-C certificate.
See Sections 54 and 57 of the research notes for the integral-model argument.
"""

import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

import itertools as it
import math
import numpy as np
import sympy as s

def det(M,q):
 M=np.array(M,dtype=np.int64).copy(); v=1
 for j in range(len(M)):
  piv=next((k for k in range(j,len(M)) if M[k,j]%q),None)
  if piv is None:return 0
  if piv!=j:M[[j,piv]]=M[[piv,j]];v=-v
  a=int(M[j,j]);v=v*a%q;M[j]=M[j]*pow(a,-1,q)%q
  if j+1<len(M):M[j+1:]=(M[j+1:]-M[j+1:,j:j+1]*M[j])%q
 return v%q

def inverse(M,q):
 n=len(M);V=np.concatenate([M,np.eye(n,dtype=np.int64)],axis=1)
 for j in range(n):
  piv=next((k for k in range(j,n) if V[k,j]),None)
  if piv is None:raise ArithmeticError('singular matrix')
  V[[j,piv]]=V[[piv,j]];V[j]=V[j]*pow(int(V[j,j]),-1,q)%q
  factors=V[:,j:j+1].copy();factors[j]=0
  V=(V-factors*V[j])%q
 return V[:,n:]

def construct(p,q=None):
 m=(p-1)//2;N=p
 if q is None:
  q=32000
  while True:
   q=int(s.nextprime(q))
   if (q-1)%p==0 and s.legendre_symbol(p*p+4,q)==1:break
 root=int(s.sqrt_mod(p*p+4,q));d=(p+root)*pow(2,-1,q)%q
 gamma=-p*d*pow((d-1)**2,-1,q)%q
 z=pow(int(s.primitive_root(q)),(q-1)//p,q)
 cos=lambda j:(pow(z,j%p,q)+pow(z,(-j)%p,q))*pow(2,-1,q)%q
 mu=[1]+[2]*m
 weights=np.array([gamma*mu[j]%q for j in range(m)]+mu,dtype=np.int64)
 normals=np.array([[int(i==j) for j in range(m)] for i in range(m)]+[[mu[j]*cos(k*j)%q for j in range(m)] for k in range(m+1)],dtype=np.int64)
 constants=np.array([0]*m+[-2*cos(k*m)%q for k in range(m+1)],dtype=np.int64)
 basis=list(it.combinations(range(N-1),m));ix={I:j for j,I in enumerate(basis)};size=len(basis)
 allminor={I:det(normals[list(I)],q) for I in it.combinations(range(N),m)}
 assert all(allminor.values())
 def expand(I):
  if N-1 not in I:return {ix[I]:1}
  J=I[:-1];ret={}
  for j in range(N-1):
   if j in J:continue
   loc=sum(t<j for t in J);H=tuple(sorted(J+(j,)))
   ret[ix[H]]=(-1)**(m+loc)
  return ret
 matrices=[np.zeros((size,size),dtype=np.int64) for _ in range(N)]
 for C in it.combinations(range(N),m+1):
  subsets=[C[:j]+C[j+1:] for j in range(m+1)]
  lam=np.array([(-1)**j*allminor[I]%q for j,I in enumerate(subsets)],dtype=np.int64)
  fc=int(lam@constants[list(C)]%q);assert fc
  v=np.zeros(size,dtype=np.int64)
  for j,I in enumerate(subsets):
   for ix0,coef in expand(I).items():v[ix0]=(v[ix0]+(-1)**j*int(weights[C[j]])*coef)%q
  columns=[(ix[I],(-1)**j) for j,I in enumerate(subsets) if I in ix]
  for l,j in enumerate(C):
   vv=v*(int(lam[l])*pow(fc,-1,q)%q)%q
   for col,sign in columns:matrices[j][:,col]=(matrices[j][:,col]+sign*vv)%q
 print('constructed',p,'q',q,'d',d,'size',size,flush=True)
 I=np.eye(size,dtype=np.int64)
 for j in range(m):
  assert not np.any(sum((int(normals[k,j])*matrices[k] for k in range(N)))%q),('linear',p,j)
 X=[int(weights[j])*inverse(matrices[j],q)%q for j in range(m)]
 for j in range(N):
  f=(int(constants[j])*I+sum((int(normals[j,k])*X[k] for k in range(m))))%q
  assert np.array_equal(matrices[j]@f%q,int(weights[j])*I%q),('mult',p,j)
 for j,k in it.combinations(range(m),2):assert not np.any((X[j]@X[k]-X[k]@X[j])%q),('commute',j,k)
 L=(d-1)**2%q
 u=[-I%q]*p
 v=[-I%q]*p
 for a in range(2,(p+1)//2+1):
  j=(p+1)//2-a
  u[a]=u[(1-a)%p]=X[j]
  v[a]=v[(1-a)%p]=d*matrices[j]*pow(int(weights[j]),-1,q)%q
 for g in range(p):
  val=sum((u[(a+g)%p]@v[a] for a in range(p)))%q
  assert np.array_equal(val,L*I%q if g==0 else I*0),('Q1',p,g)
 print('exact finite field: critical relations, commutativity, complete column passed',p,flush=True)
 return q,d,v,u,matrices


SCALAR_GP = r"""
BfromP(P,g,h)={g=g%n;h=h%n;if(g==0&&h==0,return(d-2));if(g==0||h==0||g==h,return(-1));if(g<h,return(P[h+1]/(P[g+1]*P[h-g+1])),return(d*P[h+1]*P[g-h+1]/P[g+1]));};
run_scalar()={
my(ff=factor(F),z,r,P,cp,H,G,tr,sigma,degree,total=0,B,errors,qlength=0,hd=List());
if(poldegree(gcd(F,deriv(F)))>0,error("not reduced at selected prime"));
for(i=1,matsize(ff)[1],
 z=ffgen(ff[i,1],'z);r=apply(f->subst(f,t,z),rr);P=vector(n,a,z^0);
 for(a=2,n-1,P[a+1]=P[a]*r[a+1]);
 cp=x^n-d*P[n];sigma=-1+sum(a=1,n-1,x^a/P[a+1]);
 tr=sum(a=0,n-1,BfromP(P,a,2*a));H=(sigma^2+(d-1)*tr-2*(d-1)^2)%cp;
 G=gcd(cp,H);degree=poldegree(G);total+=poldegree(ff[i,1])*degree;
 if(degree,
  listput(hd,[poldegree(ff[i,1]),degree]);
  B=matrix(n,n,g,h,BfromP(P,g-1,h-1));
  errors=0;for(g=1,n-1,for(h=1,n-1,if(sum(a=0,n-1,B[(g+a)%n+1,h+1]*B[h+1,a+1]),errors++)));
  if(errors,error("scalar component fails Q",[i,errors]));
  qlength+=poldegree(ff[i,1])*degree;
 );
);
print("p=",n," q=",q," one-column length=",poldegree(F)," H-phase quotient length=",total," all-Q length in H quotient=",qlength," selected factor degrees=",Vec(hd));
print("FINITE-FIELD SCALAR CHECK PASSED; characteristic-zero lower bound still required");
};
run_scalar();
quit;
"""

LOWER13_GP = r"""
run_lower13()={
my(cert=hi_stark_run(13),pref=vector(13,a,Mod(1,P)),roots,W,H);
for(a=2,12,pref[a+1]=pref[a]*B[2,a+1]);
roots=nfroots(F,x^13-d*pref[13]);
hi_check("unique phase root in the certified field",#roots==1);
W=vector(13,a,if(a==1,-1,Mod(roots[1],P)^(a-1)/pref[a]));
hi_check("all phase norms",vecmin(vector(12,a,W[a+1]*W[14-a]==d)));
H=sum(a=1,13,W[a])^2+(d-1)*sum(a=0,12,B[a+1,(2*a)%13+1])-2*(d-1)^2;
hi_check("exact scalar completion condition",H==0);
hi_check("row coordinate has full absolute degree 24",poldegree(minpoly(B[2,3]))==24);
print("EXACT LOWER BOUND 12 AT ORDER 13 PASSED");
};
iferr(run_lower13(),e,print(e);quit(1));
quit;
"""

def run_gp(source, directory, name):
    path = directory / (name + '.gp')
    path.write_text('default(parisizemax,1000000000);\n' + source)
    result = subprocess.run(['gp', '-q', '-f', str(path)], capture_output=True,
                            text=True, timeout=600)
    output = result.stdout + result.stderr
    if result.returncode or '***   at' in output:
        raise ArithmeticError(output)
    return output


def krylov_source(p, q, d, R):
    m, size = (p-1)//2, len(R[0])
    v = np.eye(size, dtype=np.int64)[:, 0]
    for seed in range(1, 11):
        Z = sum((pow(seed+j+1, j+1, q)*R[j+2] for j in range(m))) % q
        columns = [v]
        for _ in range(size):
            columns.append(Z @ columns[-1] % q)
        transform = np.stack(columns[:-1], axis=1)
        try:
            transform_inverse = inverse(transform, q)
        except ArithmeticError:
            continue
        break
    else:
        raise ArithmeticError('No primitive combination found')
    f = np.append(-transform_inverse @ columns[-1] % q, 1)
    coordinates = [transform_inverse @ r[:, 0] % q for r in R]
    print(f'Exact Krylov basis: order={p}, dimension={size}, choice={seed}', flush=True)
    return '\n'.join([
        f'q={q};n={p};d=Mod({d},q);',
        f'F=Mod(1,q)*Polrev({f.tolist()},t);',
        f'rr=apply(v->Polrev(v,t),{[r.tolist() for r in coordinates]});',
    ]) + '\n'


def lower11(directory):
    basis = (Path(__file__).resolve().parent / 'hi_row11_basis.txt').read_text().strip()
    source = '\n'.join([
        'ring R=(0,d),(r1,r2,r3,r4,r5,t),dp;',
        'minpoly=d^2-11*d-1;', 'ideal J='+basis+';', 'J=std(J);',
        'ring S=(0,d),(r1,r2,r3,r4,r5,t),lp;',
        'minpoly=d^2-11*d-1;', 'ideal L=fglm(R,J);', 'print(L);',
        'print("FGLM_FINISHED");', 'quit;',
    ])
    path = directory / 'lower11.sing'
    path.write_text(source)
    result = subprocess.run(['Singular', '-q', str(path)], capture_output=True,
                            text=True, timeout=600)
    output = result.stdout + result.stderr
    if result.returncode or '?' in output or 'FGLM_FINISHED' not in output:
        raise ArithmeticError(output)
    parts = output.split('FGLM_FINISHED')[0].strip().split(',\n')
    assert len(parts) == 6
    row_polynomials = {v.split('+')[0]: v.split('+', 1)[1] for v in parts[1:]}
    rows = ['-1', '-1'] + ['-('+row_polynomials['r'+str(min(a, 12-a)-1)]+')'
                           for a in range(2, 11)]
    data = '\n'.join([
        'x=\'x;t=\'t;y=varlower("dfield",t);',
        'default(parisizemax,3000000000);',
        'n=11;d=Mod(y,y^2-11*y-1);', 'F='+parts[0]+';',
        'rr=['+','.join(rows)+'];',
    ]) + '\n'
    check = SCALAR_GP.replace('ff=factor(F)', 'ff=nffactor(nfinit(y^2-11*y-1),F)')
    check = check.replace("z=ffgen(ff[i,1],'z)", 'z=Mod(t,ff[i,1])')
    check = check.replace('" q=",q,', '" characteristic zero",')
    check = check.replace(
        'FINITE-FIELD SCALAR CHECK PASSED; characteristic-zero lower bound still required',
        'EXACT CHARACTERISTIC-ZERO LOWER BOUND PASSED')
    output = run_gp(data+check, directory, 'lower11')
    assert 'H-phase quotient length=12' in output
    assert 'EXACT CHARACTERISTIC-ZERO LOWER BOUND PASSED' in output
    print(output, end='', flush=True)
    return 12


def lower13(directory):
    path = directory / 'lower13.gp'
    path.write_text(LOWER13_GP)
    library = Path(__file__).resolve().parent / 'hi_stark_seedless.gp'
    env = os.environ.copy()
    env['HI_STARK_LIBRARY'] = '1'
    result = subprocess.run(['gp', '-q', '-f', str(library), str(path)], env=env,
                            capture_output=True, text=True, timeout=600)
    output = result.stdout + result.stderr
    if result.returncode or '***   at' in output or 'EXACT LOWER BOUND 12 AT ORDER 13 PASSED' not in output:
        raise ArithmeticError(output)
    print(output, end='', flush=True)
    return 12


def small_lower(p, directory):
    from hi_column_trace_exact import sources, singular
    _, source, *_ = sources(p)
    lines = singular(source, directory / f'lower{p}.sing', 600, 'GOOD_FINISHED')
    lower = int(next(v.split('=')[1] for v in lines if v.startswith('GOOD_DIM=')))
    assert 'C_FAILURES=0' in lines
    print(f'Exact characteristic-zero full-Q/H quotient length at {p}: {lower}; all C passed',
          flush=True)
    return lower


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[11, 13])
    parser.add_argument('--output', type=Path,
                        help='Keep the generated GP and Singular sources in this directory')
    args = parser.parse_args()
    if any(p not in (3, 5, 7, 11, 13) for p in args.orders):
        parser.error('The available exact lower-bound certificates are at 3, 5, 7, 11, 13')
    with tempfile.TemporaryDirectory(prefix='hi_circuit_trace_') as temp:
        directory = args.output or Path(temp)
        directory.mkdir(parents=True, exist_ok=True)
        for p in args.orders:
            started = time.monotonic()
            q, d, R, _, _ = construct(p)
            data = krylov_source(p, q, d, R)
            output = run_gp(data+SCALAR_GP, directory, f'upper{p}')
            assert 'FINITE-FIELD SCALAR CHECK PASSED' in output
            upper = int(re.search(r'H-phase quotient length=(\d+)', output).group(1))
            print(output, end='', flush=True)
            lower = lower11(directory) if p == 11 else lower13(directory) if p == 13 else small_lower(p, directory)
            assert lower == upper
            print(f'EXACT SCALAR COMPLETION p={p}: upper=lower={upper}; '
                  f'{time.monotonic()-started:.2f} seconds', flush=True)
    print('ALL REQUESTED CIRCUIT SCALAR-COMPLETION CERTIFICATES PASSED')


if __name__ == '__main__':
    main()
