"""Numerical indexing regressions for the proved pentagon operator theorem.

These checks compare the complete cubic residual with the scalar trace
identity, including away from Q. They do not prove Q-to-C in general.
The separate GP script supplies exact finite operator certificates.
"""
import re
from pathlib import Path
import numpy as np

def check(b,d):
 n=len(b);t=1/d;ii=np.arange(n);g,h=np.indices((n,n))
 A=np.sqrt(d)/(d-1)*b[g]*b[(h-g)%n]*b[(-h)%n];A[0,0]+=(d-1)/d
 R=np.zeros((n*n,n*n),complex)
 for a in range(n):
  for b0 in range(n):
   R[a*n+b0,b0*n+ii]=A[b0,(a+ii)%n]
 u=np.zeros(n*n);u[::n]=1/np.sqrt(n)
 v=np.zeros(n*n);v[:n]=1/np.sqrt(n)
 w=R@u;V=np.array([u,v,w]).T
 q=np.array([[sum(np.conj(A[m,k])*A[(m+j)%n,k] for m in range(n)) for k in range(n)] for j in range(n)])
 qtarget=np.zeros((n,n));qtarget[0,:]=1;qtarget[:,0]-=t
 qerr=np.max(abs(q-qtarget))
 errs=[]
 for g0 in range(n):
  for h0 in range(n):
   for k in range(n):
    for l in range(n):
     val=np.sum(A[ii,(g0+h0)%n]*np.conj(A[(ii+k)%n,g0]*A[(ii+l)%n,h0]))-A[(g0+l)%n,k]*A[(h0+k)%n,l]+(g0==0 and h0==0)*t
     errs.append(val)
 cnorm=float(np.vdot(errs,errs).real)
 T=np.trace(np.linalg.matrix_power(R,5))
 SU=sum(q[j,g0]*q[j,h0]*np.conj(q[j,(g0+h0)%n]) for j in range(n) for g0 in range(n) for h0 in range(n))
 total=SU.real+(n-t)**2+n*n*t*t-2*t**4-2*t*(n-t)-2*T.real
 print(n,'Qerr',qerr,'C squared norm',cnorm,'general norm diff',total-cnorm,'T',T)
 assert abs(total-cnorm)<1e-9
 if qerr<1e-10:
  K=np.linalg.qr(V)[0];Proj=K@K.conj().T;H=np.eye(n*n)-Proj
  defects=[np.max(abs(R@R.conj().T-(np.eye(n*n)-(1-t*t)*np.outer(u,u)))),np.max(abs(R.conj().T@R-(np.eye(n*n)-(1-t*t)*np.outer(v,v)))),np.max(abs(R@v+t*u)),np.max(abs(R@w-v+t*u)),np.max(abs(H@R@Proj)),np.max(abs(Proj@R@H))]
  fifth=(np.linalg.matrix_power(R,5)-np.eye(n*n))@H
  print('structural errors',defects,'fifth defect norm',np.linalg.norm(fifth)**2,'predicted C norm',2*(d*d-5+6*t*t-T.real),'traceH R',np.trace(H@R))
  assert max(defects)<1e-10
  assert abs(np.linalg.norm(fifth)**2-cnorm)<1e-8

n=5;d=(n+np.sqrt(n*n+4))/2;rng=np.random.default_rng(27);theta=rng.normal(size=(n-1)//2);b=np.r_[-1/np.sqrt(d),np.exp(1j*theta),np.exp(-1j*theta[::-1])];check(b,d)
s=Path(__file__).with_name('z13_stark_test.gp').read_text();j=list(map(float,re.search(r'jrefined = \[([^]]+)\];',s).group(1).split(',')));center=j[6]+j[7]
for g in range(8,13):j[g]=center-j[13-g]
n=13;d=(n+np.sqrt(n*n+4))/2;b=np.array([-1/np.sqrt(d)]+[np.exp(-1j*(j[g]-center*g/13)) for g in range(1,13)]);check(b,d)

print("ALL NUMERICAL PENTAGON OPERATOR REGRESSIONS PASSED")
