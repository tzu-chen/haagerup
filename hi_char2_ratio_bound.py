"""Exact checks for the patched consecutive-ratio obstruction in Section 67.

The uniform proof is a divisor argument, not a finite search. This program
checks its off-solution ratio identities and computes minimal rational
interpolation degrees for the six saved characteristic-two certificates.
The ratios at indices 0 and 1 are deliberately omitted. No new HI
existence certificate is claimed. Requires Python and PARI/GP.
"""

import json
from pathlib import Path
import subprocess


GP = r'''
phasecheck(W,d)={
my(n=#W,rr=vector(#W,a,W[a]/W[(a-2)%n+1]));
for(a=1,n-1,
 if(W[a+1]*W[n-a+1]!=d||W[2*a%n+1]!=W[a+1]^4,
  error("norm or Frobenius failure")));
for(a=0,n-1,
 if(rr[2*a%n+1]*rr[(2*a-1)%n+1]!=rr[a+1]^4,
  error("off-solution ratio Frobenius identity")));
for(a=2,n-1,
 if(rr[a+1]!=rr[(1-a)%n+1],error("ratio reflection")));
rr
};

check(data,branch)={
my(n=data[1],degree=#data[3]-1,modulus=Mod(1,2)*Polrev(data[3]),
 z=ffgen(modulus,'z),gen=ffprimroot(z),d=subst(Polrev(data[4]),'x,z),
 row=vector(n,a,subst(Polrev(data[5][a]),'x,z)),W=vector(n),rr,
 ze=gen^((2^degree-1)/n),points=vector(n-2,a,ze^(a+1)),
 K,M,den,num,coeff,ok=0,rmin=-1,H,rootH,bad,
 c=d^2,constant=vector(n,a,if(a==1,z^0,c)));
if(ze^n!=1||ze^(n/3)==1,error("nonprimitive cyclic parameter"));
W[1]=z^0;W[2]=(1/row[3])^(2^(degree-1));
for(a=2,n-1,W[a+1]=W[2]*W[a]/row[a+1]);
rr=phasecheck(W,d);
if(sum(m=0,n-1,W[m+1]^2*W[(1-m)%n+1]*W[(-1-m)%n+1]),
 error("saved certificate fails first Q"));
phasecheck(constant,d);
if(sum(m=0,n-1,constant[m+1]^2*constant[(1-m)%n+1]*constant[(-1-m)%n+1])!=d,
 error("constant-phase Q defect"));
/* Find the first degree allowing P/Q at all nonexceptional points.
   A kernel alone is insufficient: Q must be nonzero at every sample.
   A polynomial curve in the kernel avoids the union of these hyperplanes. */
for(r=0,n-2,
 M=matrix(n-2,2*r+2,a,j,if(j<=r+1,points[a]^(j-1),
  rr[a+2]*points[a]^(j-r-2)));
 K=matker(M);if(matsize(K)[2]==0,next);
 bad=0;
 for(a=1,n-2,
  if(vector(matsize(K)[2],j,
   sum(i=0,r,K[r+2+i,j]*points[a]^i))==vector(matsize(K)[2]),bad=1;break));
 if(bad,next);
 for(j=0,(n-2)*(matsize(K)[2]-1),
  coeff=K*vector(matsize(K)[2],i,(gen^j)^(i-1))~;
  num=sum(i=0,r,coeff[i+1]*x^i);den=sum(i=0,r,coeff[r+2+i]*x^i);
  if(sum(a=1,n-2,subst(den,x,points[a])==0)==0,ok=1;break));
 if(!ok,error("failed finite hyperplane avoidance"));
 rmin=r;break
);
if(rmin<0,error("no rational interpolant"));
if(poldegree(gcd(num,den))>0,error("minimal interpolant not coprime"));
for(a=2,n-1,
 if(subst(num,x,ze^a)/subst(den,x,ze^a)!=rr[a+1],error("bad interpolant")));
H=subst(num,x,x^2)*subst(num,x,ze^-1*x^2)*den^4
 +subst(den,x,x^2)*subst(den,x,ze^-1*x^2)*num^4;
if(H==0&&n>3,error("nonconstant saved solution has global ratio identity"));
if(H,
 if(deriv(H)!=0,error("Frobenius residual not a square"));
 rootH=sum(j=0,poldegree(H)\2,polcoef(H,2*j)^(2^(degree-1))*x^j);
 if(rootH^2!=H,error("bad polynomial square root"));
 for(a=0,n-1,
  if(a!=0&&a!=1&&a!=(n+1)/2,
   if(subst(rootH,x,ze^a),error("missing Frobenius zero"))));
 if(poldegree(rootH)<n-3,error("too many polynomial zeros"))
);
if(4*rmin<n-3,error("uniform patched ratio bound fails"));
print("n=",n," branch=",branch,": minimal patched rational-ratio degree=",rmin,
 "; uniform lower bound=",ceil((n-3)/4),
 "; square-root Frobenius residual degree=",if(H,poldegree(rootH),-1));
};
'''


def main():
    directory = Path(__file__).resolve().parent / 'hi_finite_field_certificates'
    for n, count in [(3, 1), (9, 2), (27, 3)]:
        for branch in range(count):
            data = json.loads((directory / f'hi_finite_field_{n}_char2_{branch}.json').read_text())
            source = GP + f'iferr(check({json.dumps(data)},{branch}),e,print(e);quit(1));\nquit;\n'
            result = subprocess.run(['gp', '-q', '-f'], input=source, text=True,
                                    capture_output=True)
            if result.returncode or result.stderr:
                raise ArithmeticError(result.stdout + result.stderr)
            print(result.stdout, end='', flush=True)
    print('ALL EXACT PATCHED-RATIO CHECKS PASSED; this is an obstruction, not infinitude.')


if __name__ == '__main__':
    main()
