"""Exact checks of the uniform diagonal-cubic/Frobenius identity.

Off-solution checks do not assume Q or Frobenius covariance. Saved full
certificates are then twisted by every cyclic character and uniquely
normalized back to their Frobenius gauge. Requires PARI/GP only.
"""

import json
from pathlib import Path
import subprocess


GP = r'''
conv(a,b)={my(n=#a);vector(n,s,sum(t=0,n-1,a[t+1]*b[(s-1-t)%n+1]))};
sq(a)={vector(#a,j,a[j]^2)};
matrixW(W,d)={my(n=#W);
 matrix(n,n,g,h,if(h==1,if(g==1,d,1),W[g]*W[(h-g)%n+1]/W[h]))/(d-1)
};

residual_checks(n)={
 my(z=ffgen(ffinit(2,12,'z),'z),gen=ffprimroot(z),d=gen^((2^12-1)/3),
 W=vector(n,j,z^0),A,u,v,f,w,zz,q,q2,D,H,raw,e=vector(n,j,if(j==1,z^0,0*z)),
 nonzeroQ=0,nonzeroH=0,inv2=(n+1)/2);
 for(a=1,(n-1)/2,W[a+1]=gen^(a^2+3*a+2);W[n-a+1]=d/W[a+1]);
 A=matrixW(W,d);
 for(g=1,n-1,
  u=vector(n,j,A[j,g+1]);v=vector(n,j,A[g+1,(1-j)%n+1]);
  f=vector(n,j,A[j,2*g%n+1]);w=sq(u);zz=sq(v);
  q=conv(u,v)-e;q2=sq(q);D=conv(f,zz)-w;
  raw=vector(n,s,my(k=(1-s)%n);
   sum(m=0,n-1,A[m+1,2*g%n+1]*A[g+1,(m+k)%n+1]^2)-A[(g+k)%n+1,k+1]^2);
  if(raw!=D,error("diagonal cubic indexing failed"));
  H=f-vector(n,j,A[(j-1)*inv2%n+1,g+1]^4);
  if(D!=conv(H,zz)+conv(w,q2),error("D residual identity failed"));
  if(H!=conv(D,w)+conv(f,q2),error("H residual identity failed"));
  nonzeroQ+=(q!=0*q);nonzeroH+=(H!=0*H)
 );
 if(!nonzeroQ||!nonzeroH,error("off-solution test degenerated"));
 print("EXACT OFF-SOLUTION DIAGONAL-CUBIC IDENTITIES n=",n,
       "; nonzero Q columns=",nonzeroQ,"; nonzero Frobenius columns=",nonzeroH)
};

saved(data,branch)={
 my(n=data[1],degree=#data[3]-1,z=ffgen(Mod(1,2)*Polrev(data[3]),'z),
 gen=ffprimroot(z),d=subst(Polrev(data[4]),'x,z),alpha=gen^((2^degree-1)/n),
 row=vector(n,a,subst(Polrev(data[5][a]),'x,z)),W=vector(n),V,r,chi,U,A);
 W[1]=z^0;W[2]=(1/row[3])^(2^(degree-1));
 for(a=2,n-1,W[a+1]=W[2]*W[a]/row[a+1]);
 A=matrixW(W,d);
 for(g=0,n-1,for(h=0,n-1,
  if(A[g+1,h+1]^4!=A[2*g%n+1,2*h%n+1],error("matrix Frobenius covariance failed"))));
 for(t=0,n-1,
  V=vector(n,a,W[a]*alpha^(t*(a-1)));
  r=vector(n,a,V[a]^4/V[2*(a-1)%n+1]);
  if(r[2]^n!=1,error("Frobenius ratio not a character"));
  for(a=0,n-1,if(r[a+1]!=r[2]^a,error("Frobenius ratio not multiplicative")));
  chi=r[2]^(-(n+1)/2);
  U=vector(n,a,chi^(a-1)*V[a]);
  if(U!=W,error("unique Frobenius gauge recovery failed"));
  if(matrixW(V,d)!=A,error("character gauge changed matrix"))
 );
 print("EXACT UNIQUE FROBENIUS GAUGE n=",n," branch=",branch,
       "; all ",n," character twists recovered; matrix covariance passed")
};
'''


def main():
    calls = [f'residual_checks({n})' for n in [3, 5, 7, 9, 11, 13]]
    directory = Path(__file__).resolve().parent / 'hi_finite_field_certificates'
    for n, count in [(3, 1), (9, 2), (27, 3)]:
        for branch in range(count):
            data = json.loads((directory / f'hi_finite_field_{n}_char2_{branch}.json').read_text())
            calls.append(f'saved({json.dumps(data)},{branch})')
    for call in calls:
        result = subprocess.run(['gp', '-q', '-f'], text=True, capture_output=True,
                                input=GP + f'iferr({call},e,print(e);quit(1));\nquit;\n')
        if result.returncode or result.stderr:
            raise ArithmeticError(result.stdout + result.stderr)
        print(result.stdout, end='', flush=True)
    print('ALL EXACT DIAGONAL-CUBIC/FROBENIUS CHECKS PASSED; infinitude is not proved.')


if __name__ == '__main__':
    main()
