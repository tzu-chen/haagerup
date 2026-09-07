"""Test a rational-function recurrence on a fixed characteristic-two curve.

Section 61 proves the elliptic parametrization of Frobenius-covariant,
norm-normalized phases. The recurrence tested here gives complete HI
certificates at 3, 9 and 27, but fails the first quadratic at every
primitive order-81 point. It is not an infinitude construction.

The formulas contain no saved HI data. Every full-Q candidate is exported
to a temporary JSON file and checked by the independent complete verifier.
Requirements: Python standard library and PARI/GP.
"""

import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from hi_finite_field_certificate import verify


GP = r'''
encode(p,d)={vector(max(0,poldegree(p))+1,j,
 my(c=polcoef(p,j-1));
 if(c==0,0,if(c==1,1,if(c==d,2,if(c==d^2,3,error("non-F4 coefficient"))))))};
check(n,k,outdir)={
my(deg=4*n/3,modulus=ffinit(2,deg,'z),z=ffgen(modulus,'z),
 gen=ffprimroot(z),d=gen^((2^deg-1)/3),c=d^2,
 E=ellinit([0,0,1,0,d]),vv=ellgenerators(E),co=(2^(deg/2)-1)/n,
 P=ellmul(E,vv[1],co),Q=ellmul(E,vv[2],co),pairing,
 seen=Map(),functions=Map(),polys=List(),aa,r,num,den,key,
 root,u,xx,yy,W=vector(n),ok,first=0,total=0,count=0,
 pair,kk,nn,certificate,row,path);
if(ellmul(E,P,n)!=[0]||ellmul(E,Q,n)!=[0],error("bad torsion"));
pairing=ellweilpairing(E,P,Q,n);
if(pairing^n!=1||pairing^(n/3)==1,error("dependent torsion basis"));
for(i=0,2,
 aa=d^i;r=aa^2;
 for(j=2,k,
  r=subst(r,x,aa*(x+c));
  r=c^2*r^3+aa^2*r^2+c/x+c;
 );
 if(k==2&&r!=c/x,error("second recurrence value"));
 if(k==3&&r!=(c*x^4+x^3+x^2+x+c)/(x^4+c*x^3+c^2*x^2+x),
  error("third recurrence value"));
 num=numerator(r);den=denominator(r);num/=pollead(den);den/=pollead(den);
 key=[encode(num,d),encode(den,d)];
 if(!mapisdefined(functions,key),mapput(functions,key,1);listput(polys,[num,den]));
);
for(pa=0,n-1,for(pb=0,n-1,
 if(pa%3==0&&pb%3==0,next);
 pair=[pa,pb];if(mapisdefined(seen,pair),next);
 kk=pair;for(i=1,2*n/3,mapput(seen,kk,1);kk=2*kk%n);
 root=elladd(E,ellmul(E,P,pa),ellmul(E,Q,pb));
 u=root;xx=vector(n-1);yy=xx;
 for(a=1,n-1,
  xx[a]=u[1];yy[a]=u[2];
  if(ellmul(E,u,2)!=[u[1]^4,u[2]^4],error("Frobenius is not doubling"));
  u=elladd(E,u,root);
 );
 for(i=1,#polys,
  total++;W[1]=z^0;ok=1;
  for(a=1,n-1,
   den=subst(polys[i][2],x,xx[a]);
   num=yy[a]*den+subst(polys[i][1],x,xx[a]);
   if(num==0||num+den==0,ok=0;break);
   W[a+1]=d^2*num/(num+den);
  );if(!ok,error("unexpected phase zero or pole"));
  for(a=1,n-1,
   if(W[a+1]*W[n-a+1]!=d||W[2*a%n+1]!=W[a+1]^4,
    error("phase norm or Frobenius failure"));
  );
  if(sum(m=0,n-1,W[m+1]^2*W[(1-m)%n+1]*W[(-1-m)%n+1]),next);
  first++;nn=n;
  while(nn>1,
   kk=n/nn;
   for(g=1,n-1,
    if(sum(m=0,n-1,W[m+1]*W[(kk-m)%n+1]*W[(-g-m)%n+1]*W[(m+g-kk)%n+1]),
     ok=0;break);
   );
   if(!ok,break);nn/=3;
  );
  if(!ok,next);
  count++;
  row=vector(n,a,if(a<=2,z^0,W[2]*W[a-1]/W[a]));
  certificate=[n,2,vector(deg+1,j,lift(polcoef(modulus,j-1))),
   vector(deg,j,lift(polcoef(d.pol,j-1))),
   vector(n,a,vector(deg,j,lift(polcoef(row[a].pol,j-1))))];
  path=Str(outdir,"/elliptic_",n,"_",count,".json");
  write(path,certificate);
  print("FULL Q: n=",n," function=",i," torsion coordinates=",[pa,pb]);
 );
));
if(#seen!=8*n^2/9,error("incomplete primitive-point orbit enumeration"));
print("ELLIPTIC SEARCH: n=",n," functions=",#polys,
 " evaluations=",total," firstQ=",first," allQ=",count);
if(n<=27&&count==0,error("lost known finite solution"));
if(n==81&&first!=0,error("new first-Q survivor: inspect before reporting obstruction"));
};
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', choices=[3, 9, 27, 81],
                        default=[3, 9, 27, 81])
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='hi_char2_elliptic_') as temp:
        directory = Path(temp)
        for n in args.orders:
            k = {3: 1, 9: 2, 27: 3, 81: 4}[n]
            source = ('default(parisizemax,1000000000);\n' + GP
                      + f'iferr(check({n},{k},{json.dumps(temp)}),e,print(e);quit(1));\nquit;\n')
            path = directory / 'elliptic.gp'
            path.write_text(source)
            result = subprocess.run(['gp', '-q', '-f', str(path)],
                                    capture_output=True, text=True, check=True)
            if 'ELLIPTIC SEARCH:' not in result.stdout:
                raise ArithmeticError(result.stdout + result.stderr)
            print(result.stdout, end='', flush=True)
            for certificate in sorted(directory.glob(f'elliptic_{n}_*.json')):
                verify(certificate, directory)
    print('FINITE CERTIFICATES AND ORDER-81 RECURRENCE OBSTRUCTION VERIFIED')


if __name__ == '__main__':
    main()
