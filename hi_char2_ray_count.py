"""Compare complete phase counts with the sum over quadratic overorders.

The ray-class degrees are arithmetic theorems. Their equality with the
HI phase counts is checked only at the completed finite orders; it is
not assumed in constructing or verifying the phase certificates.
Requires PARI/GP. Maximal class numbers are certified with bnfcertify.
"""

import subprocess


COUNTS = {3: 2, 5: 4, 7: 6, 9: 12, 11: 12, 13: 12, 15: 24,
          17: 16, 19: 36, 21: 48, 23: 44, 25: 40, 27: 54,
          29: 60, 31: 60, 33: 100}


GP = r'''
arithmetic(n,expected=-1)={
 my(b=bnfinit(x^2-n*x-1,1),D0=b.disc,F=sqrtint((n^2+4)/D0),
 m,phi=eulerphi(n),divs,rows=List(),sumray=0,u,ff,h,local,ray);
 if(bnfcertify(b)!=1,error("uncertified maximal class group"));
 if(F^2*D0!=n^2+4||gcd(F,n)!=1,error("incorrect conductor"));
 m=quadunitindex(D0,F);divs=divisors(F);
 for(j=1,#divs,
  ff=divs[j];u=quadunitindex(D0,ff);
  if(m%u,error("overorder unit index does not divide"));
  local=ff;forprime(p=2,ff,if(ff%p==0,local*=1-kronecker(D0,p)/p));
  h=b.no*local/u;ray=h*phi/(m/u);
  if(denominator(h)!=1||denominator(ray)!=1,error("nonintegral class degree"));
  sumray+=ray;listput(rows,[ff,h,m/u,ray]);
 );
 if(expected>=0&&sumray!=expected,error("finite count comparison failed",[n,sumray,expected]));
 print("CERTIFIED RAY-COUNT ARITHMETIC n=",n,"; fundamental D=",D0,
       "; conductor=",F,"; maximal unit index=",m,
       "; [overorder conductor,class number,unit image order,ray degree]=",Vec(rows),
       "; sum=",sumray,if(expected<0,"; NO HI COUNT ASSERTED","; exact finite HI count matched"));
};
'''


def main():
    for n, count in list(COUNTS.items()) + [(39, -1), (81, -1), (6561, -1)]:
        source = GP + f'iferr(arithmetic({n},{count}),e,print(e);quit(1));\nquit;\n'
        result = subprocess.run(['gp', '-q', '-f'], input=source, text=True,
                                capture_output=True)
        if result.returncode or result.stderr:
            raise ArithmeticError(result.stdout + result.stderr)
        print(result.stdout, end='', flush=True)
    print('ALL FINITE COUNT COMPARISONS PASSED; a uniform HI count or lower bound remains unproved.')


if __name__ == '__main__':
    main()
