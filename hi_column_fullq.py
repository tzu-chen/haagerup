"""Certify the complete order-13 quadratic-to-cubic implication.

The critical-algebra construction is uniform in prime order. At order 13,
the full quadratic quotient has modular dimension 12, and an independently
certified characteristic-zero cubic orbit supplies the matching lower
bound. No scalar H equation is imposed in either part of this argument.

By default the program rebuilds and checks all critical multiplication
matrices. --algebra-dir reuses a previously checked circuit export.
"""

import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

from hi_column_circuits import construct, krylov_source, run_gp


UPPER_GP = r'''
BfromP(P,g,h)={
 g=g%n;h=h%n;
 if(g==0&&h==0,return(d-2));
 if(g==0||h==0||g==h,return(-1));
 if(g<h,return(P[h+1]/(P[g+1]*P[h-g+1])));
 return(d*P[h+1]*P[g-h+1]/P[g+1]);
};
run_fullq()={
my(ff=factor(F),z,r,P,B,ok,total=0,degrees=List());
if(n!=13||q!=32059||d!=Mod(1153,q)||poldegree(F)!=924,
 error("wrong critical algebra"));
if(poldegree(gcd(F,deriv(F)))>0,error("nonreduced critical algebra"));
for(i=1,matsize(ff)[1],
 z=ffgen(ff[i,1],'z);r=apply(f->subst(f,t,z),rr);P=vector(n,a,z^0);
 if(r[1]!=-1||r[2]!=-1,error("exceptional row values"));
 for(a=2,n-1,
  if(r[a+1]==0||r[a+1]!=r[n+2-a],error("row units or reflection"));
  P[a+1]=P[a]*r[a+1];
 );
 B=matrix(n,n,g,h,BfromP(P,g-1,h-1));ok=1;
 for(g=1,n-1,for(h=1,n-1,
  if(sum(a=0,n-1,B[(g+a)%n+1,h+1]*B[h+1,a+1]),ok=0;break)
 ));
 if(ok,
  total+=poldegree(ff[i,1]);listput(degrees,poldegree(ff[i,1]));
  print("FULL Q FACTOR: degree=",poldegree(ff[i,1]));
 );
);
print("MODULAR FULL-Q ROW DIMENSION=",total,"; factor degrees=",Vec(degrees));
if(total!=12||Vec(degrees)!=[12],error("unexpected full-Q upper bound"));
print("FULL-Q UPPER BOUND 12 VERIFIED WITHOUT H");
};
iferr(run_fullq(),e,print(e);quit(1));
quit;
'''


LOWER_GP = r'''
run_lower()={
my(cert=hi_stark_run(13));
hi_check("row coordinate generates the full absolute degree-24 field",
 poldegree(minpoly(B[2,3]))==24&&poldegree(P)==24);
hi_check("the dimension generates a quadratic subfield",poldegree(minpoly(d))==2);
print("FULL-C ROW LOWER BOUND 12 VERIFIED WITHOUT H");
};
iferr(run_lower(),e,print(e);quit(1));
quit;
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--algebra-dir', type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='hi_fullq13_') as temp:
        directory = Path(temp)
        if args.algebra_dir:
            source = (args.algebra_dir / 'upper13.gp').read_text().split('BfromP(', 1)[0]
            if not re.search(r'q=32059;n=13;d=Mod\(1153,q\);', source):
                raise ValueError('Not the expected previously checked circuit export')
        else:
            q, d, row, *_ = construct(13)
            source = krylov_source(13, q, d, row)
        output = run_gp(source + UPPER_GP, directory, 'fullq_upper13')
        if 'FULL-Q UPPER BOUND 12 VERIFIED WITHOUT H' not in output:
            raise ArithmeticError(output)
        print(output, end='', flush=True)

        path = directory / 'fullq_lower13.gp'
        path.write_text(LOWER_GP)
        library = Path(__file__).resolve().parent / 'hi_stark_seedless.gp'
        env = os.environ.copy()
        env['HI_STARK_LIBRARY'] = '1'
        result = subprocess.run(['gp', '-q', '-f', str(library), str(path)],
                                env=env, capture_output=True, text=True, timeout=600)
        output = result.stdout + result.stderr
        if (result.returncode or '***   at' in output
                or 'FULL-C ROW LOWER BOUND 12 VERIFIED WITHOUT H' not in output):
            raise ArithmeticError(output)
        print(output, end='', flush=True)
    print('EXACT ORDER-13 Q-TO-C IMPLICATION: row dimension 12, phase dimension 156')


if __name__ == '__main__':
    main()
