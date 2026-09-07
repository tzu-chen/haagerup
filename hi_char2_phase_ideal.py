"""Generate a Magma proof of finite characteristic-two Q => C.

This checks the entire phase ideal, without Frobenius covariance or a
chosen field-degree restriction. The output is a finite-order result.
Run this generator with --source, then run Magma on the generated file.
The cross-free orbit reduction is the one proved in Sections 34--40.
"""

import argparse
from pathlib import Path

from hi_beta_reductions import beta_representatives


MAGMA = r'''
SetQuitOnError(true);
procedure Check(n, representatives)
 K<w>:=GF(4); R:=PolynomialRing(K,n-1,"grevlex");
 W:=[R!1] cat [R.i:i in [1..n-1]];
 rel:=[W[a+1]*W[n-a+1]-w:a in [1..(n-1) div 2]];
 for g in [1..(n-1) div 2] do
  for h in [g..(n-1) div 2] do
   Append(~rel,&+[W[m+1]*W[(h-m) mod n+1]*W[(-m-g) mod n+1]
                  *W[(m+g-h) mod n+1]:m in [0..n-1]]);
  end for;
 end for;
 I:=ideal<R|rel>;
 print "BUILD n",n,"relations",#rel;
 t:=Cputime(); basis:=GroebnerBasis(I);
 assert Dimension(I) eq 0;
 length:=Dimension(quo<R|I>);
 assert length gt 0;
 print "FINITE NONEMPTY n",n,"basis",#basis,"length",length,"CPU",Cputime(t);
 // Independently check coverage of every omitted nonzero Q.
 for g,h in [1..n-1] do
  f:=&+[W[m+1]*W[(h-m) mod n+1]*W[(-m-g) mod n+1]
         *W[(m+g-h) mod n+1]:m in [0..n-1]];
  assert NormalForm(f,I) eq 0;
 end for;
 for quad in representatives do
  g,h,k,l:=Explode(quad);
  a:=[0,(k-g) mod n,(l-h) mod n]; c:=[(g+h) mod n,(-k) mod n,(-l) mod n];
  assert &and[(ai+ci) mod n ne 0:ai in a,ci in c];
  s:=&+[(&*[W[(m+ai) mod n+1]:ai in a])
         *(&*[W[(-m+ci) mod n+1]:ci in c]):m in [0..n-1]];
  p:=&*[W[(ai+ci) mod n+1]:ai in a,ci in c];
  // w^2 = w-1 in characteristic two, so the balanced cubic is s=p.
  assert NormalForm(s-p,I) eq 0;
 end for;
 print "ALL Q AND CROSS-FREE C IDEAL MEMBERSHIPS PASSED n",n,
       "cubic orbit representatives",#representatives,"length",length;
end procedure;
'''


def source(orders):
    commands = []
    for n in orders:
        representatives, _ = beta_representatives(n)
        commands.append(f'Check({n},' + str([list(q) for q in representatives]) + ');')
    return MAGMA + '\n'.join(commands) + '\nquit;\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[3, 5, 7, 9, 11, 13])
    parser.add_argument('--source', type=Path, required=True)
    args = parser.parse_args()
    args.source.write_text(source(args.orders))


if __name__ == '__main__':
    main()
