"""Generate exact canonical Q-ideal computations for Magma.

Frobenius covariance is imposed explicitly. Positive length gives full-Q
points in this gauge; C must still be proved or independently verified.
This is an alternative to Boolean search, not an infinitude theorem.
"""

import argparse
from pathlib import Path

from hi_char2_general_search import quadratic_representatives


PREAMBLE = r'''
SetQuitOnError(true);
SetSeed(80071);
procedure Check(n, pairs)
 K<w> := GF(4);
 R := PolynomialRing(K,n-1,"grevlex");
 W := [R!1] cat [R.i : i in [1..n-1]];
 rel := [W[a+1]*W[n-a+1]-w : a in [1..(n-1) div 2]];
 rel cat:= [W[a+1]^4-W[(2*a) mod n+1] : a in [1..n-1]];
 for pair in pairs do
  g,h := Explode(pair);
  Append(~rel, &+[W[m+1]*W[(h-m) mod n+1]*W[(-m-g) mod n+1]
                 *W[(m+g-h) mod n+1] : m in [0..n-1]]);
 end for;
 I := ideal<R|rel>;
 print "CANONICAL BUILD n",n,"relations",#rel,"Q representatives",#pairs;
 t := Cputime();
 basis := GroebnerBasis(I);
 print "CANONICAL BASIS n",n,"size",#basis,"dimension",Dimension(I),"time",Cputime(t);
 if Dimension(I) eq 0 then
  print "CANONICAL DEGREE",Dimension(quo<R|I>);
 end if;
 print "CUBIC MEMBERSHIP HAS NOT BEEN TESTED IN THIS RUN";
end procedure;
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int, default=[9, 27])
    parser.add_argument('--source', type=Path, required=True)
    args = parser.parse_args()
    calls = []
    for n in args.orders:
        if n < 3 or n % 2 == 0:
            raise ValueError('Require odd n>=3')
        pairs = quadratic_representatives(n)
        encoded = ','.join(f'<{g},{h}>' for g, h in pairs)
        calls.append(f'Check({n}, [{encoded}]);')
    args.source.write_text(PREAMBLE+'\n'+'\n'.join(calls)+'\nquit;\n')
    print(f'Wrote {args.source}; full-Q Frobenius-covariant ideals at {args.orders}.')


if __name__ == '__main__':
    main()
