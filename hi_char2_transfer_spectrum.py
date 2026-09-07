"""Generate sparse-transfer spectral checks for saved characteristic-2 points.

At a complete Q/C point, the corrected pentagon spectrum can be recovered
from five ranks of R-lambda I, without forming R^6. This does not construct
new Q/C points. The input certificates were independently checked earlier.
"""

import argparse
import json
from pathlib import Path


PREAMBLE = r'''
SetQuitOnError(true);
procedure Spectrum(n, branch, modulus, delta_coeffs, row_coeffs)
 F := GF(2);
 P0<T> := PolynomialRing(F);
 K<z> := ext<F | P0!modulus>;
 delta := Evaluate(P0!delta_coeffs,z);
 t := 1/delta;
 assert t^2+t+1 eq 0;
 row := [Evaluate(P0!v,z) : v in row_coeffs];
 products := [K!1 : a in [0..n-1]];
 for a in [2..n-1] do
  products[a+1] := products[a]*row[a+1];
 end for;
 A := ZeroMatrix(K,n,n);
 for g,h in [0..n-1] do
  if g eq 0 and h eq 0 then
   value := delta-2;
  elif g eq 0 or h eq 0 or g eq h then
   value := K!(-1);
  elif g lt h then
   value := products[h+1]/(products[g+1]*products[h-g+1]);
  else
   value := delta*products[h+1]*products[g-h+1]/products[g+1];
  end if;
  A[g+1,h+1] := value/(delta-1);
 end for;
 nn := n^2;
 R := ZeroMatrix(K,nn,nn);
 for a,b,e in [0..n-1] do
  R[a*n+b+1,b*n+e+1] := A[b+1,(a+e) mod n+1];
 end for;
 Id := IdentityMatrix(K,nn);
 root := PrimitiveElement(K)^((#K-1) div 5);
 assert root^5 eq 1 and root ne 1;
 print "SPECTRAL BUILD n",n,"branch",branch,"size",nn;
 stamp := Cputime();
 mults := [];
 corrections := [];
 for j in [0..4] do
  lambda := root^j;
  correction := j eq 0 select 1 else
       (lambda^2+t*lambda+1 eq 0 select 1 else 0);
  Append(~corrections,correction);
  Append(~mults,nn-Rank(R-lambda*Id)+correction);
 end for;
 assert &+mults eq nn;
 assert mults[2] eq mults[5] and mults[3] eq mults[4];
 if n le 9 then
  Pent := R^6;
  assert Pent^5 eq Id;
  assert mults eq [nn-Rank(Pent-root^j*Id) : j in [0..4]];
 end if;
 print "SPECTRAL RESULT n",n,"branch",branch,"multiplicities",mults,
       "Jordan corrections",corrections,"CPU seconds",Cputime(stamp);
end procedure;
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    args = parser.parse_args()
    folder = Path(__file__).with_name('hi_finite_field_certificates')
    commands = []
    for n, branch in [(3, 0), (9, 0), (9, 1), (27, 0), (27, 1), (27, 2)]:
        data = json.loads((folder/f'hi_finite_field_{n}_char2_{branch}.json').read_text())
        assert data[0:2] == [n, 2]
        commands.append(f'Spectrum({n},{branch},'+','.join(json.dumps(v) for v in data[2:])+');')
    args.source.write_text(PREAMBLE+'\n'+'\n'.join(commands)+'\nquit;\n')
    print(f'Wrote {args.source}; six saved certificates, no new existence claim.')


if __name__ == '__main__':
    main()
