"""Compare the natural Weyl basis of the cyclic pentagon with HI transfer.

The natural-basis matrix is explicit and sparse. These tests quantify why
an abstract spectral match does not itself extract the HI phases.
"""

import argparse
import json
from pathlib import Path


MAGMA = r'''
SetQuitOnError(true);
procedure Check(n, branch, modulus, delta_coeffs, row_coeffs)
 F := GF(2); P0<T> := PolynomialRing(F);
 K<z> := ext<F | P0!modulus>;
 delta := Evaluate(P0!delta_coeffs,z);
 row := [Evaluate(P0!v,z) : v in row_coeffs];
 products := [K!1 : a in [0..n-1]];
 for a in [2..n-1] do products[a+1] := products[a]*row[a+1]; end for;
 A := ZeroMatrix(K,n,n);
 for g,h in [0..n-1] do
  if g eq 0 and h eq 0 then value := delta-2;
  elif g eq 0 or h eq 0 or g eq h then value := K!(-1);
  elif g lt h then value := products[h+1]/(products[g+1]*products[h-g+1]);
  else value := delta*products[h+1]*products[g-h+1]/products[g+1];
  end if;
  A[g+1,h+1] := value/(delta-1);
 end for;
 // The saved n=3^k fields contain n-th roots; a cubic extension adds s.
 L<y> := ext<K | 3>;
 A := ChangeRing(A,L); delta := L!delta; t := 1/delta;
 s := PrimitiveElement(L)^((#L-1) div (3*n));
 if s^n ne t then s := s^-1; end if;
 assert s^n eq t and Order(s) eq 3*n;
 q := s^3;
 P<x> := PolynomialRing(L);
 coefficients := ZeroMatrix(L,n,n);
 f := P!1;
 for b in [0..n-1] do
  if b gt 0 then f *:= 1+s*q^(1-2*b)*x; end if;
  for h in [0..n-1] do
   coefficients[b+1,h+1] := s^(-2*b)*q^(b*h)*Coefficient(f,h);
   assert (coefficients[b+1,h+1] ne 0) eq (h le b);
  end for;
 end for;
 nn := n^2;
 support := 0;
 for a,b,c,e in [0..n-1] do
  v := (b eq c select A[b+1,(a+e) mod n+1] else L!0)
       +(a eq 0 select t*A[c+1,e+1] else L!0)
       +(b eq 0 select t^2*A[c+1,e+1] else L!0)
       +(b eq 0 and c eq 0 select t^2 else L!0)
       +(e eq 0 select t*A[b+1,a+1] else L!0)
       +(c eq 0 select t^2*A[b+1,a+1] else L!0);
  if v ne 0 then support +:= 1; end if;
 end for;
 ranks := [];
 for b in [0..n-1] do
  block := Matrix(L,n,n,[coefficients[b+1,(a+e) mod n+1]-A[b+1,(a+e) mod n+1]
                        : a,e in [0..n-1]]);
  Append(~ranks,Rank(block));
 end for;
 assert support ge (n-1)^2*(3*n-4);
 assert support eq 5*n^3-11*n^2+11*n-4;
 assert support gt n^2*(n+1) div 2;
 assert &+ranks ge n;
 print "BASIS COMPARISON n",n,"branch",branch,"HI corrected support",support,
       "cyclic support",n^2*(n+1) div 2,"block difference ranks",ranks;
 if n le 9 then
  U := ZeroMatrix(L,n,n);
  for j in [0..n-1] do U[(j+1) mod n+1,j+1] := 1; end for;
  Z := DiagonalMatrix([q^(2*j) : j in [0..n-1]]);
  vals := [L!1];
  for j in [0..n-1] do Append(~vals,vals[#vals]*(1+q*s*q^(2*j))/s^2); end for;
  assert vals[n+1] eq 1;
  B := Matrix(L,n,n,[q^(-2*i*j)*vals[j+1] : i,j in [0..n-1]]);
  basis := [q^(-a*b)*U^a*Z^(-b) : a,b in [0..n-1]];
  for c,e in [0..n-1] do
   expected := &+[coefficients[c+1,(a+e) mod n+1]*basis[a*n+c+1] : a in [0..n-1]];
   assert B*basis[c*n+e+1]*B^-1 eq expected;
  end for;
  print "DIRECT WEYL-BASIS INTERTWINING PASSED n",n,"branch",branch;
  xs := [s*Z,s*U];
  for j in [1..3] do Append(~xs,xs[j]^-1*(IdentityMatrix(L,n)+q*xs[j+1])); end for;
  rays := [<1,0>,<0,1>,<-1,0>,<-1,-1>,<0,-1>];
  theta := []; middle := (n-1) div 2;
  for ai,bi in [0..n-1] do
   a := ai le middle select ai else ai-n;
   b := bi le middle select bi else bi-n;
   for j in [1..5] do
    v := rays[j]; w := rays[j mod 5+1];
    p := a*w[2]-b*w[1]; r := v[1]*b-v[2]*a;
    if p ge 0 and r ge 0 then
     Append(~theta,q^(-p*r)*xs[j]^p*xs[j mod 5+1]^r); break;
    end if;
   end for;
  end for;
  V := Transpose(Matrix(L,[Eltseq(t) : t in theta]));
  assert Rank(V) eq nn;
  Ctheta := V^-1*Transpose(Matrix(L,[Eltseq(B*t*B^-1) : t in theta]));
  R := Matrix(L,nn,nn,[((i-1) mod n eq (j-1) div n)
       select A[(i-1) mod n+1,((i-1) div n+(j-1) mod n) mod n+1]
       else L!0 : i,j in [1..nn]]);
  print "CLUSTER BASIS COMPARISON n",n,"branch",branch,
        "support",#[a : a in Eltseq(Ctheta) | a ne 0],
        "rank(Ctheta-R)",Rank(Ctheta-R);
 end if;
end procedure;
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    args = parser.parse_args()
    folder = Path(__file__).with_name('hi_finite_field_certificates')
    calls = []
    for n, branch in [(3, 0), (9, 0), (9, 1), (27, 0), (27, 1), (27, 2)]:
        data = json.loads((folder/f'hi_finite_field_{n}_char2_{branch}.json').read_text())
        calls.append(f'Check({n},{branch},'+','.join(json.dumps(v) for v in data[2:])+');')
    args.source.write_text(MAGMA+'\n'+'\n'.join(calls)+'\nquit;\n')


if __name__ == '__main__':
    main()
