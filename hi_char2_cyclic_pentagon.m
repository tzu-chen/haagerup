// Explicit quantum A2 intertwiner at the characteristic-two central fixed point.
// This constructs order-five conjugation operators, not HI associators.
// The variable omega is the CENTRAL fixed point. In the HI spectral comparison
// the matching dimension is delta=omega^-1, so t=omega.
SetQuitOnError(true);
procedure CyclicPentagon(n)
 assert IsOdd(n) and n ge 3;
 r := Order(Integers(3*n)!4);
 K<g> := GF(2,2*r);
 generator := PrimitiveElement(K);
 s := generator^((#K-1) div (3*n));
 q := s^3;
 omega := s^n;
 assert Order(s) eq 3*n and Order(q) eq n;
 assert omega^2+omega+1 eq 0;
 Id := IdentityMatrix(K,n);
 X := DiagonalMatrix([s*q^(2*j) : j in [0..n-1]]);
 Y := ZeroMatrix(K,n,n);
 for j in [0..n-1] do Y[(j+1) mod n+1,j+1] := s; end for;
 assert X*Y eq q^2*Y*X and X^n eq omega*Id and Y^n eq omega*Id;
 b := [K!1];
 for j in [0..n-1] do
  Append(~b,b[#b]*(1+q*s*q^(2*j))/s^2);
 end for;
 assert b[n+1] eq 1 and &*b ne 0;
 B := Matrix(K,n,n,[q^(-2*i*j)*b[j+1] : i,j in [0..n-1]]);
 Z := X^-1*(Id+q*Y);
 assert B*X eq Y*B and B*Y eq Z*B;
 variables := [X,Y];
 for j in [1..5] do
  Append(~variables,variables[j]^-1*(Id+q*variables[j+1]));
 end for;
 assert variables[6] eq X and variables[7] eq Y;
 B5 := B^5;
 scalar := B5[1,1];
 assert scalar ne 0 and B5 eq scalar*Id;
 print "CYCLIC PENTAGON n",n,"base degree over F4",r,
       "Weyl, intertwiner, period five, scalar fifth power: PASS";
 // At powers of three r is odd, so the scalar has a unique fifth root in K.
 // Other orders need not satisfy this and are still covered by Ad(B)^5=I.
 if Gcd(5,#K-1) eq 1 then
  B /:= scalar^InverseMod(5,#K-1);
  L<h> := ext<K | 2>;
  BL := ChangeRing(B,L);
  root := PrimitiveElement(L)^((#L-1) div 5);
  assert BL^5 eq IdentityMatrix(L,n);
  multiplicities := [n-Rank(BL-root^j*IdentityMatrix(L,n)) : j in [0..4]];
  adjoint := [&+[multiplicities[i+1]*multiplicities[(i+j) mod 5+1]
                 : i in [0..4]] : j in [0..4]];
  print "CYCLIC SPECTRUM n",n,"B multiplicities",multiplicities,
        "Ad(B) multiplicities",adjoint;
  print "CYCLIC FIFTH-ROOT LABELS n",n,"roots of lambda^2+omega^-1*lambda+1",
        [j : j in [1..4] | root^(2*j)+(L!omega)^-1*root^j+1 eq 0];
 end if;
end procedure;
for n in [3,5,7,9,15,27] do CyclicPentagon(n); end for;
quit;
