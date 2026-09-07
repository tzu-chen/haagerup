// Norm/Frobenius candidates at n=2^r+1 from a normal-basis permutation.
// A candidate is accepted only after the additional additive equations.
SetQuitOnError(true);
procedure Probe(r)
 assert IsOdd(r);
 q := 2^r; n := q+1;
 E<g> := GF(2,4*r);
 generator := PrimitiveElement(E);
 beta := generator^((#E-1) div 3);
 zeta := generator^((#E-1) div n);
 P<T> := PolynomialRing(E);
 eta := Roots(T^4+T+1)[1][1];
 assert eta^4 eq eta+1;
 smallgen := generator^((#E-1) div (q-1));
 normal := 0; selfdual := 0; first := 0; complete := 0;
 for exponent in [0..q-2] do
  theta := smallgen^exponent;
  basis := [theta^(2^i) : i in [0..r-1]];
  M := Matrix(GF(2),[Eltseq(v) : v in basis]);
  if Rank(M) ne r then continue; end if;
  normal +:= 1;
  dual := forall{j : j in [0..r-1] |
       &+[(theta*basis[j+1])^(2^k) : k in [0..r-1]] eq (j eq 0 select E!1 else E!0)};
  if dual then selfdual +:= 1; end if;
  images := [theta^(2^((2*i) mod r)) : i in [0..r-1]];
  mapped := [];
  for a in [1..n-1] do
   x := 1/(1+zeta^a)+beta;
   assert x^q eq x;
   coordinates := Solution(M,Vector(GF(2),Eltseq(x)));
   Append(~mapped,&+[(E!coordinates[i])*images[i] : i in [1..r]]);
  end for;
  for gamma in [E!0,E!1,beta,beta^2] do
   W := [E!1] cat [beta^2*(v+gamma+eta)/(v+gamma+eta+1) : v in mapped];
   assert forall{a : a in [1..n-1] | W[a+1]*W[n-a+1] eq beta};
   assert forall{a : a in [0..n-1] | W[a+1]^4 eq W[(2*a) mod n+1]};
   f := &+[W[m+1]^2*W[(1-m) mod n+1]*W[(-1-m) mod n+1] : m in [0..n-1]];
   if f ne 0 then continue; end if;
   first +:= 1;
   ok := true;
   for a,b in [1..n-1] do
    if &+[W[m+1]*W[(b-m) mod n+1]*W[(-m-a) mod n+1]*W[(m+a-b) mod n+1]
           : m in [0..n-1]] ne 0 then ok := false; break; end if;
   end for;
   print "NORMAL-BASIS FIRST Q r",r,"theta exponent",exponent,"selfdual",dual,
         "gamma",gamma,"fullQ",ok;
   if ok then complete +:= 1; end if;
  end for;
 end for;
 print "NORMAL-BASIS COUNTS r",r,"n",n,"normal theta",normal,
       "selfdual theta",selfdual,"first Q",first,"full Q",complete;
end procedure;
for r in [1,3,5] do Probe(r); end for;
quit;
