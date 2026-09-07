// All F2-linear Cayley maps intertwining squaring with fourth powers.
// The inverse norms and Frobenius laws are automatic; Q remains a test.
SetQuitOnError(true);
procedure ProbeMaps(r)
 assert IsOdd(r);
 q := 2^r; n := q+1;
 E<g> := GF(2,4*r); generator := PrimitiveElement(E);
 beta := generator^((#E-1) div 3);
 zeta := generator^((#E-1) div n);
 P<T> := PolynomialRing(E); eta := Roots(T^4+T+1)[1][1];
 smallgen := generator^((#E-1) div (q-1));
 for i in [0..q-2] do
  theta := smallgen^i;
  M := Matrix(GF(2),[Eltseq(theta^(2^j)) : j in [0..r-1]]);
  if Rank(M) eq r then break; end if;
 end for;
 assert Rank(M) eq r;
 coordinates := [];
 for a in [1..n-1] do
  x := 1/(1+zeta^a)+beta;
  assert x^q eq x;
  Append(~coordinates,Solution(M,Vector(GF(2),Eltseq(x))));
 end for;
 halfgen := generator^((#E-1) div (q^2-1));
 seeds := 0; first := 0; full := 0;
 for exponent in [0..q^2-2] do
  v := halfgen^exponent;
  images := [v^(4^i) : i in [0..r-1]];
  if &+images ne 1 then continue; end if;
  seeds +:= 1;
  mapped := [&+[(E!row[i])*images[i] : i in [1..r]] : row in coordinates];
  for gamma in [E!0,E!1,beta,beta^2] do
   W := [E!1] cat [beta^2*(y+gamma+eta)/(y+gamma+eta+1) : y in mapped];
   assert forall{a : a in [1..n-1] | W[a+1]*W[n-a+1] eq beta};
   assert forall{a : a in [0..n-1] | W[a+1]^4 eq W[(2*a) mod n+1]};
   if &+[W[m+1]^2*W[(1-m) mod n+1]*W[(-1-m) mod n+1] : m in [0..n-1]] ne 0 then continue; end if;
   first +:= 1;
   ok := true;
   for a,b in [1..n-1] do
    if &+[W[m+1]*W[(b-m) mod n+1]*W[(-m-a) mod n+1]*W[(m+a-b) mod n+1]
           : m in [0..n-1]] ne 0 then ok := false; break; end if;
   end for;
   print "LINEAR-CAYLEY FIRST Q r",r,"seed exponent",exponent,"gamma",gamma,"full Q",ok;
   if ok then full +:= 1; end if;
  end for;
 end for;
 assert seeds eq 4^(r-1);
 print "LINEAR-CAYLEY COUNTS r",r,"n",n,"seeds",seeds,"candidates",4*seeds,
       "first Q",first,"full Q",full;
end procedure;
for r in [1,3,5] do ProbeMaps(r); end for;
quit;
