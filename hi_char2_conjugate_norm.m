// Exact off-solution checks for an involution that interchanges delta and delta^2.
// These reject two restricted phase constructions, not HI existence.
SetQuitOnError(true);
SetSeed(644);
K<delta> := GF(4); c := delta^2;
R<t> := RationalFunctionField(K);
exception := delta + delta/t + c*t;
conjugate_exception := c + c*t + delta/t;
assert conjugate_exception + c*exception eq t+delta+c/t;
assert t+delta+c/t eq (t+1)*(t+c)/t;
U := delta*(t+delta)/(t+c);
Ubar := c*(t+c)/(t+delta);
assert U*Ubar eq 1;
assert U*Evaluate(U,1/t) eq delta;
assert ((U+1)*(U+delta)/U)^2 eq delta*t^2/(t^2+t+1)^2;
print "EXACT rational exceptional-term, factorization, and Mobius identities passed";

function Residual(W,g,h)
 n := #W;
 return &+[W[m+1]*W[(h-m) mod n+1]*W[(-m-g) mod n+1]*W[(m+g-h) mod n+1]
           : m in [0..n-1]];
end function;

procedure Check(r,n,trials)
 assert IsOdd(r) and IsOdd(n) and n gt 1;
 E<z> := GF(2,2*r); gen := PrimitiveElement(E);
 delta := gen^((#E-1) div 3); c := delta^2;
 bar := func<x | x^(2^r)>;
 assert bar(delta) eq c;
 orbits := [];
 seen := {0};
 for a in [1..n-1] do
  if a in seen then continue; end if;
  orbit := []; b := a;
  repeat Append(~orbit,b); b := (2*b) mod n; until b eq a;
  negative := {(-b) mod n : b in orbit};
  Append(~orbits,<orbit,not IsDisjoint(SequenceToSet(orbit),negative)>);
  seen join:= SequenceToSet(orbit) join negative;
 end for;
 for mode in ["fixed_line","unit_norm"] do
  checks := 0; diagonal_zeros := 0; cross_witnesses := 0;
  for trial in [1..trials] do
   W := [E!1 : a in [0..n-1]];
   for orbit in orbits do
    if orbit[2] then
     seed := c;
    else
     e := GCD(r,#orbit[1]);
     if mode eq "fixed_line" then
      seed := c*gen^(((#E-1) div (2^e-1))*Random(0,2^e-2));
     else
      seed := gen^(((#E-1) div (2^e+1))*Random(0,2^e));
     end if;
    end if;
    value := seed;
    for a in orbit[1] do
     W[a+1] := value;
     W[(-a) mod n+1] := delta/value;
     value := value^4;
    end for;
    assert value eq seed;
   end for;
   assert forall{a : a in [1..n-1] | W[a+1]*W[n-a+1] eq delta};
   assert forall{a : a in [0..n-1] | W[a+1]^4 eq W[(2*a) mod n+1]};
   if mode eq "fixed_line" then
    assert forall{a : a in [1..n-1] | bar(W[a+1]) eq c*W[a+1]};
   else
    assert forall{a : a in [1..n-1] | bar(W[a+1])*W[a+1] eq 1};
   end if;
   for a in [1..n-1] do
    residual := Residual(W,a,a); t := W[a+1]^2;
    assert bar(residual)+c*residual eq t+delta+c/t;
    assert t+delta+c/t eq ((W[a+1]+1)*(W[a+1]+delta)/W[a+1])^2;
    if mode eq "fixed_line" then assert residual ne 0; end if;
    if residual eq 0 then
     assert W[a+1] in {E!1,delta};
     diagonal_zeros +:= 1;
    end if;
    checks +:= 1;
   end for;
   if forall{a : a in [1..n-1] | W[a+1] in {E!1,delta}} then
    a := Rep({a : a in [1..n-1] | W[a+1] eq delta});
    k := 2;
    while W[(k*a) mod n+1] eq delta do k +:= 1; end while;
    g := ((k-1)*a) mod n; h := a;
    witness := Residual(W,g,h);
    assert witness ne 0 and delta*witness+(delta*witness)^2 eq 1;
    cross_witnesses +:= 1;
   end if;
  end for;
  printf "OFF-SOLUTION r=%o n=%o mode=%o checks=%o diagonal_zeros=%o F4_cross_witnesses=%o\n",
         r,n,mode,checks,diagonal_zeros,cross_witnesses;
 end for;
end procedure;

for r in [1,3,5,7], n in [3,7,9,15,23,31,47,71,127] do Check(r,n,8); end for;

for n in [7,23,31,47,71,79,103] do
 assert IsPrime(n) and n mod 8 eq 7;
 r := Order(Integers(n)!2);
 assert IsOdd(r);
 E<z> := GF(2,2*r); gen := PrimitiveElement(E);
 delta := gen^((#E-1) div 3); c := delta^2;
 xi := gen^((#E-1) div n); exponent := (n+3) div 2;
 assert (Integers(n)!2)^exponent eq 4 and IsOdd(exponent);
 input := [xi^(Integers()!((Integers(n)!a)^exponent)) : a in [1..n-1]];
 for mode in ["fixed_line","unit_norm"] do
  W := [E!1] cat [mode eq "fixed_line" select c*x else delta*(x+delta)/(x+c) : x in input];
  assert forall{a : a in [1..n-1] | W[a+1]*W[n-a+1] eq delta};
  assert forall{a : a in [0..n-1] | W[a+1]^4 eq W[(2*a) mod n+1]};
  residual := Residual(W,1,1);
  assert residual ne 0;
  if mode eq "unit_norm" then
   assert residual^(2^r)+c*residual eq delta*input[1]^2/(input[1]^2+input[1]+1)^2;
  end if;
  printf "LEGENDRE n=%o field_degree=%o mode=%o first_Q=false\n",n,2*r,mode;
 end for;
end for;
print "COMPLETE CONJUGATE-NORM CHECKS; no HI nonexistence or infinitude assertion";
quit;
