// Exact checks of the uniform conic and trace-zero Cayley coordinates.
SetQuitOnError(true);
procedure Check(r)
 assert IsOdd(r);
 q := 2^r; n := q+1;
 E<g> := GF(2,4*r); gen := PrimitiveElement(E);
 delta := gen^((#E-1) div 3); zeta := gen^((#E-1) div n);
 P<T> := PolynomialRing(E); eta := Roots(T^4+T+1)[1][1];
 assert eta^(q^2) eq eta+1;
 Trace2 := func<x | &+[x^(2^j) : j in [0..r-1]]>;
 X := [1/(1+zeta^a)+delta : a in [1..n-1]];
 assert #SequenceToSet(X) eq q;
 for a in [1..n-1] do
  assert X[a]^q eq X[a];
  assert X[n-a] eq X[a]+1;
  assert X[(2*a) mod n] eq X[a]^2+1;
  for b in [1..n-1] do
   if (a+b) mod n eq 0 then
    assert X[a]+X[b]+1 eq 0;
   else
    assert X[(a+b) mod n] eq (X[a]*X[b]+1)/(X[a]+X[b]+1);
   end if;
  end for;
 end for;
 tracezero := Setseq({x^2+x : x in X});
 assert #tracezero eq q div 2;
 todo := SequenceToSet(tracezero); cycles := [];
 U := AssociativeArray(); Infinite := {};
 while #todo gt 0 do
  y := Rep(todo); orbit := [y]; next := y^2;
  while next ne y do Append(~orbit,next); next := next^2; end while;
  todo diff:= SequenceToSet(orbit); d := #orbit;
  assert r mod d eq 0;
  seed := gen^((#E-1) div (4^d-1));
  for j in [1..d] do U[orbit[j]] := seed^(4^(j-1)); end for;
  if IsEven(#cycles) then Infinite join:= SequenceToSet(orbit); end if;
  Append(~cycles,d);
 end while;
 for use_boundary in [false,true] do
  W := [E!1];
  for x in X do
   y := x^2+x;
   assert U[y^2] eq U[y]^4;
   if use_boundary and y in Infinite then
    Append(~W,delta^2);
   else
    v := Trace2(x)+U[y];
    w := delta^2*(v+eta)/(v+eta+1);
    assert eta+w/(w+delta^2) eq v;
    Append(~W,w);
   end if;
  end for;
  for a in [1..n-1] do
   assert W[a+1]*W[n-a+1] eq delta;
   assert W[a+1]^4 eq W[(2*a) mod n+1];
  end for;
 end for;
 assert 2*&+cycles eq q;
 print "EXACT CAYLEY GEOMETRY r",r,"n",n,"trace-zero Frobenius cycle lengths",Sort(cycles);
 print "FINITE CHART BINARY DIMENSION",q,"PROJECTIVE NORM-FROBENIUS COUNT",&*[4^d+1 : d in cycles];
end procedure;
for r in [1,3,5,7,9] do Check(r); end for;
print "ALL CONIC, TRACE-ZERO, AND FINITE/INFINITE NORM-FROBENIUS CHECKS PASSED; Q NOT ASSUMED";
quit;
