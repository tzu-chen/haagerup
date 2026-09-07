// Bounded probes of phase extraction from the cyclic pentagon eigenprojectors.
// Every reported full point must be independently certified before acceptance.
SetQuitOnError(true);
procedure Probe(n)
 K<g> := GF(2,2*n);
 generator := PrimitiveElement(K);
 s := generator^((#K-1) div (3*n)); q := s^3; omega := s^n;
 b := [K!1];
 for j in [0..n-1] do Append(~b,b[#b]*(1+q*s*q^(2*j))/s^2); end for;
 assert b[n+1] eq 1;
 B := Matrix(K,n,n,[q^(-2*i*j)*b[j+1] : i,j in [0..n-1]]);
 scalar := (B^5)[1,1];
 assert B^5 eq scalar*IdentityMatrix(K,n);
 B /:= scalar^InverseMod(5,#K-1);
 L<h> := ext<K | 2>;
 B := ChangeRing(B,L); q := L!q; omega := L!omega;
 delta := omega^-1;
 root := PrimitiveElement(L)^((#L-1) div 5);
 powers := [B^j : j in [0..4]];
 normexponent := (#L-1) div (4^(2*n div 3)-1);
 counts := [0 : i in [1..8]];
 for j in [0..4] do
  projector := &+[root^(-j*k)*powers[k+1] : k in [0..4]];
  assert projector^2 eq projector;
  vectors := [[projector[a+1,c+1] : a in [0..n-1]] : c in [0..n-1]];
  Append(~vectors,[&+[projector[k+1,k+1]*q^(2*a*k) : k in [0..n-1]]
                    : a in [0..n-1]]);
  for vi in [1..#vectors], normchoice in [0..1] do
   vector := vectors[vi];
   if normchoice eq 1 then vector := [x^normexponent : x in vector]; end if;
   for shift in [0..n-1] do
    counts[1+4*normchoice] +:= 1;
    if &*vector eq 0 then continue; end if;
    W := [vector[(a+shift) mod n+1]/vector[shift+1] : a in [0..n-1]];
    normvalue := W[2]*W[n];
    if exists{a : a in [1..n-1] | W[a+1]*W[n-a+1] ne normvalue} then continue; end if;
    scale := (delta/normvalue)^(#L div 2);
    W := [L!1] cat [scale*W[a+1] : a in [1..n-1]];
    assert forall{a : a in [1..n-1] | W[a+1]*W[n-a+1] eq delta};
    counts[2+4*normchoice] +:= 1;
    if &+[W[m+1]^2*W[(1-m) mod n+1]*W[(-1-m) mod n+1] : m in [0..n-1]] ne 0 then continue; end if;
    counts[3+4*normchoice] +:= 1;
    ok := true;
    for a,c in [1..n-1] do
     if &+[W[m+1]*W[(c-m) mod n+1]*W[(-m-a) mod n+1]*W[(m+a-c) mod n+1]
            : m in [0..n-1]] ne 0 then ok := false; break; end if;
    end for;
    if ok then
     counts[4+4*normchoice] +:= 1;
     print "PROBE FULL Q n",n,"eigenvalue",j,"vector",vi,"norm",normchoice,"shift",shift;
    end if;
   end for;
  end for;
 end for;
 print "PROBE COUNTS n",n,"direct [trials,norm,firstQ,fullQ]",counts[1..4],
       "relative norm [trials,norm,firstQ,fullQ]",counts[5..8];
end procedure;
for n in [3,9,27] do Probe(n); end for;
quit;
