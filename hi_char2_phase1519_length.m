// Full Q algebra, with no Frobenius equations or extension-degree cutoff.
// A length of 360 at n=15 or 684 at n=19 would equal the independent
// complete cubic point count; a larger length requires further analysis.
SetQuitOnError(true);
SetSeed(68069);
procedure Check(n)
 K<w> := GF(4);
 R := PolynomialRing(K,n-1,"grevlex");
 W := [R!1] cat [R.i : i in [1..n-1]];
 rel := [W[a+1]*W[n-a+1]-w : a in [1..(n-1) div 2]];
 for g in [1..(n-1) div 2] do
  for h in [g..(n-1) div 2] do
   Append(~rel, &+[W[m+1]*W[(h-m) mod n+1]*W[(-m-g) mod n+1]
                  *W[(m+g-h) mod n+1] : m in [0..n-1]]);
  end for;
 end for;
 I := ideal<R|rel>;
 print "BUILD n",n,"relations",#rel;
 t := Cputime();
 basis := GroebnerBasis(I);
 print "BASIS n",n,"size",#basis,"dimension",Dimension(I),"time",Cputime(t);
 if Dimension(I) eq 0 then
  print "DEGREE",Dimension(quo<R|I>);
 end if;
end procedure;
Check(15);
Check(19);
quit;
