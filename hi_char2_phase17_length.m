// Exact Q-algebra length; combine with the independently classified C scheme.
SetQuitOnError(true);
SetSeed(68069);
procedure Check(n)
 K<w>:=GF(4); R:=PolynomialRing(K,n-1,"grevlex");
 W:=[R!1] cat [R.i:i in [1..n-1]];
 rel:=[W[a+1]*W[n-a+1]-w:a in [1..(n-1) div 2]];
 for g in [1..(n-1) div 2] do
  for h in [g..(n-1) div 2] do
   Append(~rel,&+[W[m+1]*W[(h-m) mod n+1]*W[(-m-g) mod n+1]*W[(m+g-h) mod n+1]:m in [0..n-1]]);
  end for;
 end for;
 I:=ideal<R|rel>;
 print "BUILD n",n,"relations",#rel;
 t:=Cputime(); B:=GroebnerBasis(I);
 print "BASIS n",n,"size",#B,"dimension",Dimension(I),"time",Cputime(t);
 if Dimension(I) eq 0 then print "DEGREE",Dimension(quo<R|I>); end if;
end procedure;
Check(9);
Check(13);
Check(17);
quit;
