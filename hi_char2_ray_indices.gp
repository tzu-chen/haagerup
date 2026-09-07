\\ Certified ray-class indices to compare with Section 58's finite searches.
\\ These are arithmetic counts, not a construction of HI solutions.

default(parisizemax,1000000000);

check_ray_indices()={
my(n,B,arch,R,a,ord,unit,pr,beta,clbeta,betord,clord,
 expected=[1,2,3,8,25,36,84]);
for(k=1,7,
 n=3^k;B=bnfinit(y^2-n*y-1,1);
 if(!bnfcertify(B),error("class group or units not certified"));
 if(B.disc!=n^2+4,error("nonmaximal displayed quadratic order"));
 unit=bnfisunit(B,y);
 if(#unit!=2||abs(unit[1])!=1,error("dimension is not a fundamental unit"));
 arch=vector(2,j,B.roots[j]>0);
 if(vecsum(arch)!=1,error("wrong infinite place"));
 R=bnrinit(B,[idealhnf(B,y-1),arch],1);
 a=bnrisprincipal(R,2,0);
 ord=lcm(vector(#a,j,R.cyc[j]/gcd(R.cyc[j],a[j])));
 pr=select(p->idealval(B,y+1,p)>0,idealprimedec(B,3));
 if(#pr!=1,error("conjugate prime not identified"));
 beta=bnrisprincipal(R,pr[1],0);clbeta=bnfisprincipal(B,pr[1],0);
 clord=if(#clbeta,lcm(vector(#clbeta,j,B.cyc[j]/gcd(B.cyc[j],clbeta[j]))),1);
 betord=lcm(vector(#beta,j,R.cyc[j]/gcd(R.cyc[j],beta[j])));
 if(clord!=k||betord!=k*ord,error("incorrect class or ray order of conjugate prime"));
 if(vecmax(vector(#a,j,(k*beta[j]-a[j])%R.cyc[j]))!=0,
  error("conjugate-prime power is not Frobenius at (2)"));
 if(ord!=eulerphi(n)||R.no!=B.no*eulerphi(n),error("unexpected ray index"));
 if(R.no/ord!=expected[k],error("unexpected certified class number"));
 print("n=",n,"; discriminant=",B.disc,"; class group=",B.cyc,
  "; ray group=",R.cyc,"; order of Frobenius at (2)=",ord,
  "; index=",R.no/ord,"; conjugate-prime order=",betord,
  "; cycles of length ",k," on Frobenius cosets=",R.no/betord);
);
};

check_nonmaximal_order()={
my(k=8,n=3^k,D=n^2+4,D0=quaddisc(D),f=sqrtint(D/D0),
 B=bnfinit(y^2-y-(D0-1)/4,1),d=f*y+(n-f)/2,
 R=bnrinit(B,f,1),gens=znstar(f,1).gen,H=matdiagonal(R.cyc),a,p,ord);
if(!bnfcertify(B),error("nonmaximal example not certified"));
\\ Pic(O_f) is the maximal-order ray group modulo f, divided by
\\ the image of (Z/fZ)^*. H presents that quotient lattice.
for(j=1,#gens,
 a=bnrisprincipal(R,lift(gens[j]),0);H=mathnf(matconcat([H,a]));
);
p=select(p->idealval(B,d+1,p)>0,idealprimedec(B,3))[1];
a=H^-1*bnrisprincipal(R,p,0);ord=denominator(a);
if(f!=5||B.no!=96||matdet(H)!=384||ord!=k,error("nonmaximal-order class check"));
print("NONMAXIMAL ORDER: n=",n,"; conductor=",f,
 "; maximal class number=",B.no,"; order class number=",matdet(H),
 "; conjugate-prime class order=",ord);
};

iferr(check_ray_indices();check_nonmaximal_order(),e,print(e);quit(1));
print("RAY INDICES CERTIFIED; HI ORBIT COUNTS ABOVE 27 ARE NOT ESTABLISHED");
quit;
