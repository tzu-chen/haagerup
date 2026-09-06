\\ Exact arithmetic for an infinite supply of candidate odd HI orders.
\\ Run: gp -q -f hi_pell_ray.gp
\\ This verifies arithmetic, not existence of fusion categories at these n.

pell_check(label, condition) =
{
  if(!condition, error(Str("check failed: ",label)));
};

pell_ray_check(m) =
{
  my(delta=eps^m, n=trace(eps^m), fm=fibonacci(m),
     fm1=fibonacci(m-1), a, pp, ray, beta=-eps, M=M0^m, r, bracket);
  pell_check("admissible exponent",m>1 && m%2 && m%3);
  pell_check("odd Lucas order",n%2 && n==delta-1/delta);
  pell_check("Fibonacci expansion",delta==fm*eps+fm1);
  pell_check("maximal-order index is coprime to n",gcd(fm,n)==1);
  a=Mod(1-fm1,n)/Mod(fm,n);
  pell_check("residue of epsilon has exact order m",znorder(a)==m);
  pp=idealhnf(K,delta-1);
  pell_check("modulus norm equals n",idealnorm(K,pp)==n);
  ray=bnrinit(K,[pp,[0,1]],1);
  pell_check("ray degree is phi(n)/m",ray.no==eulerphi(n)/m);
  pell_check("both real places give the same ray order",
    bnrinit(K,[pp,[1,1]],1).no==ray.no);

  \\ Use the fixed maximal-order lattice Z+Z beta, not Z+Z(-delta),
  \\ whose conductor in O_K is Fibonacci(m).
  r=-[fm1+1,fm]~/n;
  bracket=r[2]*beta-r[1];
  pell_check("fixed RM point",(M[1,1]*beta+M[1,2])/(M[2,1]*beta+M[2,2])==beta);
  pell_check("stabilizer automorphy factor",M[2,1]*beta+M[2,2]==delta^(-2));
  pell_check("stabilizer fixes all denominator-n characteristics",Mod(M,n)==Mod(matid(2),n));
  pell_check("correct denominator parameter",bracket==delta/(delta-1));
  pell_check("correct positive numerator label",delta*(delta-1)*bracket==delta^2);
  print("m=",m,"; n=",n,"; factor(n)=",factor(n),
    "; ray_group=",ray.cyc,"; degree=",ray.no,
    "; unit_image_order=",m,"; order_conductor=",fm);
};

{
K=bnfinit(y^2-y-1,1);eps=Mod(y,y^2-y-1);M0=[1,1;1,2];
iferr(
  pell_check("certified class number one",bnfcertify(K)==1 && K.no==1);
  for(i=1,8,pell_ray_check([5,7,11,13,17,19,23,25][i]));
  print("ALL PELL/RAY ARITHMETIC CHECKS PASSED"),
  pell_error,print("FAILED: ",pell_error);quit(1));
quit(0);
}
