\\ Identify the conjugate-prime Artin map for the order-25 construction.
\\ Load hi_stark_seedless.gp first with HI_STARK_LIBRARY=1.
\\ Input: HI_SINGLE_ROW_CHECKPOINT; output: HI_SINGLE_CONJUGATE_FROBENIUS.
\\ The auxiliary prime has an etale power basis, so no ramified-prime
\\ reduction of the absolute polynomial is used.

hi_stark25_artin(path,output) =
{
  [n,ell,P,d,s,phi,bar,sv,Brow]=read(path);
  hi_check("order-25 input with rational-2 scalar",n==25&&ell==2);
  hi_fast_auts=List();hi_cache_aut(phi);hi_cache_aut(bar);
  T=y^2-n*y-1;K=bnfinit(T,1);delta=Mod(y,T);
  aa=idealhnf(K,delta-1);ray=bnrinit(K,[aa,[0,1]],1);
  hi_check("cyclic ray group of order 40",ray.cyc==[40]);
  pp_conjugate=idealadd(K,5,delta+1);
  pp_coordinate=bnrisprincipal(ray,pp_conjugate,0)[1];
  auts=select(a->hi_aut(a,d)==d,nfgaloisconj(P));
  PD=poldisc(P);aux=2;found=0;
  while(!found,
    aux=nextprime(aux+1);
    if(kronecker(K.disc,aux)!=1||PD%aux==0,next);
    fm=factormod(P,aux)[1,1];md=Mod(lift(d)*Mod(1,aux),fm);
    rootbase=-1;
    for(i=0,aux-1,if(md==i,rootbase=i;break));
    if(rootbase==-1,error("base root not recovered modulo the auxiliary prime"));
    qideal=idealadd(K,aux,delta-rootbase);
    cq=bnrisprincipal(ray,qideal,0)[1];
    if(gcd(cq,ray.no)!=1,next);
    found=1);
  print("auxiliary rational prime, base root, ray coordinates: ",
    [aux,rootbase,cq,pp_coordinate]);
  matches=select(a->Mod(a*Mod(1,aux),fm)==Mod(y*Mod(1,aux),fm)^aux,auts);
  hi_check("unique exact auxiliary Frobenius in an etale power basis",#matches==1);
  pp_frob_conj=Mod(y,P);aux_frob=matches[1];hi_cache_aut(aux_frob);
  pp_power=lift(Mod(pp_coordinate,ray.no)/cq);
  for(i=1,pp_power,pp_frob_conj=hi_aut(aux_frob,pp_frob_conj));
  pp_frob_conj=lift(pp_frob_conj);
  hi_check("conjugate-prime Frobenius squares to the rational-2 Frobenius",
    hi_aut(pp_frob_conj,Mod(pp_frob_conj,P))==Mod(phi,P));
  hi_check("the conjugate-prime twist changes the lower-conductor generator",
    hi_aut(pp_frob_conj,sv[6])!=sv[6]);
  writebin(output,pp_frob_conj);
  print("CONJUGATE-PRIME ARTIN AUTOMORPHISM SAVED TO ",output);
};

{
artin_input=getenv("HI_SINGLE_ROW_CHECKPOINT");
artin_output=getenv("HI_SINGLE_CONJUGATE_FROBENIUS");
if(type(artin_input)!="t_STR"||!#artin_input,error("set HI_SINGLE_ROW_CHECKPOINT"));
if(type(artin_output)!="t_STR"||!#artin_output,error("set HI_SINGLE_CONJUGATE_FROBENIUS"));
iferr(hi_stark25_artin(artin_input,artin_output),err,print("FAILED: ",err);quit(1));
quit(0);
}
