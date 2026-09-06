\\ Prime-power field, lower-conductor norm, and one-root construction.
\\ Run with the shared library loaded first:
\\ HI_STARK_LIBRARY=1 HI_STARK_CHECKPOINT=/tmp/hi25_rows.bin gp -q -f hi_stark_seedless.gp hi_stark_prime_power.gp
\\ This stage alone does not certify existence.
\\ Lower-conductor values here are untwisted norm values. The subsequent
\\ hi_stark_single_root.gp applies the necessary numerator-ideal Artin twist.

hi_prime_power_prepare(n0) =
{
  n = n0;
  pp_fac=factor(n);
  hi_check("input is an odd prime power",n>2&&n%2&&matsize(pp_fac)[1]==1);
  pp_prime=pp_fac[1,1];pp_exponent=pp_fac[1,2];pp_unit_order=eulerphi(n);
  print("CASE n = ", n);
  timer = getwalltime();
  hi_fast_auts=List();
  T = y^2-n*y-1; K = bnfinit(T,1); delta = Mod(y,T);
  hi_check("base class/unit computation is certified", bnfcertify(K)==1);
  pp = idealhnf(K,delta-1);
  ray = bnrinit(K,[pp,[0,1]],1);
  S = bnrstarkunit(ray);
  hi_check("returned polynomial has full ray degree", poldegree(S)==ray.no);
  hi_check("returned polynomial is irreducible", matsize(nffactor(K,S))[1]==1);
  hi_check("returned polynomial is reciprocal and monic",
    polcoef(S,poldegree(S))==1 && x^poldegree(S)*subst(S,x,1/x)==S);
  cond = rnfconductor(K,S);
  hi_check("returned field has the intended full ray conductor and degree",
    cond[1]==[pp,[0,1]] && poldegree(S)==ray.no);

  \\ A small inert primitive root gives an intrinsic residue labeling.
  ell = 2;
  while(!isprime(ell) || ell==n || kronecker(K.disc,ell)!=-1
    || znorder(Mod(ell,n))!=pp_unit_order, ell++);
  raw = rnfequation(K,S,1);
  hi_check("relative root is the absolute primitive element", raw[3]==0);
  red = polredbest(raw[1],1);
  P = subst(red[1],x,y);
  s = Mod(subst(lift(red[2]),x,y),P);
  d = subst(lift(raw[2]),x,s);
  F = nfinit(P);
  hi_check("embedded dimension has its defining equation", d^2-n*d-1==0);
  auts = select(a->hi_aut(a,d)==d,nfgaloisconj(F));
  hi_check("field is Galois over the quadratic base", #auts==ray.no);
  phi = hi_frob(ell);
  hi_cache_aut(phi);

  sv=vector(n);sv[1]=1;
  for(pp_level=0,pp_exponent-1,
    pp_base=pp_prime^pp_level;pp_q=n/pp_base;
    pp_value=s;
    if(pp_level>0,
      pp_low_ideal=idealadd(K,pp,pp_q);
      pp_low_ray=bnrinit(K,[pp_low_ideal,[0,1]],1);
      pp_low_S=bnrstarkunit(pp_low_ray);
      hi_check(Str("lower conductor and degree at additive order ",pp_q),
        poldegree(pp_low_S)==pp_low_ray.no
        && rnfconductor(K,pp_low_S)[1]==[pp_low_ideal,[0,1]]);
      pp_step=pp_low_ray.no/K.no;pp_degree=ray.no/pp_low_ray.no;
      pp_value=Mod(1,P);v=s;
      for(pp_j=1,pp_degree,
        pp_value*=v;for(pp_k=1,pp_step,v=hi_aut(phi,v)));
      hi_check(Str("relative norm is exactly a lower-conductor Stark root at order ",pp_q),
        sum(pp_j=0,poldegree(pp_low_S),
          subst(lift(polcoef(pp_low_S,pp_j)),y,d)*pp_value^pp_j)==0));
    u=pp_base;q=pp_value;
    for(i=1,eulerphi(pp_q),sv[u+1]=q;u=(ell*u)%n;q=hi_aut(phi,q));
    hi_check(Str("complete consistent labels at additive order ",pp_q),u==pp_base&&q==pp_value));
  hi_check("every nonzero residue, including nonunits, has a label",vecmin(vector(n-1,g,sv[g+1]!=0)));
  bar = phi;
  for(i=2,pp_unit_order/2,bar=lift(hi_aut(phi,bar)));
  if(bar!=phi,hi_cache_aut(bar));
  hi_check("residue -1 inverts the Stark generator", hi_aut(bar,s)==1/s);
  hi_check("its fixed field is totally real",
    nfinit(minpoly(s+1/s)).sign==[poldegree(P)/2,0]);
  hi_check("all real embeddings of the full field have delta negative",
    #nfeltsign(F,d)>0 && vecmax(nfeltsign(F,d))==-1);
  \\ Consequently bar is actual complex conjugation over delta>0.

  Brow = vector(n); Brow[1] = -1; Brow[2] = -1; m = (n-1)/2;
  root_cache=List();
  pp_root_limit=if(getenv("HI_PP_FULL_ROW")=="1",m+1,2);
  for(h=2,pp_root_limit,
    my(R=d^2*sv[2]*sv[h]/sv[h+1],rr,root=0);
    for(j=1,#root_cache,if(root_cache[j][1]==R,root=root_cache[j][2];break));
    if(root==0,
      rr=nfroots(F,x^4-R);
      hi_check(Str("two exact fourth-root lifts for new row orbit ",h),#rr==2);
      root=Mod(rr[1],P);q=root;
      for(j=1,pp_unit_order,listput(root_cache,[q^4,q]);q=hi_aut(phi,q)));
    hi_check(Str("exact fourth-root lift for row entry ",h),root^4==R);
    Brow[h+1]=root; Brow[n+2-h]=root);
  checkpoint_text=getenv("HI_STARK_CHECKPOINT");
  if(type(checkpoint_text)=="t_STR" && #checkpoint_text,
    writebin(checkpoint_text,[n,ell,P,d,s,phi,bar,sv,Brow]);
    print("Saved exact row checkpoint to ",checkpoint_text));
  print("PRIME-POWER FIELD, LOWER-CONDUCTOR NORM, AND INITIAL ROOT STAGES PASSED");
  [n,ell,P,d,s,phi,bar,sv,Brow];
};


{iferr(pp_checkpoint=hi_prime_power_prepare(25),err,print("FAILED: ",err);quit(1));quit(0);}
