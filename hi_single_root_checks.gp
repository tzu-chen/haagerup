\\ Exact single-root reconstruction and sign-selection checks on saved data.
\\ HI_STARK_LIBRARY=1 gp -q -f hi_stark_seedless.gp hi_single_root_checks.gp
\\ HI_SINGLE_CHECK_CASES='[25]' also needs HI_SINGLE_CONJUGATE_FROBENIUS.

hi_single_saved_check(order) =
{
  [n,ell,P,d,s,phi,bar,vals,idx]=read(Str("hi_stark",order,"_certificate.gp"));
  B=matrix(n,n,g,h,vals[idx[g,h]]);
  hi_fast_auts=List();hi_cache_aut(phi);if(phi!=bar,hi_cache_aut(bar));
  D=B[2,3];inva=lift(1/Mod(4,n));invb=lift(1/Mod(2,n));
  ja=lift(znlog(Mod(inva,n),Mod(ell,n)));
  jb=lift(znlog(Mod(invb,n),Mod(ell,n)));
  sa=s;Da=D;Db=D;
  for(i=1,ja,sa=hi_aut(phi,sa);Da=hi_aut(phi,Da));
  for(i=1,jb,Db=hi_aut(phi,Db));
  W=d^2*sa/(Da^2*Db);
  hi_check(Str("one Kummer root at n=",n),W^4==d^2*s);
  wv=vector(n);wv[2]=W;
  for(a=2,n-1,wv[a+1]=W*wv[a]/B[2,a+1]);
  hi_check("physical norms of the reconstructed cochain",vecmin(vector(n-1,a,
    wv[a+1]*hi_aut(bar,wv[a+1])==d)));
  hi_check("every generic entry equals the single-root coboundary",vecmin(vector(n^2,i,
    g=(i-1)\n;h=(i-1)%n;if(g==0||h==0||g==h,1,
      B[g+1,h+1]*wv[h+1]==wv[g+1]*wv[(h-g)%n+1]))));
  u=1;v=W;scalar_roots_ok=1;
  for(i=1,eulerphi(n),
    if(wv[u+1]!=v,scalar_roots_ok=0);
    u=ell*u%n;v=hi_aut(phi,v));
  hi_check("every unit scalar root label",scalar_roots_ok);
  sign_trace=D+hi_aut(bar,D);
  sign_even=1+sum(m=2,n-2,B[(m+1)%n+1,2]*B[2,m+1]);
  hi_check("the sign-selecting trace is nonzero",sign_trace!=0);
  hi_check("one quadratic equation selects the saved global sign",sign_even==sign_trace);
  hi_check("the globally opposite sign fails that quadratic equation",sign_even+sign_trace!=0);
  hi_check("the linear stratum-sign equation selects only the saved signs",
    hi_prime_power_sign_candidates(B)==[0]);
  if(n==25,
    artin_path=getenv("HI_SINGLE_CONJUGATE_FROBENIUS");
    if(type(artin_path)!="t_STR"||!#artin_path,error("set HI_SINGLE_CONJUGATE_FROBENIUS for n=25"));
    pp_frob_conj=read(artin_path);hi_cache_aut(pp_frob_conj);
    lower_W=Mod(1,P);v=W;
    for(j=1,5,lower_W*=v;for(k=1,4,v=hi_aut(phi,v)));
    lower_W=hi_aut(pp_frob_conj,lower_W/d^2);
    hi_check("the saved nonunit root is exactly the twisted odd norm",lower_W==wv[6]);
    passing_signs=List();
    for(choice=0,3,
      sign_B=matrix(n,n,g,h,if(g==1||h==1||g==h,B[g,h],
        B[g,h]*(-1)^(bittest(choice,valuation(g-1,5))
          +bittest(choice,valuation((h-g)%n,5))+bittest(choice,valuation(h-1,5)))));
      qpass=1;failed_at=[];
      for(level=0,1,
        h=5^level;
        for(g=0,n-1,
          if(sum(m=0,n-1,sign_B[(m+g)%n+1,h+1]*sign_B[h+1,m+1])
            !=(d-1)^2*(g==0),qpass=0;failed_at=[g,h];break));
        if(!qpass,break));
      if(qpass,listput(passing_signs,choice),print("Rejected relative stratum signs ",choice," at ",failed_at)));
    hi_check("only the saved stratum signs satisfy Q at n=25",Vec(passing_signs)==[0]));
  print("SINGLE-ROOT AND SIGN CHECKS PASSED n=",n);
};

{
single_cases=getenv("HI_SINGLE_CHECK_CASES");
if(type(single_cases)!="t_STR"||!#single_cases,single_cases="[19,199]");
single_cases=eval(single_cases);
for(case_index=1,#single_cases,
  iferr(hi_single_saved_check(single_cases[case_index]),err,print("FAILED: ",err);quit(1)));
quit(0);
}
