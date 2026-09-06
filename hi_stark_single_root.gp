\\ Reconstruct every residue stratum from one fourth root and odd norms.
\\ Load the shared library first, then this file:
\\ HI_STARK_LIBRARY=1 HI_SINGLE_ROW_CHECKPOINT=/tmp/hi25_rows.bin \
\\   HI_SINGLE_CONJUGATE_FROBENIUS=/tmp/hi25_conjugate_prime.bin \
\\   gp -q -f hi_stark_seedless.gp hi_stark_single_root.gp
\\ The input row checkpoint must have passed the preceding field checks.

hi_single_scalar(a,v) =
{
  my(j=lift(znlog(Mod(a,n),Mod(ell,n))));
  for(i=1,j,v=hi_aut(phi,v));v;
};

hi_single_period(v) =
{
  my(w=v);
  for(j=1,eulerphi(n),w=hi_aut(phi,w);if(w==v,return(j)));
  error("scalar period does not close");
};

hi_single_quadratic(B,choice=-1) =
{
  my(Bc=mattranspose(B),h);
  for(level=-1,single_exponent-1,
    h=if(level==-1,0,single_prime^level);
    for(g=0,n-1,
      if(sum(j=0,n-1,B[(g+j)%n+1,h+1]*Bc[j+1,h+1])
        !=(d-1)^2*((g==0)-(h==0)/d),
        print("Quadratic failure for sign choice ",choice," at ",[g,h]);return(0))));
  1;
};

hi_single_finish(path) =
{
  [n,ell,P,d,s,phi,bar,sv,Brow]=read(path);
  my(fac=factor(n));
  hi_check("cyclic odd prime-power input",n%2&&matsize(fac)[1]==1);
  single_prime=fac[1,1];single_exponent=fac[1,2];
  hi_fast_auts=List();hi_cache_aut(phi);if(phi!=bar,hi_cache_aut(bar));
  single_untwisted=getenv("HI_SINGLE_UNTWISTED")=="1";
  if(single_exponent>1&&!single_untwisted,
    single_frob_path=getenv("HI_SINGLE_CONJUGATE_FROBENIUS");
    if(type(single_frob_path)!="t_STR"||!#single_frob_path,
      error("set HI_SINGLE_CONJUGATE_FROBENIUS to the checked conjugate-prime Artin map"));
    single_frob=read(single_frob_path);hi_cache_aut(single_frob);
    hi_check("conjugate-prime map is a base-field automorphism commuting with scalar action",
      subst(P,y,Mod(single_frob,P))==0&&hi_aut(single_frob,d)==d
      &&hi_aut(phi,Mod(single_frob,P))==hi_aut(single_frob,Mod(phi,P))));
  D=Brow[3];a=lift(1/Mod(4,n));b=lift(1/Mod(2,n));
  W=d^2*sv[a+1]/(hi_single_scalar(a,D)^2*hi_single_scalar(b,D));
  hi_check("one fourth root of delta squared times the full Stark unit",W^4==d^2*s);
  full_period=hi_single_period(s);wv=vector(n);wv[1]=1;
  for(level=0,single_exponent-1,
    base=single_prime^level;value=W;
    if(level>0,
      low_period=hi_single_period(sv[base+1]);degree=full_period/low_period;
      hi_check("conductor descent degree is odd",type(degree)=="t_INT"&&degree%2);
      value=Mod(1,P);v=W;
      for(j=1,degree,value*=v;for(k=1,low_period,v=hi_aut(phi,v)));
      value*=d^((1-degree)/2));
    lower_s=sv[base+1];
    hi_check(Str("norm-descended fourth root on stratum ",base),value^4==d^2*lower_s);
    if(level>0&&!single_untwisted,
      for(j=1,level,value=hi_aut(single_frob,value);lower_s=hi_aut(single_frob,lower_s));
      print("Applied conjugate-prime Artin twist on stratum ",base));
    u=base;v=value;q=lower_s;
    for(j=1,eulerphi(n/base),wv[u+1]=v;sv[u+1]=q;u=ell*u%n;v=hi_aut(phi,v);q=hi_aut(phi,q));
    hi_check("cochain labels close on the scalar orbit",u==base&&v==value));
  hi_check("all cochain roots and physical norms",vecmin(vector(n-1,g,
    wv[g+1]^4==d^2*sv[g+1]&&wv[g+1]*hi_aut(bar,wv[g+1])==d)));
  hi_check("negation is physical conjugation of the cochain",vecmin(vector(n-1,g,
    wv[n-g+1]==hi_aut(bar,wv[g+1]))));
  base_B=matrix(n,n,g,h,if(g==1&&h==1,d-2,if(g==1||h==1||g==h,-1,
    (d-n)*wv[g]*wv[(h-g)%n+1]*wv[(1-h)%n+1])));
  single_candidates=hi_prime_power_sign_candidates(base_B);
  hi_check("at least one stratum sign passes the necessary linear equation",#single_candidates>0);
  found=0;
  for(candidate_index=1,#single_candidates,
    sign_choice=single_candidates[candidate_index];
    B=matrix(n,n,g,h,if(g==1||h==1||g==h,base_B[g,h],
      base_B[g,h]*(-1)^(bittest(sign_choice,valuation(g-1,single_prime))
        +bittest(sign_choice,valuation((h-g)%n,single_prime))
        +bittest(sign_choice,valuation(h-1,single_prime)))));
    if(hi_single_quadratic(B,sign_choice),found=1;single_passing_sign=sign_choice;break));
  hi_check("an orbit-sign choice satisfies all quadratic equations",found);
  print("Passing orbit-sign choice: ",single_passing_sign);
  hi_check("scalar covariance",vecmin(vector(n^2,i,
    g=(i-1)\n;h=(i-1)%n;hi_aut(phi,B[g+1,h+1])==B[(ell*g)%n+1,(ell*h)%n+1])));
  hi_check("physical Hermitian symmetry",matrix(n,n,g,h,hi_aut(bar,B[g,h]))==mattranspose(B));
  hi_check("rotation symmetry",vecmin(vector(n^2,i,
    g=(i-1)\n;h=(i-1)%n;B[g+1,h+1]==B[(-h)%n+1,(g-h)%n+1])));
  vals=Set(vector(n^2,i,B[(i-1)\n+1,(i-1)%n+1]));
  idx=matrix(n,n,g,h,setsearch(vals,B[g,h]));
  outfile=getenv("HI_SINGLE_OUTPUT");
  if(type(outfile)!="t_STR"||!#outfile,outfile=Str("hi_stark",n,"_certificate.gp"));
  outfd=fileopen(outfile,"w");
  filewrite(outfd,Str([n,ell,P,d,s,phi,bar,vals,idx]));fileclose(outfd);
  print("SINGLE-ROOT PHASE AND QUADRATIC CERTIFICATE SAVED TO ",outfile);
  print("PARTIAL: the cubic stage is still required");
};

{
single_path=getenv("HI_SINGLE_ROW_CHECKPOINT");
if(type(single_path)!="t_STR"||!#single_path,error("set HI_SINGLE_ROW_CHECKPOINT"));
iferr(hi_single_finish(single_path),err,print("FAILED: ",err);quit(1));
quit(0);
}
