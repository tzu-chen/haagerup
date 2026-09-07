\\ Exact chamber counts for the one-column master-function arrangement.
\\ These count ONE-COLUMN solutions modulo character gauge, not HI categories.
\\ All ranks are computed over Q(zeta_n), with no numerical rank decisions.

hi_column_arrangement(n) = {
  my(r=(n+1)/2, z=Mod(x,polcyclo(n)), C, M, chi=0, bad=0);
  if(n<3 || n%2==0, error("require odd n >= 3"));
  C=matrix(r,r,j,k,z^((j-1)*(k-1))+z^(-((j-1)*(k-1))));
  M=matconcat([matid(r),C]);
  for(mask=0,2^(2*r)-1,
    my(indices=select(j->bittest(mask,j-1),vector(2*r,j,j)));
    my(k=#indices, rk=if(k,matrank(vecextract(M,vector(r,j,j),indices)),0));
    chi+=(-1)^k*t^(r-rk);
    if(rk<min(k,r),bad++);
  );
  my(aff=divrem(chi,t-1), count=(-1)^(r-1)*subst(deriv(chi,t),t,1));
  if(aff[2]!=0, error("central characteristic polynomial lacks t-1"));
  if(count<2^(r-1) || count>binomial(2*r-2,r-1),error("chamber bound failed"));
  if(isprime(n),
    if(bad || count!=binomial(n-1,(n-1)/2),error("prime general-position theorem failed"))
  );
  print("n=",n,"; exact affine characteristic polynomial=",aff[1]);
  print("  one-column solutions=",count,"; nonuniform subsets=",bad);
  [chi,count,bad]
};

hi_column_arrangement_main() = {
  my(cases=if(getenv("HI_COLUMN_ARRANGEMENT_CASES")==0,[3,5,7,9,11,13,15],eval(getenv("HI_COLUMN_ARRANGEMENT_CASES"))));
  print("EXACT ONE-COLUMN ARRANGEMENT COUNTS; no additional Izumi equations asserted.");
  for(j=1,#cases,hi_column_arrangement(cases[j]));
  print("EXACT ARRANGEMENT CHECKS PASSED");
};

if(getenv("HI_COLUMN_ARRANGEMENT_LIBRARY")==0,hi_column_arrangement_main());
