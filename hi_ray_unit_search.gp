\\ Search the relative unit lattice of a prescribed ray field.
\\ Run with both libraries loaded first:
\\ HI_STARK_LIBRARY=1 HI_RAY_NORM_LIBRARY=1 gp -q -f \
\\   hi_stark_seedless.gp hi_ray_norm.gp hi_ray_unit_search.gp
\\ HI_UNIT_CASES='[13,17]' selects cases. HI_UNIT_CERTIFY=1 also certifies
\\ completeness of the absolute unit group (potentially very expensive).
\\ HI_UNIT_EXPLICIT=1 uses the explicit norm unit when p=3 mod 4.
\\ HI_UNIT_COMPARE_SAVED=1 transfers a saved complete certificate by an
\\ exact field isomorphism, instead of repeating its large Q/C calculation.
\\ Numerical logarithms select candidates; EVERY accepted Q/C identity is
\\ checked exactly. Neither shortest-vector completeness nor a uniform
\\ shortest-unit-to-Izumi theorem is asserted by this computation.
default(realprecision,100);

hi_unit_setup(p)={
  my(data=hi_norm_ray(p,0,getenv("HI_UNIT_EXPLICIT")=="1"),rnf,red,root,w);
  if(!isprime(p)||p==2,error("this search currently requires an odd prime"));
  n=p;hi_fast_auts=List();
  rnf=rnfinit(nfinit(data[1]),data[2],1);
  red=polredbest(rnf.polabs,1);P=subst(red[1],x,y);
  root=Mod(subst(lift(red[2]),x,y),P);
  w=subst(lift(rnfeltreltoabs(rnf,data[4])),x,root);
  d=subst(lift(rnfeltreltoabs(rnf,data[3])),x,root);
  F=nfinit(P);auts=select(a->hi_aut(a,d)==d,nfgaloisconj(F));
  ell=2;
  while(!isprime(ell)||ell==n||kronecker(n^2+4,ell)!=-1||znorder(Mod(ell,n))!=n-1,ell++);
  phi=hi_frob(ell);hi_cache_aut(phi);
  bar=lift(Mod(y,P));for(j=1,(n-1)/2,bar=lift(hi_aut(phi,bar)));
  hi_cache_aut(bar);
  my(full=Mod(y,P));for(j=1,n-1,full=hi_aut(phi,full));
  hi_check("Artin generator closes on the entire field",full==Mod(y,P));
  hi_check("physical conjugation is a nontrivial involution",
    Mod(bar,P)!=Mod(y,P)&&hi_aut(bar,bar)==Mod(y,P));
  hi_check("initial exact norm",w*hi_aut(bar,w)==d);
  w;
};

hi_unit_matrix(w)={
  my(Wv=vector(n),u0=1,tt=w);
  for(j=1,n-1,Wv[u0+1]=tt;u0=u0*ell%n;tt=hi_aut(phi,tt));
  if(u0!=1||tt!=w,error("phase orbit did not close"));
  matrix(n,n,g,h,if(g==1&&h==1,d-2,
    if(g==1||h==1||g==h,Mod(-1,P),Wv[g]*Wv[(h-g)%n+1]/Wv[h])));
};

hi_unit_complete_check(w)={
  my(B=hi_unit_matrix(w),Bc,reps);
  hi_check("selected unit has exact norm d",w*hi_aut(bar,w)==d);
  hi_check("all multiplier covariance entries",
    matrix(n,n,g,h,hi_aut(phi,B[g,h])-B[(ell*(g-1))%n+1,(ell*(h-1))%n+1])==matrix(n,n));
  hi_check("all quadratic identities",hi_quadratic(B));
  Bc=matrix(n,n,g,h,hi_aut(bar,B[g,h]));reps=hi_beta_reps(n);
  for(j=1,#reps,if(!hi_cubic_at(B,Bc,reps[j]),error(Str("cubic failure ",reps[j]))));
  hi_check(Str("all cubic identities via ",#reps," balanced-beta representatives"),1);
  print("absolute trace W=",trace(w),"; absolute trace W^2/d=",trace(w^2/d));
};

hi_unit_saved_comparison(order)={
  my(context=[P,d,phi,bar,ell,hi_fast_auts],old=read(Str("hi_stark",order,"_certificate.gp")),
    os,D,sa,Da,Db,ja,jb,W,mp,powers,mat,rd,rphi,alphaW,steps,answer);
  if(old[1]!=order,error("saved certificate has the wrong order"));
  P=old[3];d=old[4];phi=old[6];bar=old[7];ell=old[2];os=old[5];
  hi_fast_auts=List();hi_cache_aut(phi);hi_cache_aut(bar);
  D=old[8][old[9][2,3]];
  ja=lift(znlog(1/Mod(4,order),Mod(ell,order)));
  jb=lift(znlog(1/Mod(2,order),Mod(ell,order)));
  sa=os;Da=D;Db=D;
  for(j=1,ja,sa=hi_aut(phi,sa);Da=hi_aut(phi,Da));
  for(j=1,jb,Db=hi_aut(phi,Db));
  W=d^2*sa/(Da^2*Db);
  hi_check("saved unit fourth power and norm",W^4==d^2*os&&W*hi_aut(bar,W)==d);
  mp=minpoly(W,x);
  hi_check("saved unit generates the full field",poldegree(mp)==poldegree(P));
  powers=vector(poldegree(P));powers[1]=Mod(1,P);
  for(j=2,#powers,powers[j]=powers[j-1]*W);
  mat=matrix(#powers,#powers,i,j,polcoef(lift(powers[j]),i-1));
  rd=Polrev(matsolve(mat,vector(#powers,j,polcoef(lift(d),j-1))~),x);
  steps=lift(znlog(Mod(context[5],order),Mod(ell,order)));
  alphaW=W;for(j=1,steps,alphaW=hi_aut(phi,alphaW));
  rphi=Polrev(matsolve(mat,vector(#powers,j,polcoef(lift(alphaW),j-1))~),x);
  hi_check("exact base-field expression in the saved unit",subst(rd,x,W)==d);
  hi_check("exact Artin expression in the saved unit",subst(rphi,x,W)==alphaW);
  answer=[mp,rd,rphi];[P,d,phi,bar,ell,hi_fast_auts]=context;answer;
};

hi_unit_matches_saved(w,data)={
  subst(data[1],x,w)==0&&subst(data[2],x,w)==d
    &&subst(data[3],x,w)==hi_aut(phi,w);
};

hi_unit_search(p)={
  my(w0=hi_unit_setup(p),bnfL,u,r,C,ker,v,coord,kap,logs,gram,change,
    radius,sv,scores,cc,w,initial,selected=List(),visited=List(),completed=0,
    limit=10000,cap=100000,best,minimum,cutoff,cls,certificate=0,
    compare_saved=getenv("HI_UNIT_COMPARE_SAVED")=="1",comparison);
  if(!compare_saved,
    initial=hi_unit_matrix(w0);
    print("Initial norm candidate: Q(+)=",hi_quadratic(initial,1),
      " Q(-)=",hi_quadratic(hi_unit_matrix(-w0),1)));
  bnfL=bnfinit(P,1);
  if(getenv("HI_UNIT_CERTIFY")=="1",
    hi_check("certified full absolute unit group",bnfcertify(bnfL));certificate=1);
  print("Absolute unit basis completeness certified: ",certificate);
  hi_check("initial norm element is integral and is a unit",
    denominator(nfalgtobasis(F,w0))==1&&abs(norm(w0))==1);
  u=bnfL.fu;r=#u;
  C=matrix(r,r,i,j,bnfisunit(bnfL,hi_aut(bar,u[j]))[i]);
  for(j=1,r,
    coord=bnfisunit(bnfL,hi_aut(bar,u[j]));
    hi_check(Str("exact unit conjugation column ",j),
      hi_aut(bar,u[j])==(-1)^coord[r+1]*prod(i=1,r,u[i]^coord[i])));
  hi_check("free unit conjugation squares to identity",C^2==matid(r));
  ker=matkerint(C+matid(r));
  v=vector(matsize(ker)[2],k,prod(j=1,r,u[j]^ker[j,k]));
  hi_check("expected relative unit rank",#v==poldegree(P)/4);
  for(j=1,#v,hi_check(Str("relative unit norm ",j),v[j]*hi_aut(bar,v[j])==1));
  coord=bnfisunit(bnfL,w0^2/d);kap=matsolve(ker,vecextract(coord,vector(r,j,j)));
  hi_check("integral exact twice-offset",denominator(kap)==1);
  print("Relative unit rank=",#v,"; twice-offset=",kap~);
  logs=matrix(F.r1,#v,i,j,log(abs(subst(lift(v[j]),y,F.roots[i]))));
  gram=logs~*logs;change=qflll(gram,1);
  hi_check("lattice basis change is unimodular",abs(matdet(change))==1);
  v=vector(#v,j,prod(k=1,#v,v[k]^change[k,j]));
  gram=change~*gram*change;coord=change^-1*kap;
  kap=vector(#v,j,coord[j]%2)~;cc=(kap-coord)/2;
  w0*=prod(j=1,#v,v[j]^cc[j]);
  hi_check("recentered exact free exponents",
    matsolve(ker,vecextract(bnfisunit(bnfL,w0^2/d),vector(r,j,j)))==change*kap);
  if(kap==0,error("zero parity coset requires a separate zero-vector branch"));
  radius=1.01*(kap~*gram*kap);
  sv=qfminim(gram,radius,limit,2)[3];scores=List();
  for(k=1,matsize(sv)[2],cc=sv[,k];
    if(vector(#v,j,(cc[j]-kap[j])%2)==vector(#v),listput(scores,[cc~*gram*cc,cc])));
  if(#scores==0,error("bounded numerical search found no coset representative"));
  scores=vecsort(Vec(scores),1);best=scores[1][1];
  \\ Refine the radius so a truncated initial enumeration is never reported
  \\ as a complete shell. All completeness here concerns floating arithmetic.
  sv=qfminim(gram,best*1.000001,cap,2)[3];
  if(matsize(sv)[2]>=cap,error("refined enumeration was truncated"));
  scores=List();
  for(k=1,matsize(sv)[2],cc=sv[,k];
    if(vector(#v,j,(cc[j]-kap[j])%2)==vector(#v),listput(scores,[cc~*gram*cc,cc])));
  if(#scores==0,error("refined shell is empty"));
  scores=vecsort(Vec(scores),1);minimum=scores[1][1];cutoff=minimum*(1+1e-20);
  print("Numerical lowest squared doubled-log score=",minimum);
  print("Refined sphere vectors modulo +/-=",matsize(sv)[2]);
  if(compare_saved,comparison=hi_unit_saved_comparison(p));
  for(k=1,#scores,
    if(scores[k][1]>cutoff,break);
    cc=(scores[k][2]-kap)/2;w=w0*prod(j=1,#v,v[j]^cc[j]);
    my(qpos,qneg);
    if(compare_saved,
      qpos=hi_unit_matches_saved(w,comparison);qneg=hi_unit_matches_saved(-w,comparison);
      print("Lowest-shell vector ",k,": exact saved-certificate match (+)=",qpos," (-)=",qneg),
      qpos=hi_quadratic(hi_unit_matrix(w),1);qneg=hi_quadratic(hi_unit_matrix(-w),1);
      print("Lowest-shell vector ",k,": Q(+)=",qpos," Q(-)=",qneg));
    if(!qpos&&!qneg,next);
    if(qneg,w=-w);listput(selected,w);
    my(seen=0);
    for(j=1,#visited,for(t=1,#auts,if(hi_aut(auts[t],visited[j])==w,seen=1;break))); 
    if(!seen,
      if(compare_saved,
        hi_check("exact isomorphism transports the complete saved Izumi certificate",
          hi_unit_matches_saved(w,comparison)),hi_unit_complete_check(w));
      listput(visited,w);completed++);
  );
  hi_check("at least one complete Izumi solution was obtained",completed>0);
  print("RAY UNIT SEARCH PASSED: n=",n,"; accepted shell vectors=",#selected,
    "; exact Galois orbits=",completed);
};

hi_ray_unit_main()={
  my(cases=if(getenv("HI_UNIT_CASES"),eval(getenv("HI_UNIT_CASES")),[3,5,7,11,13,17,29]));
  iferr(for(j=1,#cases,hi_unit_search(cases[j])),E,print("FAILED: ",E);quit(1));
  print("ALL REQUESTED RAY UNIT SEARCHES PASSED");quit(0)
};
if(getenv("HI_UNIT_LIBRARY")!="1",hi_ray_unit_main());
