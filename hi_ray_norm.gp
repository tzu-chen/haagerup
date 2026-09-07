\\ Norm elements from ray class fields, without Stark polynomials or HI seeds.
\\ These certify W*c(W)=d; they do not assert the additive Izumi identities.
default(parisizemax,3000000000);
default(realprecision,50);
hi_norm_ray(n,verbose=1,explicit_unit=0)={
 if(n<3 || n%2==0,error("the order must be odd and at least 3"));
 my(K=bnfinit(y^2-n*y-1,1),delta=Mod(y,y^2-n*y-1),ray,P,nfL,subs,Mpol,nfM,polrel,emb,disc,chosen,T,ans);
 if(!bnfcertify(K),error("base class-group certificate failed"));
 ray=bnrinit(K,[idealhnf(K,delta-1),[0,1]],1);
 P=bnrclassfield(ray,,2); nfL=nfinit(P);
 print("n=",n," ray=",ray.cyc," absolute degree=",poldegree(P)," signature=",nfL.sign);
 subs=nfsubfields(P,poldegree(P)/2);
 for(j=1,#subs,
   Mpol=subst(subs[j][1],x,y); nfM=nfinit(Mpol);
   if(nfM.r1==poldegree(Mpol),break)
 );
 if(nfM.r1!=poldegree(Mpol),error("totally real fixed field not found"));
 polrel=nffactor(nfM,P)[1,1];
 if(poldegree(polrel)!=2,error("quadratic relative factor not found"));
 emb=nfisincl(z^2-n*z-1,Mpol,2);
 disc=poldisc(polrel);
 for(j=1,#emb,
   my(ok=1,cand=Mod(emb[j],Mpol));
   for(k=1,nfM.r1,
     if(real(subst(lift(disc),y,nfM.roots[k]))<0 && real(subst(lift(cand),y,nfM.roots[k]))<0,ok=0)
   );
   if(ok,chosen=cand;break)
 );
 if(type(chosen)!="t_POLMOD",error("physical quadratic embedding not found"));
 if(chosen^2-n*chosen-1!=0,error("quadratic embedding check failed"));
 if(explicit_unit,
   if(n%4!=3,error("the explicit unit theorem requires n=3 mod 4"));
   my(roots=nfroots(nfM,x^2-(1-chosen)/disc));
   if(#roots!=2,error("explicit quadratic subfield did not embed"));
   ans=[Mod(1+roots[1]*(2*x+polcoef(polrel,1)),polrel),1];
   print("Using the explicit unit 1+sqrt(1-d)"),
   T=rnfisnorminit(nfM,polrel,1); ans=rnfisnorm(T,chosen)
 );
 if(ans[2]!=1 || norm(ans[1])!=chosen,error("exact norm identity failed"));
 print("[ok] fixed-field degree=",poldegree(Mpol),"; exact W*c(W)=d");
 if(verbose,
   print("base polynomial=",Mpol);
   print("relative polynomial=",polrel);
   print("d=",chosen);
   print("W=",ans[1])
 );
 print("EXACT RAY NORM CONSTRUCTION PASSED");
 [Mpol,polrel,chosen,ans[1],P]
};
hi_ray_norm_main()={
 iferr(for(j=1,5,hi_norm_ray([3,5,7,9,11][j])),E,print("FAILED: ",E);quit(1));
 print("ALL RAY NORM CONSTRUCTIONS PASSED");quit(0)
};
if(getenv("HI_RAY_NORM_LIBRARY")!="1",hi_ray_norm_main());
