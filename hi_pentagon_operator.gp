\\ Exact checks of the uniform transfer-operator reduction of (C).
\\ Load the libraries first:
\\ HI_STARK_LIBRARY=1 HI_RAY_NORM_LIBRARY=1 HI_UNIT_LIBRARY=1 gp -q -f \
\\   hi_stark_seedless.gp hi_ray_norm.gp hi_ray_unit_search.gp hi_pentagon_operator.gp
\\ A trace-of-fifth-power certificate is checked independently of the
\\ original cubic loops. The uniform equivalence is proved in Section 50.
hi_pentagon_operator_check(p)={
  my(w=hi_unit_setup(p),B=hi_unit_matrix(w),A,R,Rstar,R2,R3,R5,U,V,J,T5);
  if(!hi_quadratic(B),w=-w;B=hi_unit_matrix(w));
  hi_check("complete quadratic input for the operator theorem",hi_quadratic(B));
  A=B/(d-1);
  R=matrix(n^2,n^2,i,j,
    if((i-1)%n==(j-1)\n,A[(i-1)%n+1,((i-1)\n+(j-1)%n)%n+1],0));
  U=vector(n^2,i,((i-1)%n==0))~;
  V=vector(n^2,i,((i-1)\n==0))~;
  Rstar=matrix(n^2,n^2,i,j,hi_aut(bar,R[j,i]));J=matid(n^2);
  hi_check("exact two rank-one unitarity defects",
    R*Rstar==J-U*U~/d&&Rstar*R==J-V*V~/d);
  R2=R^2;R3=R2*R;
  hi_check("the universal three-dimensional invariant subspace",
    R*V==-U/d&&R2*U==V-U/d);
  T5=sum(i=1,n^2,sum(j=1,n^2,R2[i,j]*R3[j,i]));
  hi_check("exact scalar fifth-trace cubic certificate",T5==d^2-5+6/d^2);
  R5=R3*R2;
  hi_check("equivalent degree-eight operator polynomial",
    (R5-J)*(R3+R/d+J/d)==matrix(n^2,n^2));
  print("PENTAGON OPERATOR CERTIFICATE PASSED: n=",n,"; dimension of unitary part=",n^2-3);
};
hi_pentagon_operator_main()={
  iferr(for(j=1,3,hi_pentagon_operator_check([3,5,7][j])),
    E,print("FAILED: ",E);quit(1));
  print("ALL EXACT PENTAGON OPERATOR CHECKS PASSED");quit(0)
};
hi_pentagon_operator_main();
