\\ Exact checks accompanying the uniform n=3 mod 4 ray-unit theorem.
\\ The conductor inclusion follows from the displayed integral quadratic
\\ order, whose discriminant is 1-d. No class-field computation is needed.
default(parisizemax,1000000000);
hi_explicit_ray_unit_test(p)={
  my(d=Mod(y,y^2-p*y-1),theta=x^2-d*x+((p+1)/4)*d,
    r=Mod(x,x^2+d-1),w=1+r,wb=1-r,c,Q,expected,e,Qminus);
  if(p%4!=3||!isprime(p),error("the correlation check requires a prime 3 mod 4"));
  if(poldisc(theta)!=1-d,error("integral-order discriminant identity failed"));
  if(w*wb!=d,error("unit norm failed"));
  if(norm(norm(w))!=-1,error("absolute unit norm failed"));
  c=vector(p,j,if(j==1,-1,1+kronecker(j-1,p)*r));
  Q=sum(m=0,p-1,c[m+1]^2*c[(1-m)%p+1]*c[(-1-m)%p+1]);
  e=kronecker(2,p);
  expected=if(e==1,2*p+2-(p+6)*d,2*p-14+(10-p)*d);
  if(Q!=expected||Q==0,error("explicit diagonal obstruction failed"));
  c=vector(p,j,if(j==1,-1,-c[j]));
  Qminus=sum(m=0,p-1,c[m+1]^2*c[(1-m)%p+1]*c[(-1-m)%p+1]);
  if(Qminus!=2*p+2-(p+2)*d||Qminus==0,error("negative seed obstruction failed"));
  print("p=",p," integral-order discriminant=1-d; unit norm=d; Q11(+)=",expected,
    "; Q11(-)=",Qminus);
};
hi_explicit_ray_unit_main()={
  iferr(forprime(p=3,100,if(p%4==3,hi_explicit_ray_unit_test(p))),
    E,print("FAILED: ",E);quit(1));
  print("ALL EXPLICIT RAY UNIT AND DIAGONAL OBSTRUCTION CHECKS PASSED");quit(0)
};
hi_explicit_ray_unit_main();
