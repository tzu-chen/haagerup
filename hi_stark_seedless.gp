\\ Construct and certify HI matrices directly from PARI Stark polynomials.
\\ Run: gp -q -f hi_stark_seedless.gp
\\ One case: HI_STARK_CASES='[17]' gp -q -f hi_stark_seedless.gp
\\ Requires PARI/GP 2.17.4 (bnrstarkunit). No phase seeds or recognized HI
\\ polynomials enter the construction. Every assertion after bnrstarkunit
\\ is exact; the word "Stark" does not assert the general Stark conjecture.
\\ See Sections 28--40 of haagerup_izumi_class_field_stark_notes.md.
\\ HI_STARK_FULL_CUBIC=1 also runs the older, unreduced cubic loop.
\\ HI_STARK_LIBRARY=1 loads the routines without running any cases.
\\
\\ The main routine uses global working variables, so run cases sequentially.
\\ On any failure the top-level handler exits with status 1. In particular,
\\ an unsupported new case cannot silently count as a successful certificate.

default(parisizemax, 4000000000);
default(nbthreads, 1);
default(threadsizemax, 536870912);
default(realprecision, 80);

hi_check(label, condition) =
{
  if(!condition, error(Str("check failed: ", label)));
  print("[ok] ", label);
};

hi_aut(a, v) =
{
  my(w=lift(v),j);
  if(type(w)!="t_POL",return(w));
  for(j=1,#hi_fast_auts,if(a==hi_fast_auts[j][1],
    return(Mod(Polrev(hi_fast_auts[j][2]
      *vector(poldegree(P),i,polcoef(w,i-1))~,y),P))));
  subst(w,y,Mod(a,P));
};

hi_cache_aut(a) =
{
  my(deg=poldegree(P),powers=vector(poldegree(P)),v=Mod(1,P));
  for(j=1,deg,powers[j]=lift(v);v*=Mod(a,P));
  listput(hi_fast_auts,[a,matrix(deg,deg,i,j,polcoef(powers[j],i-1))]);
};

hi_frob(ell) =
{
  my(pr = nfmodprinit(F, idealprimedec(F, ell)[1]), matches = List(), good);
  \\ Test the entire integral basis, avoiding a possible index divisor of a
  \\ particular primitive-element polynomial. ell is inert in the base.
  for(i = 1, #auts,
    good=1;
    for(j=1,#F.zk,
      if(nfmodpr(F,hi_aut(auts[i],F.zk[j]),pr)
        != nfmodpr(F,F.zk[j],pr)^(ell^2),good=0;break));
    if(good,listput(matches,auts[i])));
  hi_check(Str("unique arithmetic Frobenius at (", ell, ")"), #matches == 1);
  matches[1];
};

hi_quadratic(B, scalar_reduced=0) =
{
  my(Bc = matrix(n, n, g, h, hi_aut(bar, B[g,h])));
  \\ With checked multiplier covariance, h=1 represents all nonzero h.
  for(g = 0, n-1, for(h = 0, if(scalar_reduced,1,n-1),
    if(sum(j = 0, n-1, B[(g+j)%n+1,h+1]*Bc[j+1,h+1])
      != (d-1)^2*((g==0)-(h==0)/d), return(0))));
  1;
};

\\ One necessary quadratic equation is linear in transformed stratum signs.
\\ Requires the physical phase form; these conditions are checked separately.
\\ Return all surviving sign bitmasks. Full rank needs no sign enumeration.
hi_prime_power_sign_candidates(B) =
{
  my(fac=factor(n),prime,exponent,coeff,constant,R,level,M,rhs,sol,rank,choices=List(),ys,choice);
  if(n%2==0||matsize(fac)[1]!=1,error("stratum sign solver needs an odd prime power"));
  prime=fac[1,1];exponent=fac[1,2];
  coeff=vector(exponent,j,Mod(0,P));coeff[1]=-B[2,3]-B[3,2];
  constant=Mod(1,P);
  for(m=2,n-2,
    R=B[m+2,2]*B[2,m+1];level=valuation(m^2-1,prime);
    if(level==0,constant+=R,coeff[level+1]+=R));
  M=matrix(poldegree(P),exponent,i,j,polcoef(lift(coeff[j]),i-1));
  rhs=vector(poldegree(P),i,-polcoef(lift(constant),i-1))~;
  rank=matrank(M);sol=matinverseimage(M,rhs);
  print("Exact stratum-sign linear rank: ",rank," / ",exponent);
  if(#sol==0,return([]));
  if(rank==exponent,
    if(vecmin(vector(exponent,j,sol[j]^2==1))==0,return([]));
    choice=if(sol[1]==-1,1,0);
    for(j=2,exponent,if(sol[1]*sol[j]==-1,choice+=2^(j-1)));
    return([choice]));
  \\ In deficient rank, filter the sign cube by this necessary linear equation.
  for(choice=0,2^exponent-1,
    ys=vector(exponent,j,if(j==1,(-1)^bittest(choice,0),
      (-1)^(bittest(choice,0)+bittest(choice,j-1))))~;
    if(M*ys==rhs,listput(choices,choice)));
  Vec(choices);
};

hi_cross_free(a,c,p) =
{
  for(i=1,3,for(j=1,3,if((a[i]+c[j])%p==0,return(0))));
  1;
};

hi_beta_reps(p) =
{
  my(seen=Vecsmall(vector(p^3)),seen_count=0,reps=List(),count=0,
    a,c,u,v,gg,hh,kk,ll,inv,key,slot,
    perms=[[1,2,3],[1,3,2],[2,1,3],[2,3,1],[3,1,2],[3,2,1]]);
  for(hh0=1,p-2,for(kk0=0,p-1,for(ll0=0,p-1,
    a=[0,(kk0-1)%p,(ll0-hh0)%p];c=[(1+hh0)%p,(-kk0)%p,(-ll0)%p];
    if(!hi_cross_free(a,c,p),next);
    count++;key=[1,hh0,kk0,ll0];
    slot=hh0*p^2+kk0*p+ll0+1;
    if(seen[slot],next);
    listput(reps,key);
    for(swap=0,1,for(ii=1,6,for(jj=1,6,
      u=vector(3,t,if(swap,c,a)[perms[ii][t]]);
      v=vector(3,t,if(swap,a,c)[perms[jj][t]]);
      gg=(-v[2]-u[2])%p;hh=(-v[3]-u[3])%p;
      kk=(-v[2]-u[1])%p;ll=(-v[3]-u[1])%p;
      inv=lift(1/Mod(gg,p));
      slot=(hh*inv%p)*p^2+(kk*inv%p)*p+(ll*inv%p)+1;
      if(!seen[slot],seen[slot]=1;seen_count++)))))));
  hi_check("balanced-beta orbits cover every cross-free scalar tuple",
    seen_count==count && count==(p-2)*(p^2-6*p+10));
  Vec(reps);
};

hi_cubic_at(B,Bc,q) =
{
  my(g=q[1],h=q[2],k=q[3],l=q[4]);
  sum(j=0,n-1,B[j+1,(g+h)%n+1]
    *Bc[(j+k)%n+1,g+1]*Bc[(j+l)%n+1,h+1])
    == (d-1)*B[(g+l)%n+1,k+1]*B[(h+k)%n+1,l+1]
      -(d-1)^3*(g==0&&h==0)/d;
};

hi_compare_old_input(B) =
{
  my(expected, actual, cs, pairs);
  \\ These comparisons are downstream assertions, never construction input.
  if(n == 11,
    hi_check("constructed n=11 solution is the simple-ray secondary branch",
      B[2,3]^2+(3*d-4)/5*B[2,3]+d==0));
  if(n == 19,
    cs = [-333455 + 17502*d,
      40480016719 - 2124657930*d,
      -2184194334179476 + 114640906538609*d,
      52633065206494093178 - 2762529970321943798*d,
      -529349994319030677934786 + 27783774673940945312647*d,
      1672523963669322448563809376 - 87785074982637885499085605*d,
      -1642488963741199847701730730841 + 86208640337713983191119491620*d,
      646555447716745795210875455727616 - 33935488932384135968663445224353*d,
      -108638025689290772641476214469989528 + 5702039216333565010862535167197604*d,
      9642170457440094765993211124443243338 - 506084621200145257158413143889621189*d,
      -502512727593124272746658575474842842071 + 26375178131805817029277650303746832071*d,
      16086788983733850072641078703489192777849 - 844340653911344277989282379675390009468*d,
      -318635193234704925190640567433073273637227 + 16724073877452771463908233739817693120773*d,
      3823800994434206931907484764317566416169259 - 200698264602837450348962771092691115210691*d,
      -26746311308097542699063596640337262012652453 + 1403822602660496764423796740905422535420643*d,
      106456935427683871078812613162208909039858661 - 5587561231970933519802130494078700101361492*d,
      -239958142388405162260727968767552385790138612 + 12594583981952076680905688086357450253576818*d,
      313454105109270988272887994762348265080330293 - 16452136243396368439735966221635671877278307*d];
    expected=x^36+1+sum(j=1,17,cs[j]*(x^j+x^(36-j)))+cs[18]*x^18;
    hi_check("constructed n=19 eta satisfies the formerly recognized full polynomial",
      subst(expected,x,-B[2,3]^2/d)==0);
    actual=sum(g=1,n-1,B[g+1,(2*g)%n+1]^2/d);
    hi_check("constructed n=19 branch coefficient has the Hilbert-class quadratic",
      actual^2-cs[1]*actual+61207710-3212584*d==0));
  if(n == 13,
    cs = [467*d-6097, 12814191-979939*d,
      825835784*d-10799019382, 3392673833885-259448689016*d,
      30448109649290*d-398153890397194,
      11724621314790962-896619533298169*d];
    expected = x^12+1+sum(j=1,5,cs[j]*(x^j+x^(12-j)))+cs[6]*x^6;
    actual = prod(g=1,12,x+B[g+1,(2*g)%n+1]^2/d);
    hi_check("constructed n=13 orbit equals the formerly recognized HI polynomial", actual==expected));
  if(n == 17,
    pairs = [[1,0],[-1,0],[-2580,150],[7856,-462],
      [1421008,-83294],[-4237905,248395],[-107944297,6328294],
      [-140236552,8221011],[643252625,-37715514],[8221011,-479365],
      [-363299,152211],[-9835,-182385],[36902,629210],
      [-124086,-2116736],[-1789620,-30528450],[-1439560,-24556909],
      [24556909,418907013]];
    expected = sum(j=1,17,(pairs[j][1]+pairs[j][2]*d)*x^(17-j));
    actual = prod(g=1,16,x-B[g+1,(2*g)%n+1]);
    hi_check("constructed n=17 orbit equals the formerly recognized P2", actual==expected);
    pairs = [[1,0],[88,-4],[2770,-151],[34942,-1980],[71997,-3962],
      [-1721469,101419],[-7809793,457226],[23941037,-1412808],
      [86056376,-5091529],[-1412808,-76699],[-36951,-170941],
      [146537,2493783],[1279116,21819941],[5767854,98391638],
      [16383970,279487941],[28453644,485379940],[24556909,418907013]];
    expected=sum(j=1,17,(pairs[j][1]+pairs[j][2]*d)*x^(17-j));
    hi_check("constructed n=17 orbit equals the formerly recognized P3",
      prod(g=1,16,x-B[g+1,(3*g)%n+1])==expected);
    pairs = [[1,0],[54,-4],[337,-13],[-19861,1126],[-378462,22347],
      [-2225467,130012],[-1210231,71385],[27441545,-1605286],
      [62238779,-3670344],[-1605286,151683],[3314,127723],
      [-129459,-2216066],[796629,13589469],[-3230353,-55105369],
      [9724813,165891903],[-20491396,-349554966],[24556909,418907013]];
    expected=sum(j=1,17,(pairs[j][1]+pairs[j][2]*d)*x^(17-j));
    hi_check("constructed n=17 orbit equals the formerly recognized P4",
      prod(g=1,16,x-B[g+1,(4*g)%n+1])==expected));
};

hi_stark_run(n0) =
{
  n = n0;
  hi_check("input is an odd prime", n>2 && isprime(n));
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
    || znorder(Mod(ell,n))!=n-1, ell++);
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

  sv = vector(n); sv[1] = 1; u = 1; q = s;
  for(i=1,n-1,sv[u+1]=q;u=(ell*u)%n;q=hi_aut(phi,q));
  hi_check("complete consistent residue labels",
    u==1 && q==s && vecmin(vector(n-1,g,sv[g+1]!=0)));
  bar = phi;
  for(i=2,(n-1)/2,bar=lift(hi_aut(phi,bar)));
  if(bar!=phi,hi_cache_aut(bar));
  hi_check("residue -1 inverts the Stark generator", hi_aut(bar,s)==1/s);
  hi_check("its fixed field is totally real",
    nfinit(minpoly(s+1/s)).sign==[poldegree(P)/2,0]);
  hi_check("all real embeddings of the full field have delta negative",
    #nfeltsign(F,d)>0 && vecmax(nfeltsign(F,d))==-1);
  \\ Consequently bar is actual complex conjugation over delta>0.

  Brow = vector(n); Brow[1] = -1; Brow[2] = -1; m = (n-1)/2;
  root_cache=List();
  for(h=2,m+1,
    my(R=d^2*sv[2]*sv[h]/sv[h+1],rr,root=0);
    for(j=1,#root_cache,if(root_cache[j][1]==R,root=root_cache[j][2];break));
    if(root==0,
      rr=nfroots(F,x^4-R);
      hi_check(Str("two exact fourth-root lifts for new row orbit ",h),#rr==2);
      root=Mod(rr[1],P);q=root;
      for(j=1,n-1,listput(root_cache,[q^4,q]);q=hi_aut(phi,q)));
    hi_check(Str("exact fourth-root lift for row entry ",h),root^4==R);
    Brow[h+1]=root; Brow[n+2-h]=root);
  checkpoint_text=getenv("HI_STARK_CHECKPOINT");
  if(type(checkpoint_text)=="t_STR" && #checkpoint_text,
    writebin(checkpoint_text,[n,ell,P,d,s,phi,bar,sv,Brow]);
    print("Saved exact row checkpoint to ",checkpoint_text));
  hi_stark_finish();
};

\\ Resume only a row checkpoint produced by the exact stages above.
\\ Its earlier field checks remain part of the construction certificate.
hi_stark_resume(path) =
{
  my(data=read(path));
  [n,ell,P,d,s,phi,bar,sv,Brow]=data;
  timer=getwalltime();m=(n-1)/2;
  hi_fast_auts=List();hi_cache_aut(phi);
  if(bar!=phi,hi_cache_aut(bar));
  T=y^2-n*y-1;K=bnfinit(T,1);delta=Mod(y,T);
  ray=bnrinit(K,[idealhnf(K,delta-1),[0,1]],1);
  print("RESUMING previously checked exact row data for n=",n);
  hi_stark_finish();
};

hi_stark_finish() =
{

  \\ Arbitrary initial signs. Prefix products reconstruct the whole upper
  \\ triangle without adjoining sqrt(delta); pmask tracks each unknown sign.
  prefix = vector(n,i,1); pmask = vector(n);
  for(h=2,n-1,
    prefix[h+1]=prefix[h]*Brow[h+1];
    pmask[h+1]=bitxor(pmask[h],2^(min(h,n+1-h)-2)));
  B = matrix(n,n,g,h,if(g==1&&h==1,d-2,
    if(g==1||h==1||g==h,-1,
    if(g<h,prefix[h]/(prefix[g]*prefix[h-g+1]),0))));
  V = matrix(n,n,g,h,if(g==1||h==1||g==h,0,
    if(g<h,bitxor(pmask[h],bitxor(pmask[g],pmask[h-g+1])),0)));
  for(g=1,n-1,for(h=1,g-1,
    B[g+1,h+1]=hi_aut(bar,B[h+1,g+1]); V[g+1,h+1]=V[h+1,g+1]));

  rows = List(); rhs = List();
  for(g=1,n-1,for(h=1,n-1,if(g!=h,
    my(ratio=hi_aut(phi,B[g+1,h+1])/B[(ell*g)%n+1,(ell*h)%n+1],
       mask=bitxor(V[g+1,h+1],V[(ell*g)%n+1,(ell*h)%n+1]));
    if(ratio!=1 && ratio!=-1,error("covariance ratio is not a sign"));
    listput(rows,vector(m,j,bittest(mask,j-1))); listput(rhs,ratio==-1))));
  MM = matrix(#rows,m,i,j,rows[i][j]); rhs = Col(Vec(rhs));
  \\ Construct a solution by the sign-transport theorem (Section 30).
  \\ f(u)=E(u/2,u/2), where E is the covariance-error cocycle.
  signf=vector(n);signf[1]=1;
  for(u=1,n-1,
    a=lift(Mod(u,n)/2);
    signf[u+1]=hi_aut(phi,B[a+1,(2*a)%n+1])
      /B[(ell*a)%n+1,(2*ell*a)%n+1];
    if(signf[u+1]!=1 && signf[u+1]!=-1,error("transport is not a sign")));
  ts=vector(n);ts[1]=1;u=1;q=1;
  for(i=1,n-1,ts[u+1]=q;q*=signf[u+1];u=(ell*u)%n);
  hi_check("sign transport closes and respects negation",
    q==1 && vecmin(vector(n-1,u,ts[u+1]==ts[n-u+1])));
  ss=vector(m,j,ts[2]*ts[j+1]*ts[j+2]==-1)~;
  hi_check("transport solves every linear sign equation",
    Mod(MM,2)*Mod(ss,2)==Mod(rhs,2));
  hi_check("their only freedom is a global generic sign",
    matrank(Mod(MM,2))==m-1
    && Mod(MM,2)*vector(m,i,Mod(1,2))~==0*Mod(rhs,2));
  for(g=1,n-1,for(h=1,n-1,if(g!=h,
    B[g+1,h+1]*=(-1)^sum(j=1,m,bittest(V[g+1,h+1],j-1)*ss[j]))));
  hi_check("multiplier covariance",vecmin(vector(n^2,i,
    g=(i-1)\n;h=(i-1)%n;
    hi_aut(phi,B[g+1,h+1])==B[(ell*g)%n+1,(ell*h)%n+1])));
  if(!hi_quadratic(B,1),for(g=1,n-1,for(h=1,n-1,if(g!=h,
    B[g+1,h+1]=-B[g+1,h+1]))));
  hi_check("all quadratic Izumi equations, by exact scalar covariance",hi_quadratic(B,1));
  hi_check("rotation symmetry",vecmin(vector(n^2,i,
    g=(i-1)\n;h=(i-1)%n;B[g+1,h+1]==B[(-h)%n+1,(g-h)%n+1])));
  hi_check("all generic fourth-power Stark formulas",vecmin(vector(n^2,i,
    g=(i-1)\n;h=(i-1)%n;
    if(g==0||h==0||g==h,1,
      B[g+1,h+1]^4==d^2*sv[g+1]*sv[(h-g)%n+1]/sv[h+1]))));
  hi_check("generic norms are delta",vecmin(vector(n^2,i,
    g=(i-1)\n;h=(i-1)%n;
    if(g==0||h==0||g==h,1,B[g+1,h+1]*hi_aut(bar,B[g+1,h+1])==d))));
  matrix_checkpoint_text=getenv("HI_STARK_MATRIX_CHECKPOINT");
  if(type(matrix_checkpoint_text)=="t_STR" && #matrix_checkpoint_text,
    writebin(matrix_checkpoint_text,[n,ell,P,d,s,phi,bar,B]);
    print("Saved exact matrix checkpoint before cubic verification to ",matrix_checkpoint_text));
  if(getenv("HI_STARK_STOP_AFTER_MATRIX")=="1",
    hi_check("a matrix checkpoint was requested",type(matrix_checkpoint_text)=="t_STR" && #matrix_checkpoint_text);
    print("PARTIAL: field, phase, and quadratic checks passed; cubic verification still required");
    quit(0));

  \\ Q handles boundary and cross-zero beta identities. Independent
  \\ permutations of the two triples, exchange, and scalar covariance
  \\ cover the remaining cubic identities (Section 34).
  Bc = matrix(n,n,g,h,hi_aut(bar,B[g,h])); count = 0;
  beta_reps=hi_beta_reps(n);
  for(i=1,#beta_reps,
    if(!hi_cubic_at(B,Bc,beta_reps[i]),
      error(Str("cubic equation failed at ",beta_reps[i])));
    if(i%1000==0,print("Cubic progress: ",i," / ",#beta_reps,
      "; elapsed_ms=",getwalltime()-timer)));
  count=#beta_reps;
  hi_check("every cubic Izumi equation, by exact balanced-beta orbit coverage",1);
  full_cubic_text=getenv("HI_STARK_FULL_CUBIC");
  if(type(full_cubic_text)=="t_STR" && full_cubic_text=="1",
    my(full_count=0);
    hi_check("independent complete quadratic regression",hi_quadratic(B));
    for(g=0,1,
    for(h=0,if(g==0,1,n-1),
      for(k=0,if(g==0&&h==0,1,n-1),
        for(l=0,if(g==0&&h==0&&k==0,1,n-1),
          full_count++;
          if(!hi_cubic_at(B,Bc,[g,h,k,l]),
            error(Str("cubic equation failed at ",[g,h,k,l])))))));
    hi_check("independent complete scalar-orbit cubic regression",
      full_count==1+(n^4-1)/(n-1)));
  hi_compare_old_input(B);
  print("CERTIFIED n=",n,"; ray_group=",ray.cyc,
    "; absolute_degree=",poldegree(P),"; sign_rank=",m-1,
    "; beta_representatives=",count,"; elapsed_ms=",getwalltime()-timer);
  certificate_text=getenv("HI_STARK_CERTIFICATE");
  if(type(certificate_text)=="t_STR" && #certificate_text,
    writebin(certificate_text,[n,P,d,s,phi,bar,B]);
    print("Saved complete exact certificate to ",certificate_text));
  [n,P,d,s,phi,bar,B];
};

hi_stark_main() =
{
hi_resume_text=getenv("HI_STARK_RESUME");
if(type(hi_resume_text)=="t_STR" && #hi_resume_text,
  iferr(hi_certificate=hi_stark_resume(hi_resume_text),
    hi_error,print("FAILED: ",hi_error);quit(1));
  print("RESUMED EXACT CERTIFICATE PASSED");quit(0));
hi_cases_text = getenv("HI_STARK_CASES");
hi_cases = if(type(hi_cases_text)=="t_STR" && #hi_cases_text,
  eval(hi_cases_text),[7,11,13,17,29]);
iferr(for(hi_i=1,#hi_cases,hi_certificate=hi_stark_run(hi_cases[hi_i])),
  hi_error,print("FAILED: ",hi_error);quit(1));
print("ALL REQUESTED EXACT CERTIFICATES PASSED");
quit(0);
};

if(getenv("HI_STARK_LIBRARY")!="1",hi_stark_main());
