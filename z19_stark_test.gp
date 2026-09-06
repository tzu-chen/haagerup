\\ Exact arithmetic checks for the degree-36 polynomial numerically
\\ reconstructed from both published p=19 Evans--Gannon branches.
\\ Run with: gp -q z19_stark_test.gp
\\ Requires PARI/GP with bnrstarkunit (tested with 2.17.4).
\\
\\ IMPORTANT: eta_hi is an algebraic recognition from numerical phase
\\ seeds refined against the Izumi equations.  It is exact input below;
\\ the class-field checks after its definition are exact.

check(label, condition) =
{
  if(!condition, error(Str("check failed: ", label)));
  print("[ok] ", label);
};

default(parisizemax, 4000000000);
default(realprecision, 180);

T = y^2 - 19*y - 1;
bnf = bnfinit(T, 1);
delta = Mod(y, T);
pp = idealhnf(bnf, delta - 1);

print("class group = ", bnf.clgp);
check("base-field class/unit data certify unconditionally", bnfcertify(bnf) == 1);
check("K has class number two", bnf.no == 2);
check("Norm((delta-1)) = 19", idealnorm(bnf, pp) == 19);

real_roots = polrootsreal(T);
check("physical place is PARI's second real place", real_roots[1] < 0 && real_roots[2] > 0);
bnr_plus = bnrinit(bnf, [pp, [0,1]], 1);
bnr_minus = bnrinit(bnf, [pp, [1,0]], 1);
print("physical ray group = ", bnr_plus.clgp);
print("opposite ray group = ", bnr_minus.clgp);
check("physical ray group is C18 x C2", bnr_plus.no == 36 && bnr_plus.cyc == [18,2]);

c1  = -333455 + 17502*delta;
c2  = 40480016719 - 2124657930*delta;
c3  = -2184194334179476 + 114640906538609*delta;
c4  = 52633065206494093178 - 2762529970321943798*delta;
c5  = -529349994319030677934786 + 27783774673940945312647*delta;
c6  = 1672523963669322448563809376 - 87785074982637885499085605*delta;
c7  = -1642488963741199847701730730841 + 86208640337713983191119491620*delta;
c8  = 646555447716745795210875455727616 - 33935488932384135968663445224353*delta;
c9  = -108638025689290772641476214469989528 + 5702039216333565010862535167197604*delta;
c10 = 9642170457440094765993211124443243338 - 506084621200145257158413143889621189*delta;
c11 = -502512727593124272746658575474842842071 + 26375178131805817029277650303746832071*delta;
c12 = 16086788983733850072641078703489192777849 - 844340653911344277989282379675390009468*delta;
c13 = -318635193234704925190640567433073273637227 + 16724073877452771463908233739817693120773*delta;
c14 = 3823800994434206931907484764317566416169259 - 200698264602837450348962771092691115210691*delta;
c15 = -26746311308097542699063596640337262012652453 + 1403822602660496764423796740905422535420643*delta;
c16 = 106456935427683871078812613162208909039858661 - 5587561231970933519802130494078700101361492*delta;
c17 = -239958142388405162260727968767552385790138612 + 12594583981952076680905688086357450253576818*delta;
c18 = 313454105109270988272887994762348265080330293 - 16452136243396368439735966221635671877278307*delta;

eta_hi = x^36 + c1*(x^35+x) + c2*(x^34+x^2) + c3*(x^33+x^3) + c4*(x^32+x^4) + c5*(x^31+x^5) + c6*(x^30+x^6) + c7*(x^29+x^7) + c8*(x^28+x^8) + c9*(x^27+x^9) + c10*(x^26+x^10) + c11*(x^25+x^11) + c12*(x^24+x^12) + c13*(x^23+x^13) + c14*(x^22+x^14) + c15*(x^21+x^15) + c16*(x^20+x^16) + c17*(x^19+x^17) + c18*x^18 + 1;

check("HI eta candidate is reciprocal", x^36*subst(eta_hi,x,1/x) == eta_hi);

\\ -----------------------------------------------------------------------
\\ Numerical source and recognition check
\\ -----------------------------------------------------------------------

delta_plus = (19 + sqrt(365))/2;
Bphase(g,h,jv,dv) = { if(g==0 && h==0, return(dv-2)); if(g==0 || h==0 || g==h, return(-1)); if(g<h, return(sqrt(dv)*exp(I*(jv[h+1]-jv[g+1]-jv[h-g+1]))), return(conj(sqrt(dv)*exp(I*(jv[g+1]-jv[h+1]-jv[g-h+1]))))) };

\\ Evans--Gannon, arXiv:1006.1326, Section 4.1, gives these two
\\ inequivalent seeds to six decimal places.
jseed0 = [0,0,-2.677465,1.088972,-0.899442,0.015448,-1.240928,-0.493394,1.839879,-1.525884,-2.084374,0,0,0,0,0,0,0,0];
jseed1 = [0,0,0.896858,-0.882585,-2.369855,-1.873294,-1.711620,-0.119360,2.972018,-2.460652,0.041334,0,0,0,0,0,0,0,0];
for(i=1,8,jseed0[11+i]=jseed0[11]+jseed0[10]-jseed0[10-i]);
for(i=1,8,jseed1[11+i]=jseed1[11]+jseed1[10]-jseed1[10-i]);
Bseed0 = matrix(19,19,ig,ih,Bphase(ig-1,ih-1,jseed0,delta_plus));
Bseed1 = matrix(19,19,ig,ih,Bphase(ig-1,ih-1,jseed1,delta_plus));
eta_seed = prod(g=1,18,x+Bseed0[g+1,(2*g)%19+1]^2/delta_plus)*prod(g=1,18,x+Bseed1[g+1,(2*g)%19+1]^2/delta_plus);
eta_physical = subst(lift(eta_hi),y,delta_plus);
seed_coefficient_error = vecmax(vector(37,k,abs(polcoef(eta_seed,k-1)-polcoef(eta_physical,k-1))));
print("combined eta coefficient error from published six-digit seeds = ",seed_coefficient_error);
check("combined recognition matches the published seed accuracy",seed_coefficient_error < 0.001);

\\ These values retain about 115 digits from a 450-digit Newton refinement
\\ using nine independent real instances of (4.2) for each branch.
jrefined0 = [0,0,-2.67746513112270158130565624092863414834570146520268574511940657713661356703931349336106970800284045727833808371081655,1.08897212775659749378588881050492846479451418095127802002967456333456000333551848458892444256816242864179282427500604,-0.899441860154669525480382333528287426729297366593709973631891020106340062910621285489198748693564525959370623745731446,0.0154481563139506814100500635394800084801733769518220195738303112031440307133127570068425038177024632080592631927466556,-1.24092816710598912193261965261347803850155583447467055641649773512942331078311289403315220584103526067337724807440959,-0.493394333354902298961440353675038506530869716387776919462025698706983477236790716280344743780419900252913356706970021,1.83987936595252786235665970093128717347823381890776184505312409077720008368875686240641029383739947840196607144572148,-1.52588450422686631396486218865462082220232433594034214009312364933954711863539623778082620357283203894861448494189375,-2.08437349912887928205839247478092332182342470821219290368962156661408080208645045399056447119104023293527408620181701,0,0,0,0,0,0,0,0];
jrefined1 = [0,0,0.896858383265372044435922062864223627998727607664179951209758271463898993275816774982977012728207065854843068668216903,-0.882585066369420878870986407608930854457976715369319278893071499794819350099560589193797837685329005359517016644438405,-2.36985481632619416585514655063757806743138995376208177725120722805917835075983016253623392844460054575377012657449502,-1.87329368779782611661254640940758957322123928228135997407401967669440970259891579938749270050387727232438024853886430,-1.71162023745974083432445241650015653820765299408742487658039827041366578640442092793576783185060541823897789208309152,-0.119359662371487162534911010203373753012049970539844250155627542444492915644568984787773200661395201043983935755822883,2.97201793990700027641705500558713924440748412840526119360236307672398558724700080660806736400213059134088270287630364,-2.46065156497351522454527219079255711325038758272425801944793144179841714253402965328118094160154683178395964101612536,0.0413342147957809312856959784038415320475887472385780663686877414442043494539082887325049105072634016363270252874687494,0,0,0,0,0,0,0,0];
for(i=1,8,jrefined0[11+i]=jrefined0[11]+jrefined0[10]-jrefined0[10-i]);
for(i=1,8,jrefined1[11+i]=jrefined1[11]+jrefined1[10]-jrefined1[10-i]);
Brefined0 = matrix(19,19,ig,ih,Bphase(ig-1,ih-1,jrefined0,delta_plus));
Brefined1 = matrix(19,19,ig,ih,Bphase(ig-1,ih-1,jrefined1,delta_plus));
Arefined0 = Brefined0/(delta_plus-1);
Arefined1 = Brefined1/(delta_plus-1);
res42(A,dv) = { my(r=0,z); for(g=0,18,for(h=0,18,z=sum(m=0,18,A[(g+m)%19+1,h+1]*conj(A[m+1,h+1]))-(g==0)+(h==0)/dv; r=max(r,abs(z)))); r };
res43(A,dv) = { my(r=0,z); for(g=0,18,for(h=0,18,for(k=0,18,for(l=0,18,z=sum(m=0,18,A[m+1,(g+h)%19+1]*conj(A[(m+k)%19+1,g+1]*A[(m+l)%19+1,h+1]))-A[(g+l)%19+1,k+1]*A[(h+k)%19+1,l+1]+((g==0&&h==0)/dv); r=max(r,abs(z)))))); r };
r420=res42(Arefined0,delta_plus); r421=res42(Arefined1,delta_plus);
r430=res43(Arefined0,delta_plus); r431=res43(Arefined1,delta_plus);
print("max refined (4.2) residuals for branches 0,1 = ",[r420,r421]);
print("max refined (4.3) residuals for branches 0,1 = ",[r430,r431]);
check("both refined branches satisfy all numerical (4.2) checks",max(r420,r421)<1e-105);
check("both refined branches satisfy all numerical (4.3) checks",max(r430,r431)<1e-105);
eta_refined0 = prod(g=1,18,x+Brefined0[g+1,(2*g)%19+1]^2/delta_plus);
eta_refined1 = prod(g=1,18,x+Brefined1[g+1,(2*g)%19+1]^2/delta_plus);
refined_coefficient_error = vecmax(vector(37,k,abs(polcoef(eta_refined0*eta_refined1,k-1)-polcoef(eta_physical,k-1))));
print("combined eta coefficient error after refinement = ",refined_coefficient_error);
check("refinement supports the degree-36 coefficient recognition",refined_coefficient_error<1e-100);

\\ -----------------------------------------------------------------------
\\ Exact splitting over the Hilbert class field
\\ -----------------------------------------------------------------------

ht = c1;
hn = 61207710 - 3212584*delta;
Hpol = x^2 - ht*x + hn;
check("the branch-coefficient quadratic is irreducible over K",matsize(nffactor(bnf,Hpol))[1]==1);
Hcond = rnfconductor(bnf,Hpol);
check("the branch coefficient generates the Hilbert class field",Hcond[1][1]==matid(2) && Hcond[1][2]==[0,0] && Hcond[2].no==2 && Hcond[3]==Mat(2));
check("a reduced Hilbert-class polynomial is x^2+delta-29",rnfpolredbest(bnf,Hpol)==x^2+delta-29);

ha = [1,0,(-1605467740763+84265535582*delta)/72283,(86516839203571062-4540973631294549*delta)/72283,(-2076020732085139456409+108963243331822593211*delta)/72283,(20656852525697389078733556-1084207692842457373533408*delta)/72283,(-62652813943421835336205146836+3288432386840202555017059954*delta)/72283,(53487132821916796818174515441196-2807357064754504102425874712490*delta)/72283,(-14993089145890615316829563955771110+786936081923669210648135636985634*delta)/72283,(786548148539213591187780327026338931-41283228041461595041248084645959384*delta)/72283];
hb = [0,1,(-8747112367+459110544*delta)/72283,(471078571875469-24725306564867*delta)/72283,(-11303792845290646598+593297509672187929*delta)/72283,(112475168515363100842402-5903437748147037026738*delta)/72283,(-341140345436339089412431141+17905292512539984890154882*delta)/72283,(291233830035878291763487498770-15285869836562226643727518938*delta)/72283,(-81636358983106149294907099429650+4284813880286147576540794289374*delta)/72283,(4282701609177319385572192019443184-224784391767450972750520148824793*delta)/72283];
X = varhigher("X",x);
hc = vector(10,i,ha[i]+hb[i]*x);
hcb = vector(10,i,ha[i]+hb[i]*(ht-x));
branch_H = X^18 + sum(i=1,8,hc[i+1]*(X^(18-i)+X^i)) + hc[10]*X^9 + 1;
branch_Hbar = X^18 + sum(i=1,8,hcb[i+1]*(X^(18-i)+X^i)) + hcb[10]*X^9 + 1;
branch_norm_X = sum(k=0,36,lift(Mod(polcoef(branch_H*branch_Hbar,k,X),Hpol))*X^k);
branch_norm = subst(branch_norm_X,X,x);
check("the exact Hilbert-conjugate branch norm is eta_hi",branch_norm==eta_hi);

Hroots = polroots(subst(liftall(Hpol),y,delta_plus));
branch_num_H0 = subst(subst(subst(liftall(branch_H),y,delta_plus),x,Hroots[2]),X,x);
branch_num_H1 = subst(subst(subst(liftall(branch_Hbar),y,delta_plus),x,Hroots[2]),X,x);
branch_H_error = max(vecmax(vector(19,k,abs(polcoef(eta_refined0,k-1)-polcoef(branch_num_H0,k-1)))),vecmax(vector(19,k,abs(polcoef(eta_refined1,k-1)-polcoef(branch_num_H1,k-1)))));
print("max branch-over-H coefficient recognition error = ",branch_H_error);
check("each numerical branch matches one Hilbert conjugate",branch_H_error<1e-100);

eta_fac = nffactor(bnf, eta_hi);
print("factor degrees over K = ", vector(matsize(eta_fac)[1], i, poldegree(eta_fac[i,1])));
check("HI eta candidate is irreducible over K", matsize(eta_fac)[1] == 1 && poldegree(eta_fac[1,1]) == 36);

eta_conductor = rnfconductor(bnf, eta_hi);
print("HI conductor = ", eta_conductor[1]);
print("HI conductor ray group = ", eta_conductor[2].clgp);
print("HI norm subgroup = ", eta_conductor[3]);
check("HI finite conductor is (delta-1)", eta_conductor[1][1] == pp);
check("HI infinite conductor is physical infinity", eta_conductor[1][2] == [0,1]);
check("HI is the full degree-36 ray field", eta_conductor[2].cyc == [18,2] && eta_conductor[3] == [18,0;0,2]);

eta_reldisc = rnfdisc(bnf, eta_hi)[1];
print("HI relative discriminant factorization = ", idealfactor(bnf, eta_reldisc));
print("ray discriminant data = ", bnrdisc(bnr_plus));
check("HI relative discriminant is (delta-1)^34",eta_reldisc==idealpow(bnf,pp,34));
expected_abs_disc = 365^36*19^34;
check("ray absolute discriminant is 365^36*19^34",bnrdisc(bnr_plus)[3]==expected_abs_disc);

stark = bnrstarkunit(bnr_plus);
print("Stark polynomial degree = ", poldegree(stark));
check("Stark polynomial is irreducible over K",matsize(nffactor(bnf,stark))[1]==1);
check("Stark polynomial is reciprocal",x^36*subst(stark,x,1/x)==stark);
print("HI polynomial equals Stark polynomial? ", eta_hi == stark);
\\ Both define the unique full ray field: eta_hi by the exact conductor and
\\ norm-subgroup computation above, and stark by construction from bnr_plus.
\\ A direct rnfpolredabs comparison was abandoned after five minutes; it is
\\ redundant for field identification and unsuitable for a regression test.

\\ High-precision evidence for the Stark quotient law.  The ideal (2) has
\\ ray coordinate [10,1], order 18, and generates the kernel of the map to
\\ Cl(K).  Thus its Frobenius acts as two 18-cycles on the 36 Stark roots.
q2 = idealhnf(bnf,2);
q2ray = bnrisprincipal(bnr_plus,q2,0);
print("ray coordinates of (2) = ",q2ray);
check("Frob_(2) has order 18",q2ray==[10,1]~);
eta_roots = polroots(eta_physical);
stark_physical = subst(liftall(stark),y,delta_plus);
stark_roots = polroots(stark_physical);
quotient_matches = List();
pair_errors = vector(36^2); pe=0;
for(i=1,36,for(j=1,36,q=stark_roots[i]^2/stark_roots[j]; bk=1; be=abs(q-eta_roots[1]^2); for(k=2,36,ee=abs(q-eta_roots[k]^2);if(ee<be,be=ee;bk=k)); pe++;pair_errors[pe]=be;if(be<1e-70,listput(quotient_matches,[i,j,bk,be]))));
quotient_matches = Vec(quotient_matches);
print("number of numerical e_k^2=s_i^2/s_j matches = ",#quotient_matches);
sorted_pair_errors=vecsort(pair_errors);
print("largest accepted / smallest rejected quotient errors = ",[sorted_pair_errors[#quotient_matches],sorted_pair_errors[#quotient_matches+1]]);
check("the quotient law selects exactly one edge from each Stark root",#quotient_matches==36);
rho_perm=vector(36);outdeg=vector(36);indeg=vector(36);
for(m=1,#quotient_matches,i=quotient_matches[m][1];j=quotient_matches[m][2];rho_perm[i]=j;outdeg[i]++;indeg[j]++);
check("the selected quotient edges form a permutation",vecmin(outdeg)==1&&vecmax(outdeg)==1&&vecmin(indeg)==1&&vecmax(indeg)==1);
seen=vector(36);cycle_lengths=List();
for(i=1,36,if(!seen[i],j=i;ll=0;while(!seen[j],seen[j]=1;ll++;j=rho_perm[j]);listput(cycle_lengths,ll)));
cycle_lengths=vecsort(Vec(cycle_lengths));
print("cycle lengths of quotient permutation = ",cycle_lengths);
check("the quotient permutation has a generator-of-<Frob_(2)> cycle signature",cycle_lengths==[18,18]);
rho9_inverse_error=0;
for(i=1,36,j=i;for(k=1,9,j=rho_perm[j]);rho9_inverse_error=max(rho9_inverse_error,abs(stark_roots[j]-1/stark_roots[i])));
print("max error in rho^9(s)=s^(-1) = ",rho9_inverse_error);
check("the ninth power of the quotient permutation is inversion",rho9_inverse_error<1e-70);
print("Numerically: eta^2=s^2/rho(s), where rho is compatible with a generator of <Frob_(2)>.");
print("Without a mod-2 root labeling this does not distinguish Frob_(2) from its coprime powers.");

print("eta_hi = ", eta_hi);
