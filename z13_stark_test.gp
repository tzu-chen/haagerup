\\ Exact ray/Stark checks for the numerically reconstructed principal p=13
\\ Haagerup-Izumi candidate.  Run with: gp -q z13_stark_test.gp
\\ Requires PARI/GP with bnrstarkunit (tested with 2.17.4).
\\
\\ IMPORTANT: eta_hi below is a high-precision recognition from the
\\ Evans-Gannon numerical phase seed and equations (4.1)--(4.3).  It is
\\ exact input to this script; the checks after its definition are exact.

check(label, condition) =
{
  if(!condition, error(Str("check failed: ", label)));
  print("[ok] ", label);
};

default(parisizemax, 2000000000);
default(realprecision, 100);

T = y^2 - 13*y - 1;
bnf = bnfinit(T, 1);
delta = Mod(y, T);
pp = idealhnf(bnf, delta - 1);

check("base-field class/unit data certify unconditionally", bnfcertify(bnf) == 1);
check("K has class number one", bnf.no == 1);
check("delta is PARI's fundamental unit", delta == bnf.fu[1]);
check("Norm((delta-1)) = 13", idealnorm(bnf, pp) == 13);
real_roots = polrootsreal(T);
print("real roots of delta polynomial = ", real_roots);
check("physical place is PARI's second real place", real_roots[1] < 0 && real_roots[2] > 0);

bnr_minus = bnrinit(bnf, [pp, [1,0]], 1);
bnr_plus  = bnrinit(bnf, [pp, [0,1]], 1);
print("ray group at infinity_- = ", bnr_minus.clgp);
print("ray group at infinity_+ = ", bnr_plus.clgp);
check("physical ray group is cyclic of order 12", bnr_plus.no == 12 && bnr_plus.cyc == [12]);

stark = bnrstarkunit(bnr_plus);
check("Stark polynomial has degree 12", poldegree(stark) == 12);
stark_factorization = nffactor(bnf, stark);
check("Stark polynomial is irreducible over K", matsize(stark_factorization)[1] == 1 && poldegree(stark_factorization[1,1]) == 12);
check("Stark polynomial is reciprocal", x^12 * subst(stark, x, 1/x) == stark);
sc1 = 789*delta - 10317;
sc2 = 35116283 - 2685455*delta;
sc3 = 3353223084*delta - 43848331854;
sc4 = 13784155586013 - 1054118748624*delta;
sc5 = 43244520227550*delta - 565485810623322;
sc6 = 2026659283092638 - 154985159159777*delta;
stark_expected = x^12 + sc1*x^11 + sc2*x^10 + sc3*x^9 + sc4*x^8 + sc5*x^7 + sc6*x^6 + sc5*x^5 + sc4*x^4 + sc3*x^3 + sc2*x^2 + sc1*x + 1;
check("bnrstarkunit returns the recorded exact polynomial", stark == stark_expected);

\\ eta=-B_{g,2g}^2/delta, reconstructed from the published principal
\\ j^(13) phase seed after 180-digit refinement against (4.2).
c1 = 467*delta - 6097;
c2 = 12814191 - 979939*delta;
c3 = 825835784*delta - 10799019382;
c4 = 3392673833885 - 259448689016*delta;
c5 = 30448109649290*delta - 398153890397194;
c6 = 11724621314790962 - 896619533298169*delta;

eta_hi = x^12 + c1*x^11 + c2*x^10 + c3*x^9 + c4*x^8 + c5*x^7 + c6*x^6 + c5*x^5 + c4*x^4 + c3*x^3 + c2*x^2 + c1*x + 1;

\\ Reproduce the numerical reconstruction.  Evans--Gannon, arXiv:1006.1326,
\\ Section 4.1, gives j^(13)=(j_2,...,j_7) to 6--8 decimals and
\\ A_{g,h}=sqrt(delta)/(delta-1) exp(i(j_h-j_g-j_{h-g})).
\\ The remaining phases obey j_{7+i}=j_7+j_6-j_{6-i}, 1<=i<6.
\\ First check only the precision warranted by the published seed.
delta_plus = (13 + sqrt(173))/2;
jseed = [0, 0, -3.1050384, 0.5993399, -0.111708, -0.969766, 1.336848, 1.00483129, 0, 0, 0, 0, 0];
for(i=1, 5, jseed[8+i] = jseed[8] + jseed[7] - jseed[7-i]);
Bseed = vector(12, g, h=(2*g)%13; if(g<h, sqrt(delta_plus)*exp(I*(jseed[h+1]-jseed[g+1]-jseed[h-g+1])), conj(sqrt(delta_plus)*exp(I*(jseed[g+1]-jseed[h+1]-jseed[g-h+1])))));
eta_seed_pol = prod(g=1, 12, x + Bseed[g]^2/delta_plus);
eta_physical = subst(lift(eta_hi), y, delta_plus);
seed_coefficient_error = vecmax(vector(13, k, abs(polcoef(eta_seed_pol, k-1) - polcoef(eta_physical, k-1))));
print("max coefficient error against published seed = ", seed_coefficient_error);
check("recognized eta polynomial matches published seed precision", seed_coefficient_error < 0.002);

\\ These phases retain 100 digits of a Newton refinement using six
\\ independent instances of (4.2).  Check every instance of (4.2) and
\\ all 13^4 instances of (4.3), as well as the recognized eta polynomial.
\\ These remain numerical checks, not an exact proof of the HI input.
jrefined = [0, 0, -3.105038401989823783184268677158683615861013819545623966273755115438508379085748550737014443840329039, 0.5993398888365379307622529909614194700265445021484457789635125045558254230149682374627856557543782671, -0.1117084834154405393833954538437325425192472717311252738326063247598537991174758949426497116503098100, -0.9697663641059352186934325181396185702938479913230412126007379693355503979584500085355976030164180012, 1.336848068386338843198235125298232109439291296652525372437498495124156276690255626609457136044599456, 1.004831293229230101468572818517618016040152152048807016038808099789399556989318334392989465318460861, 0, 0, 0, 0, 0];
for(i=1, 5, jrefined[8+i] = jrefined[8] + jrefined[7] - jrefined[7-i]);
Bphase(g,h,jv,dv) = { if(g==0 && h==0, return(dv-2)); if(g==0 || h==0 || g==h, return(-1)); if(g<h, return(sqrt(dv)*exp(I*(jv[h+1]-jv[g+1]-jv[h-g+1]))), return(conj(sqrt(dv)*exp(I*(jv[g+1]-jv[h+1]-jv[g-h+1]))))) };
Brefined = matrix(13, 13, ig, ih, Bphase(ig-1, ih-1, jrefined, delta_plus));
Arefined = Brefined/(delta_plus-1);
residual_42 = 0;
for(g=0, 12, for(h=0, 12, lhs42=sum(m=0, 12, Arefined[(g+m)%13+1,h+1]*conj(Arefined[m+1,h+1])); rhs42=(g==0)-(h==0)/delta_plus; residual_42=max(residual_42,abs(lhs42-rhs42))));
residual_43 = 0;
for(g=0, 12, for(h=0, 12, for(k=0, 12, for(l=0, 12, lhs43=sum(m=0, 12, Arefined[m+1,(g+h)%13+1]*conj(Arefined[(m+k)%13+1,g+1]*Arefined[(m+l)%13+1,h+1])); rhs43=Arefined[(g+l)%13+1,k+1]*Arefined[(h+k)%13+1,l+1]-((g==0 && h==0)/delta_plus); residual_43=max(residual_43,abs(lhs43-rhs43))))));
print("max residual in all instances of (4.2) after refinement = ", residual_42);
print("max residual in all instances of (4.3) after refinement = ", residual_43);
check("refined phases satisfy all numerical (4.2) checks", residual_42 < 1e-90);
check("refined phases satisfy all numerical (4.3) checks", residual_43 < 1e-90);

eta_refined_pol = prod(g=1, 12, x + Brefined[g+1,(2*g)%13+1]^2/delta_plus);
refined_coefficient_error = vecmax(vector(13, k, abs(polcoef(eta_refined_pol, k-1) - polcoef(eta_physical, k-1))));
print("max coefficient error after phase refinement = ", refined_coefficient_error);
check("100-digit refinement supports coefficient recognition", refined_coefficient_error < 1e-90);

eta_factorization = nffactor(bnf, eta_hi);
check("HI eta polynomial is irreducible over K", matsize(eta_factorization)[1] == 1 && poldegree(eta_factorization[1,1]) == 12);
check("HI eta polynomial is reciprocal", x^12 * subst(eta_hi, x, 1/x) == eta_hi);
check("HI eta has relative norm 1", polcoef(eta_hi, 0) == 1);

eta_reldisc = rnfdisc(bnf, eta_hi)[1];
expected_reldisc = idealpow(bnf, pp, 11);
check("HI relative discriminant is (delta-1)^11", eta_reldisc == expected_reldisc);
check("Stark relative discriminant is (delta-1)^11", rnfdisc(bnf, stark)[1] == expected_reldisc);
print("relative discriminant HNF = ", eta_reldisc);

eta_conductor = rnfconductor(bnf, eta_hi);
check("HI finite conductor is (delta-1)", eta_conductor[1][1] == pp);
check("HI infinite conductor is infinity_+", eta_conductor[1][2] == [0,1]);
check("HI is the full C12 ray field", eta_conductor[2].cyc == [12] && eta_conductor[3] == Mat(12));

eta_abs_data = rnfequation(bnf, eta_hi, 1);
stark_abs_data = rnfequation(bnf, stark, 1);
check("absolute generators are the relative eta/Stark roots", eta_abs_data[3] == 0 && stark_abs_data[3] == 0);
isos = nfisisom(eta_abs_data[1], stark_abs_data[1]);
check("HI and Stark polynomials define isomorphic absolute fields", #isos == 12);
base_preserving = vector(#isos, j, subst(eta_abs_data[2], x, isos[j]) == stark_abs_data[2]);
check("all 12 displayed isomorphisms fix K", vecsum(base_preserving) == 12);

expected_abs_disc = 173^12 * 13^11;
check("HI absolute discriminant is 173^12*13^11", nfdisc(eta_abs_data[1]) == expected_abs_disc);
check("Stark absolute discriminant is 173^12*13^11", nfdisc(stark_abs_data[1]) == expected_abs_disc);
check("HI absolute signature is (12,6)", nfinit(eta_abs_data[1]).sign == [12,6]);
check("ray conductor-discriminant calculation agrees", bnrdisc(bnr_plus)[3] == expected_abs_disc);

print("HI polynomial equals PARI Stark polynomial? ", eta_hi == stark);

\\ Search exact two-conjugate Stark-orbit relations.  In rnfequation(...,1)
\\ the absolute generator x is the relative Stark root, while data[2]
\\ expresses the base generator delta in that absolute field.
abs_stark_pol = stark_abs_data[1];
id_aut = Mod(x, abs_stark_pol);
autorder(a) = { my(t=id_aut, n=0); while(1, n++; t=subst(a,x,t); if(t==id_aut, return(n))) };
all_auts = nfgaloisconj(abs_stark_pol);
relative_auts = List();
for(j=1, #all_auts, if(subst(stark_abs_data[2], x, all_auts[j]) == stark_abs_data[2], listput(relative_auts, all_auts[j])));
relative_auts = Vec(relative_auts);
check("there are 12 K-automorphisms", #relative_auts == 12);
generator_index = 0;
for(j=1, #relative_auts, if(autorder(relative_auts[j]) == 12, generator_index=j; break));
check("relative Galois group has an order-12 generator", generator_index > 0);
tau = relative_auts[generator_index];
tau_powers = vector(12);
tau_powers[1] = id_aut;
for(j=2, 12, tau_powers[j] = subst(tau, x, tau_powers[j-1]));

short_relations = List();
for(ei=1, #isos, for(a=1, 12, for(b=1, 12, if(isos[ei]^2 * tau_powers[b] == tau_powers[a]^2, listput(short_relations, [ei, a-1, b-1])))));
print("relations eta_image^2 = tau^a(s)^2/tau^b(s), as [image,a,b]: ", Vec(short_relations));
check("there is exactly one short relation for every HI conjugate", #short_relations == 12);
check("every short relation has denominator displacement 5 mod 12", vecmin(vector(#short_relations,j,(short_relations[j][3]-short_relations[j][2])%12)) == 5 && vecmax(vector(#short_relations,j,(short_relations[j][3]-short_relations[j][2])%12)) == 5);
check("exact short relation eta_image^2=tau^8(s)^2/tau(s)", isos[1]^2 * tau_powers[2] == tau_powers[9]^2);
print("after s0=tau^8(s), rho=tau^5: eta_image^2 = s0^2/rho(s0)");

q2 = idealhnf(bnf, 2);
q2_dec = idealprimedec(bnf, 2);
check("2 is inert in K and q2=(2) has norm 4", #q2_dec == 1 && idealhnf(bnf, q2_dec[1]) == q2 && idealnorm(bnf, q2) == 4);
check("q2=(2) is PARI's ray-group generator", bnrisprincipal(bnr_plus, q2, 0) == [1]~);
check("the absolute Stark polynomial is irreducible modulo 2", polisirreducible(Mod(abs_stark_pol, 2)));
check("tau^5(s) has integral polynomial representative", denominator(lift(tau_powers[6])) == 1);
check("tau^5(s) reduces to s^4 modulo 2", Mod(lift(tau_powers[6]), 2) == Mod(x^4, 2));
print("Thus rho=tau^5 is arithmetic Frob_(2) over K; (2) is represented by residue 2 mod (delta-1), up to reciprocity inversion.");
stark_H_norm = prod(k=0,11,tau_powers[(5*k)%12+1]);
check("the Stark norm over <Frob_(2)>=G is one", stark_H_norm == 1);

stark_to_hi = List();
hi_to_stark = List();
for(k=1, 6, pk = polresultant(subst(stark, x, z), x-z^k, z); if(pk == eta_hi, listput(stark_to_hi, k)); qk = polresultant(subst(eta_hi, x, z), x-z^k, z); if(qk == stark, listput(hi_to_stark, k)));
print("k in [1,6] with Stark^k = HI: ", Vec(stark_to_hi));
print("k in [1,6] with HI^k = Stark: ", Vec(hi_to_stark));

delta_minus = (13 - sqrt(173))/2;
hi_plus_roots = polroots(subst(lift(eta_hi), y, delta_plus));
hi_minus_roots = polroots(subst(lift(eta_hi), y, delta_minus));
stark_plus_roots = polroots(subst(lift(stark), y, delta_plus));
stark_minus_roots = polroots(subst(lift(stark), y, delta_minus));
print("max ||HI root|-1| at physical place = ", vecmax(vector(#hi_plus_roots, i, abs(abs(hi_plus_roots[i])-1))));
print("HI positive-real range at conjugate place = [", vecmin(real(hi_minus_roots)), ", ", vecmax(real(hi_minus_roots)), "]");
print("max ||Stark root|-1| at physical place = ", vecmax(vector(#stark_plus_roots, i, abs(abs(stark_plus_roots[i])-1))));
print("Stark positive-real range at conjugate place = [", vecmin(real(stark_minus_roots)), ", ", vecmax(real(stark_minus_roots)), "]");

print("eta_hi = ", eta_hi);
print("stark = ", stark);
