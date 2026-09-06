\\ Exact p=17 Stark/ray-class test for the Haagerup-Izumi candidate.
\\ Run with: gp -q z17_stark_test.gp
\\ Requires PARI/GP with bnrstarkunit (tested with 2.17.4).

check(label, condition) =
{
  if(!condition, error(Str("check failed: ", label)));
  print("[ok] ", label);
};

default(parisizemax, 2000000000);
default(realprecision, 100);

T = y^2 - 17*y - 1;
bnf = bnfinit(T, 1);
delta = Mod(y, T);
pp = idealhnf(bnf, delta - 1);

check("base-field class/unit data certify unconditionally", bnfcertify(bnf) == 1);
check("Norm((delta-1)) = 17", idealnorm(bnf, pp) == 17);
print("real roots of delta polynomial = ", polrootsreal(T));

\\ PARI orders the real places as the roots printed above.  Hence [0,1]
\\ selects delta > 0, whereas [1,0] selects its negative conjugate.
bnr_minus = bnrinit(bnf, [pp, [1,0]], 1);
bnr_plus  = bnrinit(bnf, [pp, [0,1]], 1);
print("ray group at infinity_- = ", bnr_minus.clgp);
print("ray group at infinity_+ = ", bnr_plus.clgp);
check("physical ray group is cyclic of order 16", bnr_plus.no == 16 && bnr_plus.cyc == [16]);

stark = bnrstarkunit(bnr_plus);
check("Stark polynomial has degree 16", poldegree(stark) == 16);
stark_factorization = nffactor(bnf, stark);
check("Stark polynomial is irreducible over K", matsize(stark_factorization)[1] == 1 && poldegree(stark_factorization[1,1]) == 16);
check("Stark polynomial is reciprocal", x^16 * subst(stark, x, 1/x) == stark);
check("Stark field relative discriminant is (delta-1)^15", rnfdisc(bnf, stark)[1] == idealpow(bnf, pp, 15));

\\ P2 is the exact polynomial of B=(delta-1)A for ratio type t=2.
coeff2 = [[1,0],[-1,0],[-2580,150],[7856,-462],[1421008,-83294],[-4237905,248395],[-107944297,6328294],[-140236552,8221011],[643252625,-37715514],[8221011,-479365],[-363299,152211],[-9835,-182385],[36902,629210],[-124086,-2116736],[-1789620,-30528450],[-1439560,-24556909],[24556909,418907013]];

P2 = sum(i=1, #coeff2, (coeff2[i][1] + coeff2[i][2]*delta) * z^(#coeff2-i));
check("B orbit polynomial is irreducible over K", matsize(nffactor(bnf,subst(P2,z,x)))[1] == 1);

\\ epsilon_HI=-B^2/delta, so eliminate B with B^2+delta*x=0.
eps_hi = polresultant(P2, x + z^2/delta, z);

check("HI epsilon polynomial has degree 16", poldegree(eps_hi) == 16);
eps_factorization = nffactor(bnf, eps_hi);
check("HI epsilon polynomial is irreducible over K", matsize(eps_factorization)[1] == 1 && poldegree(eps_factorization[1,1]) == 16);
check("K(epsilon_HI)=K(B) by inclusion and equal degree", poldegree(lift(P2),z) == poldegree(eps_hi));
check("HI epsilon polynomial is reciprocal", x^16 * subst(eps_hi, x, 1/x) == eps_hi);
check("HI epsilon has relative norm 1", polcoef(eps_hi, 0) == 1);

reldisc = rnfdisc(bnf, eps_hi)[1];
check("relative discriminant is (delta-1)^15", reldisc == idealpow(bnf, pp, 15));
print("relative discriminant HNF = ", reldisc);
eps_conductor = rnfconductor(bnf,eps_hi);
check("HI conductor is exactly (delta-1) infinity_+", eps_conductor[1] == [pp,[0,1]]);
check("HI field is the full C16 ray field", eps_conductor[2].cyc == [16] && eps_conductor[3] == Mat(16));

\\ Compare the two relative extensions through absolute equations.  There
\\ are 16 K-preserving isomorphisms, as expected for the cyclic ray field.
abs_hi = rnfequation(bnf, eps_hi, 1);
abs_stark = rnfequation(bnf, stark, 1);
isos = nfisisom(abs_hi[1], abs_stark[1]);
check("HI and Stark polynomials define isomorphic absolute fields", #isos == 16);
base_preserving = vector(#isos, j, subst(abs_hi[2], x, isos[j]) == abs_stark[2]);
check("all 16 displayed isomorphisms fix K", vecsum(base_preserving) == 16);

check("relative polynomial reductions agree", rnfpolredabs(bnf,eps_hi,1)[1] == rnfpolredabs(bnf,stark,1)[1]);
expected_abs_disc = 293^16 * 17^15;
check("HI absolute discriminant is 293^16*17^15", nfdisc(abs_hi[1]) == expected_abs_disc);
check("Stark absolute discriminant is 293^16*17^15", nfdisc(abs_stark[1]) == expected_abs_disc);
check("HI absolute signature is (16,8)", nfinit(abs_hi[1]).sign == [16,8]);

print("HI polynomial equals PARI Stark polynomial? ", eps_hi == stark);

\\ A stronger exact relation is visible after choosing generators.  Here s
\\ is the root of the PARI Stark polynomial, e is one K-isomorphic image of
\\ epsilon_HI, and tau is the first order-16 K-automorphism returned by
\\ nfgaloisconj.  Changing these choices only Galois-shifts/inverts labels.
abs_stark_pol = abs_stark[1];
id_aut = Mod(x, abs_stark_pol);
autorder(a) = { my(t=id_aut, n=0); while(1, n++; t=subst(a,x,t); if(t==id_aut, return(n))) };
galois_conjugates = nfgaloisconj(abs_stark_pol);
generator_index = 0;
for(j=1, #galois_conjugates, if(autorder(galois_conjugates[j]) == 16, generator_index=j; break));
check("the relative Galois group has an order-16 generator", generator_index > 0);
tau = galois_conjugates[generator_index];
tau_powers = vector(16);
tau_powers[1] = id_aut;
for(j=2, 16, tau_powers[j] = subst(tau, x, tau_powers[j-1]));
epsilon_in_stark_field = isos[1];
check("exact short Stark-orbit relation", epsilon_in_stark_field^2 * tau_powers[6] == tau_powers[12]^2);
print("exactly: epsilon_HI^2 = tau^11(s)^2 / tau^5(s)");
print("after s0=tau^11(s), sigma=tau^5: epsilon_HI^2 = s0^2 / sigma^2(s0)");

\\ Since sigma^2=tau^10, reduction at the inert prime (2) identifies
\\ the quotient automorphism with arithmetic Frobenius there.
q2 = idealhnf(bnf,2);
q2_dec = idealprimedec(bnf,2);
check("2 is inert in K and q2=(2) has norm 4", #q2_dec == 1 && idealhnf(bnf,q2_dec[1]) == q2 && idealnorm(bnf,q2) == 4);
check("q2 has order eight in the C16 ray group", gcd(lift(bnrisprincipal(bnr_plus,q2,0)[1]),16) == 2);
check("rho=tau^10 has an integral polynomial representative", denominator(lift(tau_powers[11])) == 1);
check("rho=tau^10 reduces to arithmetic Frobenius x^4 modulo 2", Mod(lift(tau_powers[11]),2) == Mod(x^4,2));
print("Thus rho=Frob_(2), of order 8=ord_17(2), up to the reciprocity convention.");
stark_H_norm = prod(k=0,7,tau_powers[(10*k)%16+1]);
check("the Stark norm over <Frob_(2)> is one", stark_H_norm == 1);

\\ Exact unit coordinates rule out any multiplicative dependence between
\\ the HI unit and a single conjugate of the Stark root.
abs_bnf = bnfinit(abs_stark_pol,1);
epsilon_coords = bnfisunit(abs_bnf,epsilon_in_stark_field);
power_ranks = vector(16,j,matrank(Mat([epsilon_coords,bnfisunit(abs_bnf,tau_powers[j])])));
check("HI unit is not power-related to an individual Stark conjugate", vecmin(power_ranks) == 2 && vecmax(power_ranks) == 2);

\\ A Galois relabeling cannot alter a minimal polynomial.  The following
\\ checks the stronger possible explanation epsilon_HI = epsilon_Stark^k
\\ (or its converse) for small k.  Numerical extrema at the nonphysical
\\ embedding already rule out |k| >= 2; these exact checks include them.
stark_to_hi = List();
hi_to_stark = List();
for(k=1, 8, pk = polresultant(subst(stark, x, z), x-z^k, z); if(pk == eps_hi, listput(stark_to_hi, k)); qk = polresultant(subst(eps_hi, x, z), x-z^k, z); if(qk == stark, listput(hi_to_stark, k)));
print("k in [1,8] with Stark^k = HI: ", Vec(stark_to_hi));
print("k in [1,8] with HI^k = Stark: ", Vec(hi_to_stark));

delta_plus  = (17 + sqrt(293))/2;
delta_minus = (17 - sqrt(293))/2;
hi_plus_roots = polroots(subst(lift(eps_hi), y, delta_plus));
hi_minus_roots = polroots(subst(lift(eps_hi), y, delta_minus));
stark_plus_roots = polroots(subst(lift(stark), y, delta_plus));
stark_minus_roots = polroots(subst(lift(stark), y, delta_minus));

print("max ||HI root|-1| at physical place = ", vecmax(vector(#hi_plus_roots, i, abs(abs(hi_plus_roots[i])-1))));
print("HI positive-real range at conjugate place = [", vecmin(real(hi_minus_roots)), ", ", vecmax(real(hi_minus_roots)), "]");
print("max ||Stark root|-1| at physical place = ", vecmax(vector(#stark_plus_roots, i, abs(abs(stark_plus_roots[i])-1))));
print("Stark positive-real range at conjugate place = [", vecmin(real(stark_minus_roots)), ", ", vecmax(real(stark_minus_roots)), "]");

print("eps_hi = ", eps_hi);
print("stark = ", stark);
