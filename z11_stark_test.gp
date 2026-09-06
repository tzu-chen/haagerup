\\ Exact ray-class checks for the two p=11 Haagerup-Izumi candidates.
\\ Run with: gp -q z11_stark_test.gp
\\ Requires PARI/GP with bnrstarkunit (tested with 2.17.4).
\\
\\ IMPORTANT: the quadratic second-branch polynomial below is exact input.
\\ The degree-10 principal-branch polynomial was reconstructed from the
\\ published numerical Evans-Gannon phase seed.  This script verifies that
\\ reconstructed polynomial exactly as an algebraic/class-field candidate;
\\ it does not independently derive it from the exact Izumi equations.

check(label, condition) =
{
  if(!condition, error(Str("check failed: ", label)));
  print("[ok] ", label);
};

default(parisizemax, 2000000000);
default(realprecision, 100);

T = y^2 - 11*y - 1;
bnf = bnfinit(T, 1);
delta = Mod(y, T);
epsilon = (delta - 3)/5;
pp = idealhnf(bnf, delta - 1);

check("base-field class/unit data certify unconditionally", bnfcertify(bnf) == 1);
check("epsilon is the fundamental unit (delta-3)/5", epsilon == bnf.fu[1]);
check("delta = epsilon^5", delta == epsilon^5);
check("Norm((delta-1)) = 11", idealnorm(bnf, pp) == 11);

real_roots = polrootsreal(T);
print("real roots of delta polynomial = ", real_roots);
check("PARI's second real place is the physical delta > 0 place", real_roots[1] < 0 && real_roots[2] > 0);

\\ PARI orders the real places as the roots printed above.  Thus [0,1]
\\ selects infinity_+ (delta > 0), while [1,0] selects infinity_-.
bnr_minus = bnrinit(bnf, [pp, [1,0]], 1);
bnr_plus  = bnrinit(bnf, [pp, [0,1]], 1);
print("ray group for (delta-1) infinity_- = ", bnr_minus.clgp);
print("ray group for (delta-1) infinity_+ = ", bnr_plus.clgp);
check("the physical simple ray group is C2", bnr_plus.no == 2 && bnr_plus.cyc == [2]);
check("the opposite single-infinity ray group is trivial", bnr_minus.no == 1);

\\ -----------------------------------------------------------------------
\\ Second Evans-Gannon branch: exact quadratic field and Stark normalization
\\ -----------------------------------------------------------------------

Q_second = x^2 + (3*delta - 4)/5*x + delta;
check("Q_second is the stated sqrt(5) polynomial in delta coordinates", (3*delta - 4)/5 == (5 + 3*Mod(2*y-11, T)/5)/2);
check("disc(Q_second) = -(delta-1)", poldisc(Q_second) == -(delta-1));

second_ray_pol = bnrclassfield(bnr_plus,, 1);
second_ray_expected = x^2 + (3*delta - 14)/5;
check("PARI returns the expected relative quadratic class-field polynomial", second_ray_pol == second_ray_expected);
check("delta-1 differs from the class-field radicand by epsilon^2", delta - 1 == epsilon^2 * (3*delta - 14)/5);

second_stark = bnrstarkunit(bnr_plus);
second_stark_expected = x^2 + (3*delta - 24)/5*x + 1;
check("PARI returns the expected quadratic Stark-unit polynomial", second_stark == second_stark_expected);

\\ If u is a root of second_stark, then t=1+epsilon^3*u is a root of
\\ Q_second.  This fixes the normalization, modulo choosing/inverting a root.
check("exact affine normalization Q(1+epsilon^3*u)=epsilon^6*S(u)", subst(Q_second, x, 1 + epsilon^3*x) == epsilon^6*second_stark);

second_reldisc = rnfdisc(bnf, Q_second)[1];
check("second-branch relative discriminant is (delta-1)", second_reldisc == pp);
second_conductor = rnfconductor(bnf, Q_second);
check("second-branch finite conductor is (delta-1)", second_conductor[1][1] == pp);
check("second-branch infinite conductor is infinity_+", second_conductor[1][2] == [0,1]);
check("second branch is the full C2 ray field", second_conductor[2].cyc == [2] && second_conductor[3] == Mat(2));

second_abs_Q = rnfequation(bnf, Q_second);
second_abs_ray = bnrclassfield(bnr_plus,, 2);
check("absolute Q polynomial is the expected quartic", second_abs_Q == x^4 + 5*x^3 + 6*x^2 - 10*x - 1);
check("absolute ray polynomial is x^4+x^2-11", second_abs_ray == x^4 + x^2 - 11);
check("the two absolute quartics define isomorphic fields", #nfisisom(second_abs_Q, second_abs_ray) > 0);
check("second-branch absolute field discriminant is -275", nfdisc(second_abs_Q) == -275 && nfdisc(second_abs_ray) == -275);

\\ -----------------------------------------------------------------------
\\ Principal branch: exact checks on a numerically reconstructed candidate
\\ -----------------------------------------------------------------------

q5 = idealprimedec(bnf, 5)[1];
check("5 is ramified as q5^2", idealpow(bnf, q5, 2) == idealhnf(bnf, 5));

principal_fin = idealmul(bnf, pp, idealpow(bnf, q5, 2));
principal_bnr = bnrinit(bnf, [principal_fin, [0,1]], 1);
print("ray group for (delta-1) q5^2 infinity_+ = ", principal_bnr.clgp);
check("principal candidate ray group is C10", principal_bnr.no == 10 && principal_bnr.cyc == [10]);
check("the displayed modulus is the conductor of the full ray field", bnrconductor(principal_bnr) == [principal_fin, [0,1]]);

\\ For B=(delta-1)A, set eta=-B^2/delta.  The following reciprocal
\\ polynomial is the exact recognition of the eta orbit obtained from the
\\ numerical principal seed; it is input data here, not a theorem about HI.
c1 = 144*delta - 1597;
c2 = 854377 - 77039*delta;
c3 = 15771418*delta - 174907704;
c4 = 13808071707 - 1245073049*delta;
c5 = 27511525729*delta - 305107495744;

eta_principal = x^10 + c1*x^9 + c2*x^8 + c3*x^7 + c4*x^6 + c5*x^5 + c4*x^4 + c3*x^3 + c2*x^2 + c1*x + 1;

\\ Reproduce the low-precision recognition check directly from the five
\\ published phases j_2,...,j_6.  Refining these phases is deliberately not
\\ part of this exact arithmetic script.
delta_plus = (11 + 5*sqrt(5))/2;
jseed = [0, 0, 0.9996507, 2.7258434, -0.5714203, -1.7797340, 1.2675985, 0, 0, 0, 0];
for(i=1, 4, jseed[7+i] = jseed[7] + jseed[6] - jseed[6-i]);
Bseed = vector(10, g, h = (2*g) % 11; if(g < h, sqrt(delta_plus) * exp(I*(jseed[h+1] - jseed[g+1] - jseed[h-g+1])), conj(sqrt(delta_plus) * exp(I*(jseed[g+1] - jseed[h+1] - jseed[g-h+1])))));
eta_seed_pol = prod(g=1, 10, x + Bseed[g]^2/delta_plus);
eta_physical = subst(lift(eta_principal), y, delta_plus);
seed_coefficient_error = vecmax(vector(11, k, abs(polcoef(eta_seed_pol, k-1) - polcoef(eta_physical, k-1))));
print("max coefficient error against published 7-digit seed = ", seed_coefficient_error);
check("recognized eta polynomial matches the published seed precision", seed_coefficient_error < 2e-6);

\\ Refine the five principal phases by Newton iteration on the independent
\\ (4.2) instances (g,h)=(8,8),(1,5),(1,10),(5,6),(7,4).  The values
\\ below retain 100 digits of that refinement.  We check all of (4.2) and
\\ all 11^4 instances of (4.3), as well as the recognized eta polynomial.
\\ These are high-precision numerical checks, not an exact derivation of
\\ the reconstructed HI polynomial used by the exact arithmetic below.
jrefined = [0, 0, 0.9996506769567544532919433367481342195325320657135598173938939089032387552605852995173445396216636687, 2.725843437775186706566723159369740519805158673976034516889325392459254665070860594507430089624926237, -0.5714202715143507363695600119686578979284094770031389619691698729846582339767806414630055522305007353, -1.779734032818599810712273127995369425327447754180969726776275690833831980247702624275032952541376222, 1.267598444982486619544871991362638491396461047154769789178909086802300604300646553301255196755512095, 0, 0, 0, 0];
for(i=1, 4, jrefined[7+i] = jrefined[7] + jrefined[6] - jrefined[6-i]);
Bphase(g,h,jv,dv) = { if(g==0 && h==0, return(dv-2)); if(g==0 || h==0 || g==h, return(-1)); if(g<h, return(sqrt(dv)*exp(I*(jv[h+1]-jv[g+1]-jv[h-g+1]))), return(conj(sqrt(dv)*exp(I*(jv[g+1]-jv[h+1]-jv[g-h+1]))))) };
Brefined = matrix(11, 11, ig, ih, Bphase(ig-1, ih-1, jrefined, delta_plus));
Arefined = Brefined/(delta_plus-1);
residual_42 = 0;
for(g=0, 10, for(h=0, 10, lhs42=sum(m=0, 10, Arefined[(g+m)%11+1,h+1]*conj(Arefined[m+1,h+1])); rhs42=(g==0)-(h==0)/delta_plus; residual_42=max(residual_42,abs(lhs42-rhs42))));
residual_43 = 0;
for(g=0, 10, for(h=0, 10, for(k=0, 10, for(l=0, 10, lhs43=sum(m=0, 10, Arefined[m+1,(g+h)%11+1]*conj(Arefined[(m+k)%11+1,g+1]*Arefined[(m+l)%11+1,h+1])); rhs43=Arefined[(g+l)%11+1,k+1]*Arefined[(h+k)%11+1,l+1]-((g==0 && h==0)/delta_plus); residual_43=max(residual_43,abs(lhs43-rhs43))))));
print("max residual in all instances of (4.2) after refinement = ", residual_42);
print("max residual in all instances of (4.3) after refinement = ", residual_43);
check("refined phases satisfy all numerical (4.2) checks", residual_42 < 1e-90);
check("refined phases satisfy all numerical (4.3) checks", residual_43 < 1e-90);

eta_refined_pol = prod(g=1, 10, x + Brefined[g+1,(2*g)%11+1]^2/delta_plus);
refined_coefficient_error = vecmax(vector(11, k, abs(polcoef(eta_refined_pol, k-1) - polcoef(eta_physical, k-1))));
print("max eta coefficient error after phase refinement = ", refined_coefficient_error);
check("refined phases support the exact eta coefficient recognition", refined_coefficient_error < 1e-88);

eta_factorization = nffactor(bnf, eta_principal);
check("principal eta polynomial is irreducible over K", matsize(eta_factorization)[1] == 1 && poldegree(eta_factorization[1,1]) == 10);
check("principal eta polynomial is reciprocal", x^10 * subst(eta_principal, x, 1/x) == eta_principal);
check("principal eta has relative norm 1", polcoef(eta_principal, 0) == 1);

principal_reldisc = rnfdisc(bnf, eta_principal)[1];
expected_reldisc = idealmul(bnf, idealpow(bnf, q5, 16), idealpow(bnf, pp, 9));
check("principal relative discriminant is q5^16 (delta-1)^9", principal_reldisc == expected_reldisc);
print("principal relative discriminant factorization = ", idealfactor(bnf, principal_reldisc));

principal_conductor = rnfconductor(bnf, eta_principal);
check("principal finite conductor is (delta-1) q5^2", principal_conductor[1][1] == principal_fin);
check("principal infinite conductor is infinity_+", principal_conductor[1][2] == [0,1]);
check("conductor ray group is C10", principal_conductor[2].cyc == [10]);
\\ In PARI's subgroup convention Mat(10) is 10 Z inside Z, hence the
\\ trivial subgroup of the cyclic ray group Z/10 Z.
check("principal norm subgroup is trivial (the full ray field)", principal_conductor[3] == Mat(10));

principal_abs = rnfequation(bnf, eta_principal);
expected_abs_disc = -5^26 * 11^9;
check("principal absolute field discriminant is -5^26*11^9", nfdisc(principal_abs) == expected_abs_disc);
check("ray conductor-discriminant calculation gives the same discriminant", bnrdisc(principal_bnr)[3] == expected_abs_disc);

principal_class_pol = bnrclassfield(principal_bnr,, 1);
eta_abs_data = rnfequation(bnf, eta_principal, 1);
class_abs_data = rnfequation(bnf, principal_class_pol, 1);
principal_isos = nfisisom(eta_abs_data[1], class_abs_data[1]);
check("eta field is isomorphic to the degree-10 ray class field", #principal_isos == 10);
base_preserving = vector(#principal_isos, j, subst(eta_abs_data[2], x, principal_isos[j]) == class_abs_data[2]);
check("all 10 displayed isomorphisms preserve K", vecsum(base_preserving) == 10);

principal_stark = bnrstarkunit(principal_bnr);
check("principal Stark polynomial has degree 10", poldegree(principal_stark) == 10);
check("principal Stark polynomial is reciprocal", x^10 * subst(principal_stark, x, 1/x) == principal_stark);
print("principal eta polynomial equals PARI Stark polynomial? ", eta_principal == principal_stark);

print("second Q polynomial = ", Q_second);
print("second Stark polynomial = ", second_stark);
print("principal eta polynomial = ", eta_principal);
print("principal ray class polynomial = ", principal_class_pol);
