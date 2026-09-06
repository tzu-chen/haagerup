\\ Exact p=7 Haagerup-Izumi/Stark comparison.
\\ Run with: gp -q z7_stark_test.gp
\\ Requires PARI/GP with bnrstarkunit (tested with 2.17.4).
\\
\\ Unlike the p=11 and p=17 input polynomials, the p=7 HI polynomial
\\ below is derived directly from the exact Evans-Gannon construction in
\\ the proof of Theorem 5(d), arXiv:1006.1326, rather than recognized from
\\ a numerical phase seed.

check(label, condition) =
{
  if(!condition, error(Str("check failed: ", label)));
  print("[ok] ", label);
};

default(parisizemax, 2000000000);
default(realprecision, 100);

T = y^2 - 7*y - 1;
bnf = bnfinit(T, 1);
delta = Mod(y, T);
pp = idealhnf(bnf, delta - 1);

check("base-field class/unit data certify unconditionally", bnfcertify(bnf) == 1);
check("Norm((delta-1)) = 7", idealnorm(bnf, pp) == 7);
real_roots = polrootsreal(T);
print("real roots of delta polynomial = ", real_roots);
check("PARI's second real place is the physical delta > 0 place", real_roots[1] < 0 && real_roots[2] > 0);

bnr = bnrinit(bnf, [pp, [0,1]], 1);
print("ray group for (delta-1) infinity_+ = ", bnr.clgp);
check("physical ray group is C6", bnr.no == 6 && bnr.cyc == [6]);

\\ In Evans-Gannon's notation, a=B[1,2] and b is the exceptional
\\ degree-two entry in their exact Z_7 matrix.  They prove
\\   b + conjugate(b) = -2,  b*conjugate(b)=delta,
\\   t=(1+(b+1)(3-delta))/2,
\\ and a,d,conjugate(c) are the roots of
\\   W^3-t W^2+b conjugate(t) W-delta b.
\\ Eliminating b gives the complete six-element multiplier orbit of a.
b_pol = z^2 + 2*z + delta;
t = (1 + (z+1)*(3-delta))/2;
t_bar = 1-t;
a_cubic = w^3 - t*w^2 + z*t_bar*w - delta*z;
P_a = polresultant(b_pol, a_cubic, z);
P_a_expected = w^6 - w^5 + (delta-7)*w^4 + (9-3*delta)*w^3 + w^2 + (-1-7*delta)*w + 7+50*delta;
check("exact Evans-Gannon elimination gives the B[1,2] orbit", P_a == P_a_expected);
check("B[1,2] orbit polynomial is irreducible over K", matsize(nffactor(bnf, subst(lift(P_a),w,x)))[1] == 1);

\\ e=-a^2/delta.
E = polresultant(P_a, x + w^2/delta, w);
E_expected = x^6 + (15*delta-107)*x^5 + (-503*delta+3591)*x^4 + (5153*delta-36794)*x^3 + (-503*delta+3591)*x^2 + (15*delta-107)*x + 1;
check("HI unit polynomial has the expected exact form", E == E_expected);
check("HI unit polynomial is irreducible over K", matsize(nffactor(bnf, E))[1] == 1);
check("HI unit polynomial is reciprocal", x^6*subst(E,x,1/x) == E);
check("HI unit has relative norm one", polcoef(E,0) == 1);
check("HI field relative discriminant is (delta-1)^5", rnfdisc(bnf,E)[1] == idealpow(bnf,pp,5));
E_conductor = rnfconductor(bnf,E);
check("HI conductor is exactly (delta-1) infinity_+", E_conductor[1] == [pp,[0,1]]);
check("HI field is the full C6 ray field", E_conductor[2].cyc == [6] && E_conductor[3] == Mat(6));

S = bnrstarkunit(bnr);
S_expected = x^6 + (19*delta-137)*x^5 + (-503*delta+3591)*x^4 + (1635*delta-11672)*x^3 + (-503*delta+3591)*x^2 + (19*delta-137)*x + 1;
check("PARI returns the expected Stark polynomial", S == S_expected);
check("Stark polynomial is irreducible over K", matsize(nffactor(bnf,S))[1] == 1);
check("Stark field relative discriminant is (delta-1)^5", rnfdisc(bnf,S)[1] == idealpow(bnf,pp,5));
print("HI polynomial equals PARI Stark polynomial? ", E == S);

E_reduced = rnfpolredabs(bnf,E,1);
S_reduced = rnfpolredabs(bnf,S,1);
check("HI and Stark roots generate the same relative field", E_reduced[1] == S_reduced[1]);

\\ Find the exact short relation in a common absolute model.  If tau is
\\ an order-six generator, every match below has b-a=4 mod 6.  After
\\ s0=tau^a(s), rho=tau^4 generates G^2=C3 and e^2=s0^2/rho(s0).
abs_E = rnfequation(bnf,E,1);
abs_S = rnfequation(bnf,S,1);
isos = nfisisom(abs_E[1],abs_S[1]);
check("there are six K-isomorphisms between the fields", #isos == 6);
base_preserving = vector(#isos,j,subst(abs_E[2],x,isos[j]) == abs_S[2]);
check("all six isomorphisms fix K", vecsum(base_preserving) == 6);

P_abs = abs_S[1];
id_aut = Mod(x,P_abs);
autorder(a) = { my(q=id_aut,n=0); while(1,n++;q=subst(a,x,q);if(q==id_aut,return(n))) };
auts = nfgaloisconj(P_abs);
generator_index = 0;
for(j=1,#auts,if(autorder(auts[j]) == 6,generator_index=j;break));
check("the relative Galois group has an order-six generator", generator_index > 0);
tau = auts[generator_index];
tau_powers = vector(6);
tau_powers[1] = id_aut;
for(j=2,6,tau_powers[j] = subst(tau,x,tau_powers[j-1]));

short_relations = List();
for(i=1,6,for(a=0,5,for(b=0,5,if(isos[i]^2*tau_powers[b+1] == tau_powers[a+1]^2,listput(short_relations,[i,a,b])))));
check("one short relation occurs for every HI conjugate", #short_relations == 6);
check("all relations use a generator of G^2", vecmin(vector(#short_relations,j,gcd((short_relations[j][3]-short_relations[j][2])%6,6))) == 2 && vecmax(vector(#short_relations,j,gcd((short_relations[j][3]-short_relations[j][2])%6,6))) == 2);
print("short-relation triples [HI isomorphism, a, b] = ", Vec(short_relations));
print("after s0=tau^a(s), rho=tau^(b-a): e^2 = s0^2/rho(s0), with rho generating G^2=C3");

\\ Identify that quotient automorphism intrinsically.  The prime (2) is
\\ inert in K, so its residue field has four elements and arithmetic
\\ Frobenius acts by x |-> x^4.  Here rho=tau^4 is exactly that action.
q2 = idealhnf(bnf,2);
q2_dec = idealprimedec(bnf,2);
check("2 is inert in K and q2=(2) has norm 4", #q2_dec == 1 && idealhnf(bnf,q2_dec[1]) == q2 && idealnorm(bnf,q2) == 4);
check("q2 has order three in the C6 ray group", gcd(lift(bnrisprincipal(bnr,q2,0)[1]),6) == 2);
check("rho=tau^4 has an integral polynomial representative", denominator(lift(tau_powers[5])) == 1);
check("rho=tau^4 reduces to arithmetic Frobenius x^4 modulo 2", Mod(lift(tau_powers[5]),2) == Mod(x^4,2));
print("Thus rho=Frob_(2), of order 3=ord_7(2), up to the reciprocity convention.");
stark_H_norm = tau_powers[1]*tau_powers[5]*tau_powers[3];
stark_H_norm_minpoly = minpoly(stark_H_norm);
check("the Stark norm over <Frob_(2)> is not one", stark_H_norm != 1);
check("recorded absolute polynomial of that subgroup norm", stark_H_norm_minpoly == x^4-932*x^3+70*x^2-932*x+1);

\\ A unit-lattice check rules out any pure power relation with one Stark
\\ conjugate.  Torsion signs do not affect the free-coordinate rank.
abs_bnf = bnfinit(P_abs,1);
check("absolute class/unit data certify unconditionally", bnfcertify(abs_bnf) == 1);
e_coords = bnfisunit(abs_bnf,isos[1]);
power_ranks = vector(6,j,matrank(Mat([e_coords,bnfisunit(abs_bnf,tau_powers[j])])));
check("HI unit is not power-related to an individual Stark conjugate", vecmin(power_ranks) == 2 && vecmax(power_ranks) == 2);

print("HI unit polynomial E = ", E);
print("PARI Stark polynomial S = ", S);
