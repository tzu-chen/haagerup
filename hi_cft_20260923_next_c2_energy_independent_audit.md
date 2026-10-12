# Independent audit of the C2 energy bound and finite properness criterion

23 September2026. Read-only source/algebra audit; no numerical job.
Audited `hi_cft_20260923_next_structure_c2_energy_bound.md`.

**Verdict:** the C2 argument, the bound16748, and the finite polynomial
properness equivalence pass. Below are details addressing the delicate
restriction and module-truncation points, plus reductions from the exact
low-degree certificates. This result still does not supply a low-degree
strong generating set or prove properness.

## Restriction to a different conformal vector

There is a direct spectral proof that avoids a choice of orthogonal
algebraic irreducible summands. Put H=L_V(0), H_i=L_i(0). Since omega_i
has ambient weight two, [H,H_i]=0. Both operators are self-adjoint and
each ambient grade V_n is finite dimensional. Thus H_i has an orthogonal
eigenbasis on V_n. The hypothesis that intrinsic and ambient weights
agree on A_i gives

    [H-H_i,a_m]=0  for homogeneous a in A_i.

Regularity, applied to V as a weak A_i-module, gives an algebraic direct
sum of ordinary simple modules. In each summand every H_i-eigenvector
of eigenvalue greater than D_i lies in its module C2 space. Consequently
the whole H_i-eigenspace of eigenvalue greater than D_i lies in
C2_Ai(V), regardless of multiplicity or ambient shifts.

Both C2_Ai(V) and C2(V) are ambient homogeneous. If v is in
V_n intersect C2(V)-perp, then its projection to every H_i-eigenspace
above D_i is zero, since C2_Ai(V) is contained in C2(V). Therefore
<H_i v,v><=D_i||v||^2. This is all the energy inequality needs; the
different H_i need not commute with each other. The compact averages
are likewise taken inside the finite-dimensional V_n. No completion,
finite branching, or rationality of a coset is being assumed here.

The finite-dimensional module C2 quotient used in this step is exactly
the quotient in [Abe--Buhl--Dong, Proposition5.2](https://arxiv.org/html/math/0204021#S5).

## The explicit module truncation

The conventions in [Abe--Buhl--Dong, Remark3.2 and Theorem3.3](https://arxiv.org/html/math/0204021#S3)
match the note: for highest representative weight R, their Q is2R;
the nonpositive displayed indices occur at mostQ-1 times. On an
ordinary top vector, every mode x_m with m>=R vanishes, so L<=R.

Any displayed outer index n>=2 gives a module C2 vector: the translation
identity expresses a_(-n)m as a nonzero scalar multiple of
(T^(n-2)a)_(-2)m. In a surviving ordered spanning monomial there can
be only one index1, contributing at mostR. For indices0,-1,...,-R+1
the respective increases are bounded byR-1,R-2,...,0. Their total is
therefore at most(2R-1)R(R-1)/2. Adding the actual lowest weight h,
not just a relative grade, gives precisely the asserted formula.
Negative individual energy increases only improve this upper bound.

For the affine improvement, the action of R_A=A/C2(A) on
M/C2_A(M) is valid. The commutator identity shows that a_(-1)
preserves C2_A(M). The iterate identity makes (a_(-2)b)_(-1)
zero in the quotient, and makes the two possible associative products
agree there. Thus the action factors through R_A. Affine PBW reduces
to negative current modes acting on the horizontal top; every mode
of index<=-2 is zero modulo module C2. This proves generation over
R_A by the top, giving h_max+2k from the stated vacuum bound.

The affine basis in [Arakawa--Lam--Yamada, Eq.(7.1)](https://arxiv.org/html/1207.3909#S7)
has maximal degree2k. Their graded parafermion injection, Theorem7.3,
and Lemma6.9 give R<=26 at k=13; no small-level extension is needed.

The separate Potts argument also checks. In
[Dong--Lam--Yamada, AppendixB](https://arxiv.org/html/0809.3630#A2),
specializing W4_1 W4 at k=3 gives y^2=25650x^3; specializing
W4_1 W5 gives a nonzero coefficient times x^2y=0. W3_1 W3
gives38880x^2, and primary skew symmetry gives W3_1 omega=3W3.
The induced W3_0 bracket is zero on x,y, hence on their Poisson
algebra. Consequently W3_1 preserves C2 and induces a derivation:
the extra commutator term involves W3_0 a and is in C2. Applying
the derivation to x^2y gives(6*25650+38880)x^4=192780x^4=0.
The proposed six spanning monomials thus all have weight<=6.

I independently checked the final rational combination algebraically:
the two affine contributions sum to880/13; adding12875/18 and
5396375/338 gives25474585/1521. This lies strictly between16748
and16749. Hence the integer-grade conclusion is correct. The PF13
and Potts ordinary-top maxima used here are the already certified
top-table inputs, not new deductions of this audit.

## Finite polynomial properness: why the closure test is sufficient

Take N_0(G)=C*1, including the empty normal product. For positive
weights, allow all normal-product parenthesizations and derivatives;
there are finitely many at each fixed weight. This convention removes
any unnecessary reliance on an a priori associativity of normal order.

If every generator singular product belongs to the indicated N_w(G),
the usual commutator/iterate straightening terminates. One may filter
words by the sum of the conformal weights of their generator entries.
Every singular replacement of a pair of weights i,j has total weight
i+j-n-1<i+j. Derivative decorations can be included in that weight.
Thus contractions lower this nonnegative filtration; normal products
and translations supply the remaining operations. This proves that
the strong span is a vertex subalgebra. Free generation or absence of
relations is not required: all identities are evaluated in the already
existing ambient VOA B.

The equations are genuinely polynomial after introducing membership
coefficients. Zero and redundant generator entries cause no problem,
so no determinant/nonvanishing conditions are necessary. Products with
n>i+j-1 vanish by CFT type. Every required output has weight<=2D-1.
The fixed six independent currents make W1=K1, while the original
generators are required to lie in W. Therefore a solution gives
U subset W subset B and W1!=B1, proving U proper. Conversely, C2
representatives of a proper U through D, with the prescribed generators
adjoined, supply a solution.

For a real formulation, use a PCT-real basis for K1 as well as the
ambient graded spaces, or encode PCT stability with explicit linear
conjugation equations. The displayed raising/lowering currents need
not each themselves be PCT-fixed. This is a coordinate clarification,
not an obstruction to the finite equivalence.

## Reductions from B=U direct-sum X

Under properness, any intermediate vertex subalgebra W containing U is
a U-submodule of B. The two summands U and X are nonisomorphic simples,
so W is either U or B. In particular the finite-criterion solution with
W1=K1 must actually equal U. No rationality assumption on W is needed.

The exact X2 rank certificate already forces U2=S2 under properness.
Thus in the finite feasibility problem G2 may be fixed to a basis of
the known120-dimensional S2; no unknown ambient degree-two directions
are needed. This neither weakens necessity nor sufficiency. If the
current X3 job reaches10630, exactly the same reduction fixes G3
inside the certified956-dimensional S3. More generally, any finite
span of known U words on the exact X1 gives necessary linear
orthogonality constraints on candidate U_j under properness. Such
constraints can cut down unknown higher generator coordinates; they
do not remove the need for singular-product closure.

## Existing exact data rule out strong generation in weights one and two

For generators K1 and all of S2, the degree-three strong span is

    N3 = K1_(-1) S2 + T S2.

Current derivatives and current triples are already included. Reversing
the order of a weight-one and weight-two normal product changes it by
derivatives of their singular products, also in this span. The span is
K-zero-mode stable because S2 is, so taking a lowering closure does not
enlarge the mathematical N3.

This is exactly the first stage of the frozen
`hi_cft_20260923_c8_exact_grade3.py`, whose characteristic-zero
certificate `hi_cft_20260923_c8_grade3_exact_v2.json` gives dimension634.
The separately replayable checkpoint
`hi_cft_20260923_next_grade4_checkpoint/checkpoint_000005/manifest.json`
records current descendants536, translation descendants634, and
lowering closure still634. Charged S2 zero-mode products subsequently
increase this to924,953,956. Therefore at least322 new degree-three
strong-generator directions are required for any candidate with
weight-one space K1 and degree-two space S2. These are independent
classes modulo N3, not a claim that every chosen representative is
Virasoro primary. Under the conditional equality U3=S3,322 is exact.

A degree<=3 candidate may take a complement P3 of N3 in S3, of
dimension322, in addition to K1 and S2. The missing singular closure
tests then reach ambient grade5: S2_0 P3 has weight4;
P3_1 P3 has weight4; P3_0 P3 has weight5. All remaining nonnegative
modes and generator pairs must also be checked, including neutral
S2 fields. The old956 certificate is a finite span, not by itself a
certificate for every such product. The current grade-four producer's
u products do not cover these new weight-three-left-field tests.

K-equivariance can reduce the number of checks to highest-weight
channels in tensor products of finite K-modules. It does not justify
omitting channels or their multiplicities. A proof with generators
through degree4 would analogously require singular outputs through
degree7. No source currently certifies either of these enlarged closure
systems, and no runtime/memory estimate for them is asserted here.
