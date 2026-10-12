# Construction of a completely unitary c=8 Haagerup theory

23 September 2026. **The final Gate4 and Gate5 certificate replays passed.**
The finite strong-generation theorem now proves properness of the actual
generated algebra U. This document combines the completed computational
certificates, independently audited algebraic/analytic deductions, and the
published classification/extension theorems used for identification. It
does not claim to reproduce those published classifications from scratch.
All computations were root-run under the permanent resource limits;
this proof synthesis launches no job and changes no frozen artifact.

## Explicit candidate and theorem

Let B=V_(E6+A2) and H=V_(E8), with the specified index-three lattice
extension B⊂H. Fix the current subalgebra K=A1,1⊗A1,39: the first A1
is the E6 root a0=(-1,-2,-3,-2,-1,-2,0,0), and the second is the diagonal
of the principal A1 in A5 and the principal A1 in the external A2.
The lattice basis, cocycle, torus gauge and exact current operators are
fixed in the [construction record](hi_cft_20260923_c8_construction_report.md)
and [exact field file](hi_cft_20260923_c8_exact_fields.json).
In those conventions put

    u = e^(0,0,0,0,0,-1,1,1)
      + (sqrt(13)+3sqrt(-3))/20 e^(0,0,0,1,1,-1,0,0)
      + (sqrt(13)-3sqrt(-3))/20 e^(1,1,0,0,0,-1,0,0),

    U = <K, omega_B, u> ⊂ B.

This is the actual generated subVOA, not an abstract presentation or a
space inferred from a proposed character. Its PCT stability is exact.

**Theorem.** The explicit U is a proper subVOA of B and is a completely
unitary, strongly rational conformal VOA of central charge 8, with

    U1 = sl2 ⊕ sl2,                 dim U1 = 6,
    Rep(U) ≃ Z(H3)                 as unitary ribbon categories,
    ch U = q^(-1/3)(1+6q+120q²+956q³+6010q⁴+...),

and its entire twelve-component character vector is the gamma=0
Evans–Gannon vector. Its diagonal unitary full theory has
c_L=c_R=8 and partition function Σ_i |chi_i|². There also exists a
unitary holomorphic extension of U isomorphic to V_(E8) for which the
all-module category is H3 and the algebra-bimodule category is
H3⊠H3^op. The latter is the category of defects preserving U in the
corresponding full E8 extension theory and contains an H3 fusion subcategory.

The chosen extension in the last sentence need not be the original
embedded H/U extension. The original extension's all-module category is
proved to be one of H2,H3; choosing the canonical H3 Lagrangian removes
that ambiguity for the existence statement.

## Proof and provenance

**0. Properness by a finite certificate with an all-weight implication.**
Every space below is a space of actual vectors in the ambient lattice VOA,
not a space defined from a proposed character. Let S2 be the exact
120-dimensional current-stable grade-two space and S3 the exact
956-dimensional grade-three space obtained from the current descendants,
translation descendants and weight-two zero products. Put

    N3 = K(-1)S2 + T S2,                         dim N3 = 634,
    P  = S3/N3,                                 dim P  = 322,
    N4 = K(-1)S3 + T S3 + S2(-1)S2,
    W4 = N4 + P4,
    N5 = K(-1)W4 + T W4 + S2(-1)S3.

Here T is translation. P4 is the actual canonical current triplet with
joint highest weights (0,2). Its construction from S2_0 S3+N4, all 18
current-zero-mode identities and all 6 direct positive-Virasoro controls
are exact. The lower closure certificate contains all 3970 prescribed
exact relations. These are finite ambient-vector calculations over
Q(sqrt(13),sqrt(-3)), with source-bound normal-word provenance.

Gate4 is the inclusion S2_0 S3⊂W4. For each of the nine independent
primitive highest weight-two fields a, the map

    f_a : P -> B4/W4,                 [p] |-> [a_0p]

is well defined because a_0N3⊂N4. Its kernel is stable under the two
commuting raising operators E_L,E_R. If known exact kernel inputs C_a
satisfy P=E_LP+E_RP+C_a, then P/ker(f_a) equals its image under a
nilpotent raising ideal, hence vanishes. Thus this is an all-input
reduction, not a sample of products.

The final Gate4 certificate authenticates 2145 original exact identities
and 118 further direct exact identities. The last 12 targets have output
weight(0,0). Twelve additional ordinary exact identities at weight(0,2)
and an exact replay of 24 raising equations prove that each remaining
class is killed by both raising operators modulo W4. In the finite
semisimple current module B4/W4, such a weight-zero class is a joint
singlet. The grade-four joint projector

    product_(j=2,4) (1-4F_L E_L/[j(j+2)])
      product_(j=2,4,...,24) (1-4F_R E_R/[j(j+2)])

therefore has the same quotient class as the original target. Twelve
complete exact projected identities place it in projected actual normal
columns. The full formal N4 is current-stable, so these columns remain
in N4; no assertion that the selected 279 columns exhaust N4 is needed.
The independent final verifier recomputes every projected residual with
an integer-cleared engine. It then replays rank 322 for all nine raising
augmentations, proving all 2898 Gate4 identities. The prime rank is used
only as a positive lower-rank witness against the independently exact
dimension 322. It is never an upper-rank estimate for an unknown space.

Gate5 is S2_0P4⊂N5. Its 24 independent current channels follow from
Jacobi and the now-complete Gate4. Zero-mode derivation and the iterate
formula give the two normal-space facts

    S2_0 N4 ⊂ N5,                    (N3)_0 S3 ⊂ N5.

For the latter, (Ta)_0=0 and

    (x(-1)a)_0p = sum_(i>=0) x(-1-i)(a_i p)
                  + sum_(i>=0) a(-1-i)(x_i p).

Gate4 and the lower controls place each inner product in its required
lower space; repeated translation commutators put every summand in N5.
No unproved P3-with-P3 product is used. If P4⊂N4, Gate5 follows already.
Otherwise Q=W4/N4 is precisely its irreducible triplet. Write
beta(a,p)=[a_0p] in Q and F(a,q)=[a_0q] modulo N5. Whenever a_0b∈N3,

    F(a,beta(b,p)) = F(b,beta(a,p)).

The eight charged highest fields a0,...,a7 have weights
(0,4),(0,8),(0,8),(0,12),(1,1),(1,5),(1,7),(1,13).
Two authenticated exact H4 identities have nonzero P4-minus coefficient:
a3_0 r3_000910 with input weight(0,-14), and a6_0 r3_000899 with
input weight(-1,-9). The checker combines saved exact lower relations
to prove a_0b∈N3 for

    (a,b) = (0,3),(1,3),(2,3),(3,6),(4,6),(5,3),(6,3),(7,3).

For each pair, a_0p has weight outside Q at that bottom input. Jacobi
therefore kills F(a,P4-minus). Raising this resulting zero with a kept
highest gives the other two triplet inputs; current covariance gives all
left descendants. No off-weight assertion about a raised p is required.

Finally, the current span C of charged brackets equals P. An independent
certificate reconstructs 28 charged seeds from the exact lower relations
and, together with 644 lowering images of rank 294, verifies rank 322.
All seeds are actual charged brackets modulo N3; affine-normal parts
contribute zero there. Because C is a full current submodule,
P=F_LP+F_RP+C and the commuting nilpotent lowering ideal imply P/C=0.
The independent replay also verifies both sl2 commutators and cross
commutators against the exact raising coordinates. Thus e_0a3 modulo
N3 is a sum of charged brackets, for the retained neutral field e.
Their zero modes on S3 are charged Jacobi commutators and lie in N5.
A second Jacobi identity with the a3 bottom witness kills e_0P4-minus;
neutral current covariance gives the triplet. The other neutral field
is omega minus the affine Sugawara stresses and e. Gate5 is complete.

The [finite strong-generation theorem](hi_cft_20260923_next_structure_recursive_strong_certificate.md)
now applies. The higher generators have actual zero-product provenance:
P3⊂S2_0S2+N3 and P4⊂S2_0S3+N4. Singular products with left input in
K or S2 close in their differential normal span by the certified gates
and lower/Virasoro controls. For a higher generator a_0b, use
(a_0b)_n c=a_0(b_n c)-b_n(a_0c) and induct on total generator weight,
then left weight; normal remainders reduce by the iterate formula.
This proves closure in all weights and strong generation by K,S2,P3,P4.
Every other generator has weight at least 2, so U1=K has dimension 6.
Since dim B1=86, **U≠B**. This proves properness of the original generated
U, not merely of an abstract algebra with selected relations.

The completed final records are
[Gate4](hi_cft_20260923_c8two_gate4_verified.json),
[Gate5](hi_cft_20260923_c8two_gate5_verified.json), and the
[independent audit](hi_cft_20260923_c8two_certificate_audit.md).

**1. Regularity and the proper branch.** These are prior audited deductions,
not additional hypotheses. The positive decomposition of omega_U into
stresses of regular affine, Potts and parafermion subalgebras proves
C2-cofiniteness and splits every epimorphism onto the vacuum. The
finite-module-category rigidity argument uses
[Etingof–Penneys, Theorem1.1](https://arxiv.org/html/2412.17681v3):
split evaluations and moderate growth give rigidity, then the projective
unit gives semisimplicity. Thus U is strongly rational even before
properness is known. See the [rationality proof](hi_cft_20260923_next_structure_rationality.md)
and [independent dependency audit](hi_cft_20260923_next_structure_final_dependency_audit.md).

With properness now proved, the exact finite-top actions and universal simple-top
bound17/10 give B=U⊕X and the actual H restriction U⊕X⊕2Y, with
h_X=h_Y=1 and top dimensions80,81. The audited rank-four exclusions,
rank-six indicator argument and center calculation force the HI(Z3)
fusion ring for F=Rep(U)_H, an untwisted Vec(Z3) invertible subcategory,
and twelve simple U-modules with the Haagerup modular data. This part
is spherical and does not assume complete unitarity. The earlier
[conditional identification](hi_cft_20260923_next_conditional_identification.md)
lists the source-bound branching and rank proofs; its old pivotal-census
step is replaced by step3 below.

The [character proof](hi_cft_20260923_next_structure_conditional_characters.md)
uses the fundamental matrix in
[Evans–Gannon, Sections1.4 and2.4](https://arxiv.org/pdf/1006.1326).
Only one additional nonvacuum pole is possible; its coefficient gamma
adds13 gamma to the vacuum current count6. Hence gamma=0. Finite-image
modular pole cancellation and absence of an invariant constant vector
prove equality of the full characters, not just the displayed coefficients.

**2. Complete unitarity.** This is the new audited deduction, detailed in
the [certificate audit](hi_cft_20260923_c8two_certificate_audit.md).
The actual strongly local U⊂H inclusion has finite net index by
[Tener, Corollary4.24](https://link.springer.com/article/10.1007/s00039-024-00685-8);
[Longo, Theorem24](https://arxiv.org/html/math/0102196) makes its subnet
completely rational. On finite-energy H, reconstructed U fields are the
original restricted fields, so its net restriction has the same actual
multiplicities1,1,2. Its boundary fusion category consequently has rank6.
The same positive spherical ring/indicator argument, with the actual
order-three lattice action and Aut(B/U)=1, gives exactly twelve net sectors.
This comparison uses actual restrictions and endomorphisms, not a presumed
VOA quantum-dimension/net-index equality.

[Henriques–Tener, Theorem9.5 and Remark9.8](https://arxiv.org/html/2507.20735v3#S9)
recover unitary U-modules from these sectors. Regularity and orthogonal
projections onto algebraic simple summands show the recovered modules
are ordinary and irreducible. Bounded intertwiners commute with closures
of the recovered fields, so this is a fully faithful linear comparison.
Twelve net simples exhaust the already known twelve VOA simples; hence
every U-module is unitarizable.

Fusion-form positivity needs a further step. Use the geometric annulus
system of [Tener2019, Definition3.18 and Corollaries3.20–3.22](https://arxiv.org/html/1810.08168#S3.SS4).
Its exponentials and localizing lifts match the geometric action in
[Henriques–Tener's integration formula5.2](https://arxiv.org/html/2506.08684#S5).
Theorem9.5(i) identifies bounded incoming insertions with the module
vertex operator; adjoints give outgoing insertions. On inverse-finite-energy
domains the matrix coefficients are finite Laurent polynomials, so
holomorphic continuation gives the same identity across the circle seam.
The common lift cancels the deck factors. Thus every module satisfies
[Tener2024, Definition2.18](https://link.springer.com/article/10.1007/s00039-024-00685-8),
and his Corollary4.6 gives complete unitarity. The domain, continuation and
lift arguments are deductions checked independently in the linked audit;
they are not quoted as a general theorem that strong unitarity implies
complete unitarity. No natural braided VOA/net tensor functor is assumed.

**3. The unitary tensor category.** By
[Gui, Theorems2.21 and2.28](https://arxiv.org/html/1908.03484#S2.SS4),
the actual unitary H/U extension is a standard commutative Q-system and
all its algebra modules are unitarizable. Giving a one-sided module its
other action through the unitary braiding realizes F as a tensor
*-subcategory of the unitary bimodule category. Thus F is C*, including
its nonlocal modules; using only local modules would give Vec and would
be incorrect here.

For this HI(Z3) category, the actual untwisted invertible subcategory
annuls Izumi's obstruction c^(0,3). The other obstruction belongs to
H¹(Z2,H²(Z3,C*))=0. Therefore
[Izumi, Definition2.7 and Theorems5.9,9.1](https://arxiv.org/html/1609.07604)
apply and give the two unitary classes H2,H3. No algebra1+rho is assumed.
[Grossman–Snyder, Theorem1.4](https://arxiv.org/html/1102.2631#S1)
places these in the same Morita class, so their centers are braided
equivalent. The positive spherical structure is unique, hence the
equivalence is ribbon. The Lagrangian-center equivalence gives
Rep(U)≃Z(F)≃Z(H3). Finally
[Reutter, Theorem5](https://arxiv.org/html/1906.09710)
makes this a unitary braided equivalence. This uses published unitary
classification theorems, not the broader computer-assisted pivotal census;
their classification equations have not been rerun in this workspace.

**4. Full theory and a specifically H3 extension.** The canonical
diagonal Longo–Rehren construction applied to the completely rational
U net gives a unitary local full theory; the sector correspondence above
identifies its character partition function with Σ_i|chi_i|².
This is the identity-coupling case of
[Rehren, Theorem1.4, Proposition1.5 and Corollary1.6](https://arxiv.org/html/math/9911149).

Transport the canonical algebra A3=I_H3(1) from Z(H3) along the unitary
ribbon equivalence. It is connected, commutative, separable, twist-free
and Lagrangian, with local-module category Vec and all-module category
H3; see [DMNO, Section4](https://arxiv.org/abs/1009.2117).
All nonvacuum U-modules have strictly positive lowest weight, so
haploidity and trivial twist give an integer-graded extension with
one-dimensional weight-zero space. The VOA extension theorem
[Huang–Kirillov–Lepowsky, Theorems3.2–3.6](https://arxiv.org/html/1406.3420)
and Gui's Q-system theorem give a unitary extension H'. It is a finite
sum of ordinary U-modules, hence C2-cofinite; local-module semisimplicity
gives rationality, and the Lagrangian property gives holomorphicity.
[Dong–Mason, Theorem1](https://msp.org/pjm/2004/213-2/pjm-v213-n2-p05-p.pdf)
then identifies this c=8 extension with V_(E8).

The canonical algebra/bimodule duality identifies its full defect category
with H3⊠H3^op; see [Müger, Sections4 and8](https://arxiv.org/abs/math/0111205).
These algebra-bimodule defects preserve the U chiral subalgebra in the
full E8 extension theory. They need not commute with the enlarged E8
chiral algebra; the local chiral H'-module category is Vec. The selection
of A3 proves existence and does not identify it with the original embedded
H/U algebra.

## Completed certificate ledger and scope

| Ingredient | Completed record | What it establishes |
|---|---|---|
| Lower controls | [lower closure](hi_cft_20260923_next_structure_lower_closure.json) |3970 exact identities|
| Actual P4 | [triplet controls](hi_cft_20260923_next_structure_p4_controls.json) |actual triplet/provenance and direct lower controls|
| Grade-three raising | [saturation](hi_cft_20260923_c8two_structure_saturation.json) |exact644 raising images, quotient dimension322|
| Additional direct H4 | [closed118 directory](hi_cft_20260923_c8two_targeted_h4_trimmed_v2/summary.json) |118 complete exact identities; later unfinished block not treated as complete|
| Raised H4 inputs | [raised12](hi_cft_20260923_c8two_structure_h4_raised_exact/summary.json) |12 additional complete ordinary identities|
| Singlet premise | [exact replay](hi_cft_20260923_c8two_h4_singlet_premise_verified.json) |all24 raising conditions replayed exactly|
| Projected H4 | [exact21-column calculation](hi_cft_20260923_c8two_h4_singlet_exact.json) |12 full characteristic-zero projected residuals|
| Full Gate4 | [independent final replay](hi_cft_20260923_c8two_gate4_verified.json) |all2898 identities by singlet recovery and raising Nakayama|
| Charged bracket span | [independent replay](hi_cft_20260923_c8two_charged_span_verified.json) |positive rank322 and current representation controls|
| Full Gate5 | [final Jacobi replay](hi_cft_20260923_c8two_gate5_verified.json) |all24 independent channels by the audited algebraic reduction|

The Gate4 final replay completed in 2.890 seconds, reported peak RSS 74828 KiB;
Gate5 completed in 1.407 seconds, peak 42672 KiB. The separate E-premise replay
completed in 3.341 seconds. Sources, exact record digests and ancestor graphs
are included in the final JSON files. Earlier interrupted or resource-refused
attempts are preserved for provenance and are not proof inputs merely because
they were run. All source-independent mathematical implications are spelled
out above and in the linked audit; the external primary theorems remain
explicit dependencies. The old conditional note is preserved as a historical
record of the previous proof boundary.

This is a computer-assisted mathematical proof, combining exact finite
certificates with the stated analytical deductions and published theorems.
It has not been formalized in a proof assistant. It establishes the explicit
construction and its identification; it does not classify or assert
uniqueness of all central-charge-eight conformal field theories.

## Comparison with the requested paper

[Albert–Honda–Kaidi–Zheng, SectionII, footnote4](https://arxiv.org/html/2512.08225v2#S2)
assumes existence of the c=8 Haagerup-center theory. The completed
construction above supplies its gamma=0 branch, a unitary diagonal
realization, and a choice of
holomorphic E8 extension carrying the H3 algebra/bimodule construction.
It therefore supplies that existence premise, with the computational,
analytic and published-theorem dependencies separated above. This is a
c=8 statement and identifies no lattice-chain continuum limit.
