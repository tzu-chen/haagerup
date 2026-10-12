# Conditional construction of the unitary c=8 Haagerup theory

23 September 2026, reopened c=8 proof window. This is a mathematical
synthesis of source-bound certificates and independently audited deductions.
It launches no computation and changes no frozen artifact. The only remaining
model-specific hypothesis in the theorem below is **properness of U in B**.
This document does not assert that the finite properness gates have finished;
their current status is recorded in the [live report](hi_cft_20260923_c8two_report.md).

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

**Theorem, conditional only on U≠B.** The explicit U is a completely
unitary, strongly rational conformal VOA of central charge8, with

    U1 = sl2 ⊕ sl2,                 dim U1 = 6,
    Rep(U) ≃ Z(H3)                 as unitary ribbon categories,
    ch U = q^(-1/3)(1+6q+120q²+956q³+6010q⁴+...),

and its entire twelve-component character vector is the gamma=0
Evans–Gannon vector. Its diagonal unitary full theory has
c_L=c_R=8 and partition function Σ_i |chi_i|². There also exists a
unitary holomorphic extension of U isomorphic to V_(E8) for which the
all-module category is H3 and the algebra-bimodule category is
H3⊠H3^op. The latter is the Haagerup defect category of the corresponding
full rational-CFT extension construction.

The chosen extension in the last sentence need not be the original
embedded H/U extension. The original extension's all-module category is
proved to be one of H2,H3; choosing the canonical H3 Lagrangian removes
that ambiguity for the existence statement.

## Proof and provenance

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

Under properness, the exact finite-top actions and universal simple-top
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
These are extension-preserving rational-CFT defects, not local chiral
H'-modules, whose category is Vec. The selection of A3 proves existence
and does not identify it with the original embedded H/U algebra.

## What remains and comparison with the requested paper

The properness implication is genuinely all-weight. The independently
audited [finite criterion](hi_cft_20260923_next_structure_h4_certificate.md)
shows that completed Gate4 and all24 independent Gate5 channels strongly
generate actual U by K,S2,P3,P4, forcing U1=K and U≠B. The raising
saturation reduces Gate4 to authenticated exact seed identities and a
spanning check in the independently known exact grade-three quotient.
Gate5 can instead follow from the new
[Jacobi reduction](hi_cft_20260923_c8two_jacobi_proof.md): two nonzero exact
bottom coefficients, eight exact lower quotient-zero identities, and
charged-bracket spanning in that same known quotient imply all its channels.
This avoids requiring a separate grade-five residual for each channel.
Every numerical ingredient must be a completed, source-bound exact identity
or a positive rank witness against an independently exact upper dimension.
Unfinished checkpoints do not discharge a premise. The saved normal
columns need not exhaust a whole normal span for a positive certificate.
Current run completion is deliberately left to
the [live report](hi_cft_20260923_c8two_report.md).

[Albert–Honda–Kaidi–Zheng, SectionII, footnote4](https://arxiv.org/html/2512.08225v2#S2)
assumes existence of the c=8 Haagerup-center theory. Under precisely the
remaining properness hypothesis, the explicit construction above supplies
its gamma=0 branch, a unitary diagonal realization, and a choice of
holomorphic E8 extension carrying the H3 algebra/bimodule construction.
Until properness is proved, this remains a conditional resolution of that
existence premise. It is a c=8 statement and identifies no lattice-chain
continuum limit.
