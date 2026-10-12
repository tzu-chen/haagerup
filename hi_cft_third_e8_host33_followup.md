# Host33 after the rank-two restriction lemma

**Later update.** The [universal flavoured-character bound](hi_cft_third_flavoured_universal_obstruction.md)
now excludes A1_60 directly: every A1 factor in the six-current
character has level at most39, and the rank-three radical strengthens
the necessary level set further. This bypasses the coset-rationality
question below; it does not prove that rationality statement.

The next six-current value in the earlier saved near-two catalog was c=65/31,
with full currents A1_60 plus a rank-three torus. The ambient residual
is the principal coset

    C=Com(A1_60,D5_1).

This note records what the new induction lemma adds and what it does
not settle. The original exact fermion branching and double-commutant
proof are in the [principal-coset note](hi_cft_sixhour_d5_principal_coset.md).

## 1. Low-grade vacuum dimensions do not exclude the host

The six affine/Heisenberg currents have no affine integrability null
through grade three. Their vacuum PBW character begins

    1+6q+27q^2+98q^3.

The ambient C has two independent commuting stress tensors, of charges
1/2 and99/62, and its exact vacuum coefficients through grade six are

    1+2q^2+2q^3+5q^4+7q^5+15q^6.

Even retaining both stresses would only give weight-two lower bound29
for the product with the current vacuum. The fixed-character target is
120. At weight three the corresponding product lower bound is112,
against956. Thus the elementary current-vacuum/commutant character bound
is much too weak here. These numbers do not imply that the fixed
commutant actually retains both ambient stresses.

## 2. What the universal restriction lemma requires here

Let D0=Com(H,W), where H is the actual rational current/lattice frame
inside W, and let D_B=Com(H,B). The inherited alpha fixes the whole
ambient C uniformly in this host. Here is the group-level argument.

The principal A1 centralizer in E8 has Lie algebra B3 and rank three,
as certified in the embedding catalog. The radical currents form a
maximal torus there, hence are conjugate inside its connected group
to the A3 Cartan in the regular D5 times A3 embedding. Centralizing
that torus places alpha in the connected image of Spin10 times
T_A3: the roots perpendicular to it are precisely D5. We use
connectedness of torus centralizers, as in
[Knapp, Section3](https://www.math.stonybrook.edu/~aknapp/pdf-files/1-27.pdf).

The Spin10 component must commute with the principal SU2. A finite
central quotient does not change this, since its commutator with the
connected SU2 is constantly one. On the vector10=spin4 plus spin0,
the orthogonal centralizer is just plus/minus I10: its two real
irreducible blocks have scalar signs, and determinant one equates
them. The preimage is the center C4 of Spin10. The regular D5+A3
glue identifies the two centers by a graph of order four, so this
central component is absorbed into T_A3. Therefore every pointwise-H
automorphism acts through that torus and fixes the full D5 VOA.
In particular D_B=C for every simultaneous alpha in the host class.

The [rank-two restriction lemma](hi_cft_third_e8_rank_two_restriction.md)
would give D_B=D0 or an index-I proper residual inclusion, once the
finite rational-frame and residual VOA/net bridge holds. Unlike the
already identified lattice and parafermion hosts, rationality of C
has not independently been proved. Its C2-cofiniteness is still an
open input in the saved principal-coset analysis. The new lemma must
not be used to silently supply that missing hypothesis.

If D0 is strongly rational and its finite-index unitary extension to
C supplies the stated VOA/net representation bridge, then C is
strongly rational as well. Under that conditional premise, Section3
identifies its full modular category rather than merely postulating a
canonical GKO completion.

## 3. Conditional exact modular-category identification

The existing fermion proof determines

    Com(C,D5_1)=U'=A1_60(0) direct sum A1_60(60).

This is the bosonic order-two simple-current extension. In the regular
E8 extension of D5_1 tensor A3_1, no nonvacuum D5 glue branch can have
zero C energy. Indeed the only integral differences between numerator
weights 0,1/2,5/8,5/8 and SU2_60 weights ell(ell+2)/248 are

    (vacuum,ell=0 or60),   (spinor or conjugate spinor,ell=29).

The odd label29 is absent because the principal SU2 center acts
trivially on all four D5_1 modules; the fermion representation has
integer spins. Hence

    Com(C,E8)=U' tensor A3_1=:A.                         (1)

Conversely Com(A,E8)=C because A contains U' tensor A3_1 and the
original current-vacuum selection gives C. Thus A,C are an actual
normal pair, with A strongly rational independently of C.

Assume now that C is strongly rational. By
[McRae, Theorem1.1](https://arxiv.org/pdf/2107.06577), the modules of A
and C occurring in E8 form braid-reversed equivalent fusion
subcategories, and E8 is their multiplicity-free graph extension.
Let their common global dimension be d. The extension algebra has
dimension d. Holomorphicity of E8 gives

    d^2=Dim Rep(A) Dim Rep(C).

Since each displayed subcategory is contained in its full category,
d is at most each factor on the right. Equality of their product
forces both full categories to equal the corresponding subcategory.
Consequently

    Rep(C) is braid-reversed equivalent to Rep(U' tensor A3_1).
                                                               (2)

This identifies the category under the rationality premise; it does
not additionally assume a canonical field-identification prescription.
Its pointed group is C4, since the SU2_60 local simple-current
condensation has no nonvacuum invertible objects. The global dimension
has algebraic norm supported only at primes2 and31, as established in
the previous principal-coset note.

Therefore a rational full-CFT completion retaining C cannot have a
faithful order-three symmetry acting trivially on its chiral VOA:
an invertible order-three defect in any Morita-equivalent full-CFT
category would force division of its global dimension by3 to be an
algebraic integer, contradicting that norm. This improves the old
conditional ambient-model test, but it does not exclude an unknown
smaller fixed chiral algebra D0 carrying the residual hypergroup.

## 4. Remaining question

The subsequent [SO3 module-category obstruction](hi_cft_third_e8_host33_category_obstruction.md)
excludes every proper rank-two quotient on the category in(2), using
the complete unitary SO3_30 module-category classification and a
closed pointed subcategory. Thus the categorical obstruction is now
available conditional on the modular-category identification.
The rationality/finite-frame bridge remains the necessary input before
an unconditional host33 status change. The simultaneous-alpha domain
is fixed by Section2. No independent current-weight character
contradiction has been found.

The current primary rationality theorem does not remove this condition:
[McRae, Main Theorem5](https://arxiv.org/abs/2108.01898), including the
January2026 revision, proves strong rationality of a normal coset of
strongly rational VOAs **provided that the coset is C2-cofinite**.
The principal embedding here is not a diagonal affine or Cartan
parafermion coset covered by their standard rationality theorems.
A bounded primary-source search found no theorem establishing its
C2-cofiniteness. This is a missing proof in this analysis, not a claim
that the coset is nonrational. No new computation was run.
