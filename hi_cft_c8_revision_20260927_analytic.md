# Analytic and extension revision, 27 September 2026

Owned manuscript fragment: `hi_cft_c8_manuscript_analytic.tex`.
Bibliography handoff: `c8_revision_20260927/analytic_bibitems.tex`.
This work used reading, mathematical arguments, and text editing only;
no numerical job was started by this agent.

## Result and dependency boundary

Subject to the preceding finite/algebraic inputs in the master manuscript,
the former A2 and A3 obligations now have detailed proofs.  Together they
give strong unitarity of U, all twelve net sectors with their VOA characters,
and a unitary ribbon equivalence Rep(N_U) ≃ Z(H3).  The last conclusion is
about the conformal net and does not need A1: its boundary category is
already a C*-fusion category, so the unitary Izumi classification applies
there directly.

The subsequent concrete geometric attempt resolved A1 by a pairwise
comparison; see the final section of this audit.  Complete unitarity of U,
the specified unitary ribbon structure on Rep(U), and the chosen H3 VOA
extension now follow from the stated construction inputs.  Earlier entries
below retain the development history and are superseded where they call
A1 unproved.  No blanket implication from strong unitarity to complete
unitarity has been asserted.

These are research deductions for review, not proof-assistant certificates
or a substitute for independent expert verification.  In particular, the
algebraic inputs retain the qualifications attached to their own proofs.

## A2: preserve the actual subnet

The draft previously risked transferring actual embedded extension data
through an unspecified isomorphism of net constructions.  The revision
uses separate notation for the closed smeared-field net N_V and Tener's
bounded-insertion net A_V^bl.

1. Tener's finite-index theorem applies to A_U^bl ⊂ A_H^bl.  Holomorphicity
   of the E8 ambient net and Longo's finite-index theorem imply complete
   rationality of A_U^bl.  Tener's comparison lemma transfers just this
   abstract isomorphism-invariant property to N_U.  It is not used to
   identify inclusion algebras, pointwise automorphisms, or insertion
   operators on the original Hilbert space.
2. Polynomial energy bounds inherited from the E8 lattice VOA give the
   actual Hilbert decomposition H↓U = U ⊕ X ⊕ 2Y for the smeared subnet.
   Commutation with common rotations and Fourier coefficients proves the
   converse intertwiner statement, so multiplicities and inequivalence
   remain exactly those of the algebraic branching.
3. Local irreducibility is proved from locality, strong additivity, common
   rotations, the one-dimensional vacuum energy space, and vacuum
   separation.  In particular, the two complementary interval algebras
   generate the global represented subnet by removing the endpoints.
4. Kawahigashi–Longo Proposition 2.3 is the precise finite-index theorem.
   Although its paper is titled “Case c<1,” this proposition is general:
   an irreducible local extension of a net with finitely many irreducible
   sectors, all of finite statistical dimension, has finite index.
   Those hypotheses follow from complete rationality of N_U.
5. The actual dual canonical algebra has endomorphism algebra
   C ⊕ C ⊕ M2(C).  Center induction gives rank six and a noncommutative
   complex fusion algebra.  The actual H/B lattice automorphisms embed
   Z3 into its group of invertible boundary objects, using the separately
   proved automorphism–invertible injection.
6. No assertion Aut(B/U)=1 is needed.  Six invertibles would make the
   boundary category pointed of dimension six and force the intermediate
   B/U index to be two.  Its sign involution fixes the local Virasoro net,
   hence rotations; vacuum reconstruction would give an actual VOA
   involution of B with fixed VOA U.  The structure section's
   `lem:no-sign-extension` excludes this by the weight-one Lie-rank bound.
   Thus there are exactly three invertibles.
7. The lattice intermediate extension identifies the pointed subcategory
   as untwisted Vec_Z3.  The pure categorical rank-six, indicator, and
   center calculation is then repeated for this actual net boundary
   category.  Its canonical spherical structure is positive because it
   is a C*-fusion category.  This gives twelve net sectors independently
   of the VOA modular-transformation matrix.

The explicit A2 proof uses the updated structure lemmas
`lem:automorphisms-invertibles` and `lem:no-sign-extension`.

## A3: remove finite-energy multiplicity circularity

Henriques–Tener Remark 9.8 extends Proposition 9.3 and Theorem 9.5 to the
union M of bounded spectral subspaces, allowing nondiscrete spectra and
infinite multiplicities.  Definition 9.4 makes M a common core for the
closed reconstructed smeared fields.  The partition-of-unity proof of
Corollary 9.6 still identifies the reconstructed conformal zero mode with
the actual rotation Hamiltonian on this domain.

Regularity gives an algebraic ordinary simple summand S in M.  Its own
finite-dimensional energy spaces imply that its Hilbert closure reduces
L0.  The orthogonal projection P onto that closure maps every bounded
energy subspace into a finite sum of energy spaces of S.  Thus PM ⊂ S ⊂ M
is proved before any field commutation is used.

The formal adjoint of a mode is a finite sum of modes preserving S.  This
gives mode commutation with P.  Hilbert convergence of the smeared-field
Fourier sums gives commutation on M, without claiming smeared fields
preserve M.  The new common-core graph lemma extends that equality to
the closures and their adjoints.  Its proof uses graph norm and block
decomposition; it needs no unjustified assumption that M is a core for
the adjoint.  Polar decomposition then implies reduction of the local
von Neumann algebras.  Sector irreducibility forces P=1 and M=S.

Full faithfulness is also spelled out.  A module isomorphism is shown
bounded only after comparing positive forms grade by grade, constructing
an algebraic module endomorphism, and applying simplicity to an eigenspace
from the finite-dimensional lowest-energy space.  Its unitary rescaling
then extends and intertwines closures on their actual common cores.

This proves a fully faithful **linear** *-functor.  It constructs no
tensorator and asserts no preservation of Connes fusion or braiding.
The independent counts of twelve simples give essential surjectivity
and strong unitarity only at this linear stage.

Independent in-team audit by the finite-audit agent checked HT Remark 9.8,
the common-core use, KL Proposition 2.3, and the projection argument.  Its
two requested precisions (local-to-global commutation and algebraic
form comparison before boundedness) have been incorporated.

## A1: what was resolved and what remains

The remaining comparison must match Tener's specific geometric annulus
system with the integrated Henriques–Tener system, including embedded
boundaries, paths, central lifts, and a common localizing diffeomorphism.
For an incoming annulus Tener uses U(psi) exp(-t L(rho)) U(gamma)*.
The HT integration theorem gives the natural candidate, but an exact
identification with the same lifts has not been established here.
An equality through an unspecified vacuum net isomorphism is not enough;
a vacuum normalization alone does not determine fractional-energy sector
phases.

Once this geometric match is supplied, HT Proposition 4.17 transports
localized annulus actions to sectors.  The following remaining analytical
steps are now proved rather than left as slogans:

* **Dense inverse-energy domains.** Sew an incoming annulus to the
  complementary annulus of a sufficiently small centered round disc.
  The product is lambda r^L0, with the central scalar retained.  HT
  injectivity/dense-range results then give A^-1(Mfin)=C(Mfin), which
  is dense.  No claim that this domain is an operator graph core is made.
  Applying this geometric argument to Tener's concrete A_M still depends
  on the A1 annulus-action identification.
* **Continuation.** On the two dense inverse-energy test domains, the
  algebraic insertion matrix coefficient is a finite Laurent polynomial.
  The geometric bounded insertion is holomorphic.  Every component of
  int(cl(Oin) ∪ cl(Oout)) meets Oin ∪ Oout because the omitted set is
  contained in two nowhere-dense boundaries.  The identity theorem
  extends the incoming/outgoing equalities to the whole insertion
  interior.  Equality on two dense test domains proves the unique bounded
  extension of the insertion form.  Treating an unsmeared field as a
  Hilbert-space operator at every insertion point is explicitly avoided.

HT Theorem 9.5(i), its sewing construction, and its adjoint compatibility
supply the incoming and outgoing equalities after the geometric match.
Tener Corollary 4.6 then proves fusion-form positivity, since A2/A3 first
establish strong unitarity.  The unitarizable-fusion-product hypothesis of
Tener Theorem 4.4 is not used circularly to bootstrap that property.

## Categorical and full-theory expansion

The new all-module lemma explains how the braiding turns a right module
over a connected commutative Q-system into a bimodule, why its relative
tensor product remains in this full subcategory, and how Gui's results
give a C*-tensor structure.  Locality is a further monodromy condition
and is not imposed on the Haagerup boundary category.

The Izumi application now states the two vanishing group-cohomology
obstructions and the trivial G/2G quotient for G=Z3.  It uses the
published unitary classification; it does not claim an independent
replay of the classification equations or an all-pivotal census.
Applying the same argument to the already unitary net boundary gives
`cor:analytic-net-haagerup` independently of A1.

The chosen H3 VOA extension proof specifies the transported positive
Q-system structure.  It verifies CFT type and C2-cofiniteness, the latter
using ABD Proposition 5.2 on each ordinary U-summand and the inclusion
C2^U(H') ⊂ C2(H').  HKL and Gui supply extension/module/unitarity results;
Dong–Mason then identifies the resulting holomorphic c=8 VOA with E8.
The all-module category has six simples, while the full bimodule defect
category has 36, indexed by pairs in H3 × H3^op.  The opposite comes from
composition of the right tensor action.  These defects preserve U; they
are not asserted to preserve the enlarged E8 chiral algebra.

The diagonal Longo–Rehren full **net** theory uses complete rationality
and the linear sector/character identification.  It therefore needs no
A1, even though the selected H3 **VOA** extension does.

## Primary sources and precise locations

All manuscript source hyperlinks have been converted to bibliography
citations; the handoff file supplies journal data, DOI/arXiv links, and
version pinning.  Principal locations checked are:

| Key | Source and locations used |
|---|---|
| TenFields | Tener, *Representation theory…*, Selecta Math. 25 (2019), 76: Definitions 3.16, 3.18; Corollaries 3.20–3.22; Proposition 5.5; Theorem 5.6; Proposition 7.5; Lemma 7.6. https://arxiv.org/abs/1810.08168v2 |
| TenFusion | Tener, *Fusion and positivity…*, GAFA 34 (2024), 1226–1296: Definition 2.18; Theorem 4.4; Corollaries 4.6, 4.24. Published/v3 numbering. https://arxiv.org/abs/1910.08257v3 |
| HTNet | Henriques–Tener, *Every conformal net…*, arXiv **2507.20735v3**, 10 October 2025: Lemma 4.15; Proposition 4.17; Section 6.2; Proposition 6.19; Lemma 7.9; Theorem 8.9; Definition 9.4; Theorem 9.5; Corollaries 9.6–9.7; Remark 9.8. https://arxiv.org/abs/2507.20735v3 |
| HTAnn | Henriques–Tener, *Integrating positive energy…*, 2025: Theorem 5.5 and formula (5.2). https://arxiv.org/abs/2506.08684 |
| Longo | *Conformal subnets and intermediate subfactors*, CMP 237 (2003), 7–30: Theorem 24. https://arxiv.org/abs/math/0102196 |
| KL | Kawahigashi–Longo, *Classification of local conformal nets. Case c<1*, Annals 160 (2004), 493–522: Proposition 2.3, p.504. https://annals.math.princeton.edu/wp-content/uploads/annals-v160-n2-p04.pdf |
| Gui | *Q-systems and extensions…*, IMRN 2022 no.10, 7550–7614: Theorems 2.21, 2.28, 3.13. https://arxiv.org/abs/1908.03484v3 |
| Izumi | *The classification of 3^n subfactors…*, Quantum Topol.9 (2018), 473–562: Definition 2.7; Theorems 5.9, 9.1. https://arxiv.org/abs/1609.07604v2 |
| GS | Grossman–Snyder, *Quantum subgroups…*, CMP311 (2012), 617–643: Theorem 1.4. https://arxiv.org/abs/1102.2631v2 |
| Reutter | *Uniqueness of unitary structure…*, CMP397 (2023), 37–52: Theorem 5. https://arxiv.org/abs/1906.09710 |
| DMNO | *The Witt group…*, Crelle677 (2013), 135–177: Section 3.3; Corollary 4.1; Proposition 4.4. https://arxiv.org/abs/1009.2117v2 |
| HKL | Huang–Kirillov–Lepowsky, *Braided tensor categories and extensions…*, CMP337 (2015), 1143–1159: Theorems 3.2–3.6. https://arxiv.org/abs/1406.3420 |
| ABD | Abe–Buhl–Dong, *Rationality, regularity, and C2-cofiniteness*, Trans.AMS356 (2004), 3391–3402: Proposition 5.2. https://arxiv.org/abs/math/0204021 |
| DM | Dong–Mason, *Holomorphic vertex operator algebras of small central charge*, Pacific213 (2004), 253–266: Theorem 1. https://arxiv.org/abs/math/0203005 |
| Rehren | *Canonical tensor product subfactors*, CMP211 (2000), 395–406: Theorem 1.4; Proposition 1.5; Corollary 1.6. https://arxiv.org/abs/math/9911149v2 |
| Mueger | *From subfactors to categories and topology II*, JPAA180 (2003), 159–219: Sections 4 and 8. https://arxiv.org/abs/math/0111205 |

The strengthened main theorem must keep the conformal-net conclusion
separate from the A1-dependent VOA complete-unitarity conclusion.

## Final review additions

The finite-audit agent independently verified the index-two bridge and
provided the sharper CKLW references now used directly: Theorem 6.9
lifts the actual B-net automorphism to a unitary VOA automorphism;
Proposition 7.6 identifies fixed-point nets; Theorem 7.5 gives injectivity
of the unitary-subalgebra/subnet correspondence.  Hence the fixed VOA is
exactly U.  This avoids both A1 and any appeal to a new reconstruction
functor's tensor properties.

`cor:analytic-net-extension` now constructs, independently of A1, the
holomorphic local conformal-net extension E3 of N_U obtained from the
canonical H3 Q-system.  It records irreducibility, index 3(1+d²), central
charge eight, boundary category H3, and the 36-object bimodule category.
The precise reconstruction source is Longo–Rehren, *Nets of subfactors*,
Rev.Math.Phys.7 (1995), 567–597, Theorem 4.9:
https://arxiv.org/html/hep-th/9411077v2.  That theorem explicitly gives
irreducibility from multiplicity one, index equal to statistical
dimension, and locality from the commutativity equation.  Bischoff's
Section 2.6 recalls the correspondence in the conformal-net setting:
https://arxiv.org/html/1803.04949.  The bibliography handoff now also has
keys `LRNets` and `BisTY`.

The new net E3 is deliberately not identified with the E8 lattice net.
The primary net reference just cited explicitly describes uniqueness of
the holomorphic c=8 net as a conjecture in its Section 6.1; no newer
classification theorem establishing it was found in this audit.  The
manuscript does not turn that historical status into an unsupported
claim about all current literature, and uses no such classification.
Dong–Mason classifies VOAs under its hypotheses, not arbitrary nets.

Independent review of the structure fragment found no circularity in
the positive-stress → projective vacuum → strong-rationality argument.
In particular, Etingof–Penneys arXiv:2412.17681v3 Theorem 1.1 has exactly
the non-negligibility and moderate-growth hypotheses proved in the
draft.  The finite-abelian right-exact tensor estimate is enough before
rigidity is known.  A suggested simplification removes an unnecessary
global orthogonal-decomposition claim from the C2 argument by working
inside each finite-dimensional ambient grade.  The top-bound trace
argument uses complete Zhu tops and finite-dimensional sl2 characters
and does not require prior unitarity of the unknown U-module.  Its
actual embedded-field and spectral-witness premises remain R1/R2 inputs.

## Final bounded search for an A1 bypass

The search was updated through 27 September 2026.  It found no theorem
whose verified hypotheses turn the present A2/A3 conclusions into A1
or into positivity of the canonical VOA fusion forms.  This is a
statement about the sources checked, not a claim that no such theorem
could exist.  The manuscript's conditional conclusion is unchanged.

| Primary source | Relevant theorem and applicability |
|---|---|
| Gui, *Comparison of Extensions of Unitary Vertex Operator Algebras and Conformal Nets*, [arXiv:2505.03235v3](https://arxiv.org/html/2505.03235v3), 18 February 2026 | Definition 4.15 assumes complete unitarity and charged-intertwiner energy bounds/strong intertwining in Condition II. Remark 4.18 identifies it with the older Condition B; the apparent weakening to strong unitarity still retains charged-field hypotheses. Theorem 6.11 compares actual extension Q-systems only over a base satisfying Condition II. Theorems 6.14 and 6.18 retain this condition while transferring sector surjectivity and extension properties. Theorem 4.20(2) transfers the condition to a regular **coset**, not an arbitrary subVOA. Here U is a conformal subVOA of H: its coset is the vacuum VOA and its double commutant is H, so this does not recover U. |
| Gui, *Unbounded field operators in categorical extensions of conformal nets*, [arXiv:2001.03095](https://arxiv.org/html/2001.03095), published in Invent. Math. 244 (2026), 899–965 | Condition A in Section 3.4 asks for strong unitarity and, on a tensor-generating family of modules, energy bounds and strong intertwining for charged fields. Theorem 3.15 then proves complete unitarity. Strong integrability of module vertex operators is a separate conclusion of Theorem 3.16, not a substitute for Condition A. Theorem 3.34 requires the double-commutant property for both members of a coset pair. These charged-field or double-commutant hypotheses have not been proved here. |
| Henriques–Tener, *A genus zero functorial CFT associated to the vacuum sector of a conformal net*, [arXiv:2608.24437](https://arxiv.org/html/2608.24437), 25 August 2026 | Theorem A/Theorem 3.6 constructs bounded vacuum multidisc operators; Theorem B/Theorem 4.1 proves vacuum trace-class and finite energy multiplicities. Appendix A compares vacuum point and interval insertions. These results do not state the needed identification of Tener's module insertion operators and their central/path lifts. The introduction's reference to operators subsumed from Tener's earlier work concerns *Geometric realization of algebraic conformal field theories* (Adv. Math. 349 (2019)), not the module compatibility statement used here. |
| Gui, *Geometric positivity of the fusion products of unitary vertex operator algebra modules*, [arXiv:2306.11856](https://arxiv.org/html/2306.11856), CMP405 (2024), article72 | Corollary 8.4 identifies geometric and algebraic positivity when the fusion module is unitarizable. Theorem 8.6 proves positivity when that fusion product is irreducible. The present nonpointed category has reducible fusion products, so this does not establish complete unitarity for all pairs. |

The abstract of Gui's [arXiv:2606.30928](https://arxiv.org/abs/2606.30928),
*Minkowskian open/closed conformal field theory possibly without vacuum:
the Cardy case* (29 June 2026), was also checked.  Its construction starts
from a conformal net and concerns Cardy-type full net theories; it does
not assert the missing VOA/net charged-field or annulus comparison.

The precise distinction is between three statements: unitary Hilbert
structures on all ordinary U-modules (proved in A3), a positive tensor
structure on an abstractly equivalent category, and positivity of the
**canonical** Hermitian forms on VOA intertwining spaces.  A3 supplies
a linear star-equivalence, not a tensorator or a comparison of those
forms.  Abstract transport of a tensor structure does not itself
identify the transported form with the canonical VOA form.  No checked
source gives a converse that removes this distinction under our current
hypotheses.

A minimal sufficient future proof target is the following concrete
geometric comparison.  For every incoming/outgoing annulus pair in
Tener's specified system, construct the corresponding centrally
extended Henriques–Tener annuli with the same embedded boundaries,
boundary parametrizations, paths, and common localizing diffeomorphism.
Prove equality of their vacuum actions with the products
U(psi) exp(-t L(rho)) U(gamma)* and equality of their vacuum point
insertions with the bounded extension of B Y(v,z) A.  The comparison
must preserve the universal path lift, not merely a vacuum scalar:
fractional lowest weights can distinguish these lifts in other sectors.
Once this is established, the manuscript already supplies the remaining
argument: local transport to each sector, dense inverse-energy test
domains, incoming/outgoing insertion identities, and holomorphic
continuation.  Tener's positivity theorem then applies.  An alternative
target is Gui's Condition A for a finite tensor-generating family; that
requires estimates and strong commutation for charged intertwining
operators, which the current reconstruction of module vertex operators
does not supply.

The manuscript now includes a concise paragraph stating the strongest
recent comparison results, their precise unmet hypotheses, and the
remaining geometric target.  The bibliography handoff adds
`GuiCompare` and `HTGenusZero`, pinned respectively to v3 and v1.

The A2 untwistedness argument was also expanded: the diagonal and
antidiagonal isotropic lines in the actual B metric group are
transverse; free induction from the antidiagonal Tannakian category is
fully faithful by adjunction and exhaustive by the target dimension
three.  Its tensor equivalence with all H/B modules, followed by the
intermediate-algebra embedding, proves the actual pointed boundary
subcategory has trivial associator class.  The group of invertibles
alone was not used to infer untwistedness.

## Final concrete proof of A1: superseding the search-only assessment

A further bounded mathematical attempt, jointly checked against the
primary statements by the root and structure agents, found that the
previous target was unnecessarily strong.  A global canonical choice of
individual annulus lifts is not needed.  The manuscript now proves
`clm:analytic-annulus` as a pairwise compatibility proposition.

For an incoming semigroup annulus, the explicit framing
h(theta,s)=phi_(t-s)(exp(i theta)) has logarithmic velocity
i rho(exp(i theta)) partial_theta.  HTAnn's integration therefore gives
exactly exp(-t L(rho)); thin factors give Tener's boundary
reparametrizations.  This establishes the actual geometric operator,
including its scalar, rather than invoking a generic vacuum-net
isomorphism.

For a pair choose the common localizer delta.  First choose the lifts of
delta A and delta tilde-A **inside the canonical localized extension**,
whose remaining ambiguity is C*; normalize their nonzero vacuum
operators.  Only then undo the same universal delta lift on both sides.
The product is canonically localized, and its module actions are exactly
Tener's paired formula (5.2).  Changing the common deck lift conjugates
the insertion by exp(2 pi i L0), which commutes with the integer-weight
VOA modes.  This is valid also at fractional module lowest weights;
vacuum scalar normalization alone was not used to fix a deck lift.

HTNet Lemma 6.8 supplies locality and exact sector transport of the
geometric point insertion.  Sewing, Theorem 9.5(i), the adjoint formula,
and the two domain/continuation lemmas identify it with the bounded
VOA insertion form.  Round factorization now explicitly proves both
finite-energy range inclusion and density of the inverse-energy domain,
as required by Tener Definition 4.2.  The argument is repeated over all
compatible geometric representatives; the union prescription in
Tener's proof of Theorem 4.28 supplies the full insertion interior and
uniqueness of the bounded form makes overlaps agree.  The empty-interior
BA generators are treated separately by local annulus transport.

Consequently every bounded-insertion generator lies in the smeared-field
net.  Both nets act on the same vacuum Hilbert space.  Haag duality of
the bounded-insertion net and locality of the smeared-field net give
A_BL(I) ⊂ N_U(I) ⊂ A_BL(I')' = A_BL(I), proving concrete equality.
All formerly A1-conditional analytic conclusions were updated to
theorems under the ordinary construction inputs.  The distinction
between all modules and local modules, and between the original and
chosen H3 extensions, remains unchanged.  The proof does not assert
that the particular linear reconstruction functor preserves tensor
products or braiding.

This final proof supersedes the earlier audit entries saying A1 remains
open.  The search-only assessment correctly found no ready-made theorem
with exactly the claimed conclusion; the new conclusion follows from
the explicit pairwise construction and the verified source chain.

Exact source dependencies of the completed A1 proof:

- `TenFields`: Definition 3.16; Lemma 3.19; Corollaries 3.20–3.22;
  Definition 4.2; Proposition 4.13; proof of Theorem 4.28;
  Section 5.1 formula (5.2) and Remark 5.2.
- `HTAnn`: Remark 4.2; formula (5.2); Theorem 5.5; Section 7 and
  Theorem 7.4.  The localized extension is selected before its scalar
  normalization, so no vacuum-only normalization of a Z fiber is used.
- `HTNet` v3: Lemmas 4.15, 6.8 and 7.9; Proposition 4.17;
  Section 6.2 formula (76); Corollary 6.15; Proposition 6.19 and
  formula (81); Theorems 8.9 and 9.5(i).
- `TenFusion` v3/published numbering: Definition 2.18, Theorem 4.4,
  and Corollary 4.6, applied after the separately established strong
  unitarity.  Neither Gui's charged-field Condition II nor the newer
  vacuum multidisc theorem is needed for this deduction.

The root and finite-audit agents subsequently read the complete written
proof against these primary statements and reported no gap.  Their
suggested precisions are incorporated: explicit scalar-versus-vector
notation in the framing calculation; a universal localizer lift
projecting to the **fixed central lift** used in its vacuum unitary;
both range and density; full representative-union coverage; and the
empty-interior generators.  This is internal mathematical review, not
external expert validation or a machine-checked proof.  The finite
construction hypotheses in the master manuscript remain explicit.
