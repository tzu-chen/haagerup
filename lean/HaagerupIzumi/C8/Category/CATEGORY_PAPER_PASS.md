# Categorical arguments: paper pass (`L_untwisted`, net count, all-module lemma, pivotal uniqueness)

Source: `c8_expanded_20260929/haagerup_c8_expanded.tex`.

* The untwisted pointed part and free-module induction: lines 3327–3352, in "The rank-four or
  rank-six alternative".
* The net version: lines 4383–4406, in `clm:analytic-net-count`.
* `lem:analytic-unitary-all-modules`: lines 4900–4934.
* The pivotal-uniqueness paragraph of `prop:optional-algebraic-identification`: lines
  4109–4116.
* The rank-six ring step: lines 3794–3823 (briefly).

Lean: `lean/HaagerupIzumi/C8/Category/` (and `Fusion/` for §5).  Every file compiles, and the
only axioms are `propext`, `Classical.choice`, `Quot.sound`.  The end result is
`untwisted_vec_equivalence_of_separable` (`UntwistedVecEquivalence.lean`):
* `𝒞_{H/B}` (all right `H/B`-modules, realized as `H/B`-bimodules through the braiding) is
  monoidally equivalent to the untwisted `Vec_{ℤ/3}`;
* the functor is `X ↦ (⊕_i S(deg i, −deg i)) ⊗ (H/B)`;
* the leg `Vec_{ℤ/3} ≃ add(L₋)` is braided (`Lminus_vec_braided_equivalence`).

The count `9/3 = 3` is `netCount_simple_modules_of_separable`.  The pivotal statement is
`Fusion.IsHIRing.subsingleton_pivotalStructure` (`Pivotal.lean`).

**Verdict.**  The arguments are correct.
* Some inputs are used without being stated or justified:
  - that the quadratic form of line 3327 is the self-braiding of `Rep(B)` (G1; G2 is moot under
    that reading);
  - the nonvanishing of the homogeneous components of the multiplication of `H/B`, an unstated
    standard fact (G4);
  - where the separability of `H/B` comes from (G5).
* One step needs a decomposition argument that is not stated (G6).
* Shorter arguments emerged in several places:
  - Eilenberg–Mac Lane instead of Tannakian reconstruction (G3);
  - the count without the dimension formula (G7);
  - the split coequalizer (H1);
  - the universal grading group for pivotal uniqueness (P1);
  - a character count replacing the direct-ideal argument in the rank-six step (R1).

## 1. Setting actually used

`C = Rep(B)` is a braided, `ℂ`-linear category with finite biproducts and linear tensor
product.  The inputs are:

* the nine invertibles `S v`, `v ∈ (ℤ/3)²`, with
  - `dim Hom(S v, S w) = δ_{v,w}` (`hSchur`);
  - `S v ⊗ S w ≅ S(v + w)` (`hfusion`);
  - `S(0,0) ≅ 𝟙` (`hunitS`);
  - every object a finite sum of the `S v` (`hss`);
* `A = H/B` commutative, with
  - `A ≅ ⊕_{c∈ℤ/3} S(c,c)` as an object (`hA`, the support on `L₊`);
  - a separability section `sep : A → A ⊗ A`, an `A`-bimodule section of the multiplication
    (`hS`);
* idempotents split in `C` (`IsIdempotentComplete C`; true for `Rep(B)`, which is abelian);
* **external**: `hθ`, the self-braiding `c_{x,x}` is the identity for `x ∈ L₋` (G1).

The formalized end result (`untwisted_vec_equivalence_of_separable`) also assumes:
* `HasCoequalizers C`, and `X ⊗ −`, `− ⊗ X` preserving colimits.  These are the typeclass
  hypotheses of Mathlib's relative tensor product of bimodules (`Bimod.tensorBimod`), on which
  the monoidal structure of `𝒞_A` rests.
* `(3 : 𝕜) ≠ 0`, finite-dimensional Hom spaces, and `A` commutative (`IsCommMonObj`).

No dimension theory, no Tannakian reconstruction and no semisimplicity of `𝒞_A` are used.

## 2. Untwisted pointed part and free induction (3327–3352), net version (4383–4406)

**G1 (gap: missing justification; 3327–3335, 4383–4389).**
* Line 3327 says "the local `B`-module category has metric group `(ℤ/3)², q`".
* Read as a braided statement with the DGNO convention, the quadratic form of a pointed braided
  category is the self-braiding: `q(x) = c_{x,x}`.  Then the isotropy of `L₋`,
  `q(a,−a) = a² ≡ 0` (3331–3333), gives `c_{x,x} = 1` for `x ∈ L₋` directly.  That is exactly
  what the argument uses.
* What is missing is a justification of that identification.  The braided quadratic form must
  be identified with the lattice discriminant form `q(a,b) = (2a²+b²)/3`.
* Line 4383 ("the lattice net `𝒩_B` has discriminant metric group") supports the lattice
  reading, so the paper is ambiguous.
* The identification follows from either of:
  - Huang's ribbon structure `θ = e^{2πiL₀}`, with `h_{λ+L} ≡ q(λ)` mod 1 and `θ_x = c_{x,x}`
    for `d_x = 1`;
  - more directly, the Dong–Lepowsky braiding `e^{πi(λ,μ)}` on the simple currents of the
    lattice VOA `B`.
* In Lean this is the one external hypothesis `hθ` (`c_{x,x} = id` on `L₋`).  The isotropy
  itself is `Weights.Lminus_symmetric_trivial_twists` (`Data/Weights.lean`).
* **Fix:** at 3327, add "(the quadratic form of the braiding, `q(x) = c_{x,x}` on simple
  currents; it is the discriminant form by the Dong–Lepowsky braiding `e^{πi(λ,μ)}`,
  equivalently by Huang's `θ = e^{2πiL₀}` with `h_{λ+L} ≡ q(λ)`)".

**G2 (moot under the DGNO reading of 3327; 3335).**
* With `q(x) = c_{x,x}` (G1), no step from twists to self-braidings is needed.
* Under the twist reading, "trivial twists" gives trivial self-braidings only because, for an
  invertible `x`, `c_{x,x} = d_x^{-1} θ_x · id` with `d_x = 1`.
* Here `d_x² = 1` uses sphericality (the paper has a positive spherical structure, line 3259).
  Then `d_x³ = d_{x³} = 1` forces `d_x = 1`.

**G3 (suggestion; 3335–3337 "hence Tannakian; as a tensor category it is the untwisted
`Vec_{ℤ/3}`", and 4388–4389).**
* The pointed braided subcategory is `Vec_{ℤ/3}^{(ω,c)}` for an abelian 3-cocycle.
* By Eilenberg–Mac Lane, its class is determined by the quadratic form `x ↦ c(x,x)` (EGNO §8.4,
  Joyal–Street).  With `c(x,x) = 1`, the pair `(ω, c)` is a coboundary.
* So the subcategory is *braided* equivalent to `Vec_{ℤ/3}` with trivial associator and trivial
  (symmetric) braiding.
* This avoids Deligne's theorem.  It gives the braided statement, not only the tensor one.
  Symmetry need not be checked separately, since the monodromy is the bilinear form of `q`.
* For `ℤ/3` the needed direction is elementary.  In Lean:
  - `AbelianCocycle.isTrivial_of_trace_eq_one`;
  - the scalars come from `pentagon_scalar` and `hexagon_forward_scalar` /
    `hexagon_reverse_scalar` (`PointedCocycle.lean`);
  - then `Lminus_untwisted_symmetric` and `Lminus_braided_vec`.
* Two normalizations are implicit in "as a tensor category":
  - the chosen `x_a ⊗ x_b ≅ x_{a+b}` give a normalized cocycle only after a coboundary
    (`normalizedCocycle`);
  - the unit isomorphism `x_0 ≅ 𝟙` must be rescaled by the common left/right unit scalar
    (`lsc_eq_rsc`, `unitScalar`).

  Both are standard, but worth "(after normalizing)".
* **Fix:** "Its quadratic form `x ↦ c_{x,x}` is trivial (G1).  By Eilenberg–Mac Lane the abelian
  cohomology class of the pointed subcategory on `L₋` is trivial, so it is braided equivalent to
  `Vec_{ℤ/3}` with trivial associator and symmetric braiding."

**G4 (unstated standard fact; 3345–3346 "Every free module is a direct sum of these three simple
modules").**
* A free module on a general object of `Rep(B)` is `X ⊗ (H/B)` with `X = ⊕ S(v)`.
* Reducing `S(v) ⊗ (H/B)` to `S(ℓ₋(v)) ⊗ (H/B)`, with `ℓ₋(v)` the `L₋`-component of `v`,
  needs `S(c,c) ⊗ (H/B) ≅ H/B` as right modules.  Equivalently, `H/B` is a twisted group
  algebra of `L₊`: every homogeneous component `(c,c) ⊗ (d,d) → (c+d,c+d)` of the
  multiplication is nonzero.
* The paper does not state this.  It is standard for simple-current extensions (Dong–Mason; Li).
  It also has a short proof that uses separability but no traces or dimensions.  The Lean proof is in three steps:
  - The unit of `H/B` lies in degree 0, by Schur and `S(0,0) ≅ 𝟙` (`hunit_of_unitS`).
  - Suppose `(d,d)(−d,−d) = 0 = (−d,−d)(d,d)` for some `d ≠ 0`.
    - Write `sep(1) = σ = Σ σ_{c,e}`.
    - Bimodule linearity gives `xσ = σx` for `x ∈ (d,d)`.  Comparing `(d,0)`-components forces
      `σ_{0,0} = 0`.
    - Then the degree-0 part of `m(σ) = 1` is zero, which is absurd
      (`mulComp_pairing_ne_zero_of_separable`, `NondegFromSeparable.lean`).
  - Associativity propagates `(d,d)(−d,−d) ≠ 0` and the unit to all pairs
    (`mulComp_ne_zero_of_unit_of_nondegenerate`, `TwistedGroupAlgebraOfUnit.lean`).
* **Fix:** before "Every free module …", insert: "The homogeneous components of the
  multiplication of `H/B ≅ ⊕_c (c,c)` are nonzero.  If `(d,d)·(−d,−d)` vanished in both orders,
  bimodule linearity of the separability section would kill its `(0,0)` component and hence
  the unit.  Thus `(c,c) ⊗ (H/B) ≅ H/B` as right modules, and every free module is a sum of
  the three modules `x ⊗ (H/B)`, `x ∈ L₋`."

**G5 (gap; 3346 "separability makes every module a summand of a free module").**
* The separability of `H/B` in `Rep(B)` is not stated or cited.
* It holds because `H/B` is a connected commutative algebra with trivial twist (a VOA
  extension, Huang–Kirillov–Lepowsky) of dimension `3 ≠ 0` in a fusion category, hence étale
  (Kirillov–Ostrik; DMNO §3).
* In the net version, `Q₊` is a Q-system, hence special Frobenius.
* The source matters.  The obvious section of a twisted group algebra,
  `σ = (1/3) Σ_c e_c ⊗ e_c^{-1}` (`twistedSeparabilitySection`), presupposes the nonvanishing
  in G4.  So it cannot be used to prove G4.  In Lean the section is the hypothesis `hS`.
* **Fix:** add "(`H/B` is a connected étale algebra in `Rep(B)` [HKL, KO], hence separable)".

**G6 (imprecision; 3346–3348 "a summand of a free module.  Thus induction identifies …").**
* Passing from "summand of `⊕ F_a`" to "isomorphic to a sub-sum of the `F_a`" needs an argument
  that is not stated.
* **Simplest patch:** `End F_a = ℂ` is local, so Krull–Schmidt–Azumaya shows that every summand
  of `⊕ F_a` is isomorphic to a sub-sum.  No semisimplicity of `𝒞_A` is needed.
* Semisimplicity of `𝒞_A`, which the paper proves only later (4926), would also do.
* The Lean route uses only `Rep(B)`:
  - by full faithfulness on `L₋`, an idempotent of a free module on a sum of `L₋`-invertibles
    is induced from an idempotent in `Rep(B)`;
  - that idempotent splits there, since `Rep(B)` is abelian, through a sub-sum of
    `L₋`-invertibles by Schur (`hsplit_of_isIdempotentComplete`, `LminusSplitting.lean`).
* **Fix:** add "(by Krull–Schmidt–Azumaya, since `End(x ⊗ (H/B)) = ℂ` is local)".

**G7 (suggestion; 4400–4402 "The target has dimension `9/3 = 3`, so these three distinct
invertible images exhaust its simple objects").**
* This is correct.  It uses `Dim 𝒞_A = Dim 𝒞 / dim A` for a connected étale `A` (DMNO,
  Lemma 3.11) together with semisimplicity, and neither is cited here.
* The VOA passage (3345–3348) proves the same statement by a different argument.
* With G4–G6 the VOA argument needs no dimension theory, and Lean uses it for both passages
  (`netCount_simple_modules_of_separable`): the simple `Q₊`-modules are exactly the three free
  modules on `L₋`, pairwise non-isomorphic.
* **Fix:** either cite the dimension formula, or replace 4400–4402 by "As in
  Section `sec:branching`, every `Q₊`-module is a sum of these three free modules; induction is
  therefore a tensor equivalence."

## 3. `lem:analytic-unitary-all-modules` (4900–4934)

**H1 (suggestion; 4915–4916 "obtained by splitting the separability idempotent on `M ⊗ N`").**
* This can be strengthened at no cost:
  - `e(m ⊗ n) = m s₁ ⊗ s₂ n` is idempotent and coequalizes `r_M ⊗ id` and
    `(id ⊗ l_N) ∘ α`;
  - any splitting of `e` is a **split** coequalizer, with left section
    `m ⊗ n ↦ (m ⊗ s₁) ⊗ s₂ n` (`isSplitCoequalizer`, `SeparableCoequalizer.lean`).
* Split coequalizers are absolute, hence preserved by `X ⊗ −` and `− ⊗ X`.  This is exactly
  what is needed for three things:
  - the induced actions on `M ⊗_A N` to be well defined;
  - the associativity and unit constraints of `⊗_A`;
  - the "balancing relation" step at 4917–4918.
* For this identification only idempotent completeness of `𝒞` is used, not general
  coequalizers or right exactness of `⊗`, and no braiding (`SeparableCoequalizer.lean`).
* The formalized end result still goes through Mathlib's `Bimod.tensorBimod`.  That carries
  `HasCoequalizers` and colimit preservation by `⊗` as typeclass hypotheses (§1).
* **Fix:** add "the projection `M ⊗ N → M ⊗_A N` is a split, hence absolute, coequalizer of the
  two actions, so it is preserved by tensoring on either side".

**H2 (imprecision; 4909–4910 "Commutativity of `A` and the hexagon identity make these
commuting actions").**
* Three things are needed: `l = r ∘ c_{A,M}` is unital, `l` is associative, and `l` commutes
  with `r`.
* Associativity and commutation each use commutativity of `A` and a hexagon identity.  In Lean:
  `braidedLeftAct_one`, `braidedLeftAct_assoc`, `braidedLeftAct_middle_assoc`
  (`BraidedModules.lean`).
* **Fix:** "make `l` a unital associative left action commuting with `r`".

**H3 (suggestion; 4931–4933, locality).**
* `r ∘ c_{A,M} ∘ c_{M,A} = r` holds iff the two left actions `r ∘ c_{A,M}` and
  `r ∘ c_{M,A}^{-1}` coincide (`isLocalRightAct_iff`).
* So `𝒞_A` has two bimodule realizations, one for each braiding orientation, and they agree
  exactly on local modules.  This is a crisp way to say why only the local subcategory inherits
  the braiding.

## 4. Pivotal uniqueness (4109–4116)

**P1 (suggestion).**
* The argument never uses pivotality after its first sentence.  It shows that every tensor
  automorphism of the identity functor of a categorification of `eq:rank6-ring` (with `m ≥ 1`)
  is trivial.
* Equivalently, the universal grading group is trivial (EGNO §4.14): `ρ` and `𝟙` lie in
  `ρ ⊗ ρ`, and `a ⊗ ρ = aρ`.
* Lean proves this general statement (`Fusion.IsHIRing.monoidalAut_eq_refl`,
  `MonoidalAutomorphism.lean`).  It then applies it to the ratio of two pivotal structures
  (`PivotalStructure.ratio`, `Pivotal.lean`).
* **Fix (optional):** "`Aut_⊗(id_𝓕)` is trivial, since the universal grading group of this ring
  is trivial; hence a pivotal structure, a monoidal isomorphism `id ≅ (−)^{**}`, is unique when
  it exists."

**P2 (imprecision; 4111–4115).**
* The rule actually used should be stated: `t_X t_Y = t_Z` whenever `Hom(Z, X ⊗ Y) ≠ 0`, by
  naturality at such a map and monoidality.  It is needed for the paper's "`t_ρ² = 1 = t_ρ`"
  and "their scalars are one".
* The definition of `t_Z` uses `End Z = ℂ` (Schur).
* Passing from the six simples to all objects uses semisimplicity.
* In Lean these are `exists_unit_smul_id`, `mul_eq_of_hom_ne_zero` and
  `app_eq_id_of_iso_biproduct`.

## 5. The rank-six ring step (3794–3823)

**R1 (suggestion; 3806–3809, the direct-ideal argument).**
* The duality step (3804–3805) is still needed.  If `a` fixes the three noninvertibles from the
  left, duality makes the right action trivial as well.
* Then the two functions `χ_ζ` (`a ↦ ζ`, `ρ_i ↦ 0`, `ζ` a primitive cube root of unity) are
  characters of the fusion ring.  Multiplicativity uses both actions being trivial: Lean derives
  this from duality (`Z3.isCharacter_cubeChar`, `Fusion/Rank6.lean`).
* Together with `FPdim` this gives three characters.  But `ℂ ⊕ ℂ ⊕ M₂(ℂ)` has exactly two
  (`FusionAlgebraIso.atMostTwoChars`, `Fusion/FusionAlgebra.lean`).
* This count replaces only the direct-ideal argument of 3806–3809.

`lem:automorphisms-invertibles` (3273–3293): its based-ring core is `aut_invertible`
(`Fusion/AutInvertible.lean`).  It confirms the argument as written, so there are no findings.

## 6. Not covered by this pass

* The forgetful embedding into `𝓕` (3349–3352 and 4402–4405) is covered only partially:
  - `ModuleTower.lean`: modules over `H` in `(Bimod B B, ⊗_B)` are equivalent to
    `(H, B)`-bimodules in `C`;
  - `ModuleTowerTensor.lean`: the relative tensor products agree (coequalizer form);
  - `ModuleTowerMonoidal.lean`: naturality, unit and associativity coherence of the comparison.

  Not covered: the specialization to right modules through the braiding, the locality
  statement, and the packaging as a monoidal functor.
* Gui's unitarizability, semisimplicity, rigidity and finiteness in
  `lem:analytic-unitary-all-modules` (4921–4929).
* The existence of pivotal structures.
* `hθ` itself, which remains external (G1).
