module

public import HaagerupIzumi.C8.ProofMapConcreteBoundary
public import HaagerupIzumi.C8.Category.FreeModuleEquivalence
public import HaagerupIzumi.C8.Category.LminusSplitting
public import HaagerupIzumi.C8.Category.UntwistedFromSeparable
public import HaagerupIzumi.C8.Category.UntwistedVecEquivalence

@[expose] public section

/-!
# The untwisted-pointed arrow of the proof map, made concrete

Lines 3322–3352 of `c8_expanded_20260929/haagerup_c8_expanded.tex` (the paragraph after
Lemma `lem:no-sign-extension`) are the arrow

* `L_untwisted : threeInvertibles → certDiscriminant → lagrangianCenter → stronglyRational →
  untwistedPointed`.

The concrete objects: a `𝕜`-linear monoidal category `C` (the pointed category `Rep(B)` of the
lattice VOA `B`) with its nine invertibles `S v`, `v ∈ (ℤ/3)²` (the discriminant group), and the
algebra `A = H/B` in `C` (a commutative monoid object; `C` braided).  `untwistedNodes R 𝕜 C A S`
overrides `untwistedPointed` by `UntwistedNode 𝕜 C A S`: free `H/B`-module induction `x ↦ x ⊗ A`
from the additive closure of the three invertibles `S (a, -a)` of the isotropic line `L₋` is an
equivalence onto the category of all right `A`-modules ("induction identifies the entire
all-module category for `H/B` with this untwisted pointed category", lines 3345–3348), and
(`UntwistedVecNode`) the module category `𝒞_A ⊂ (Bimod A A, ⊗_A)` is *monoidally* equivalent to
the untwisted symmetric `Vec_{ℤ/3}` (`GrMat`), braided on the leg `Vec_{ℤ/3} ≃` additive closure
of `L₋` (`untwisted_vec_equivalence_of_separable`, Category/UntwistedVecEquivalence; lines
3335–3352).
`ProofMapConcreteBoundary.boundaryNodes`, applied on top, adds `ν₃(a) = 1`.

`untwisted_arrow` proves the equivalence through `RightMod.freeLminus_isEquivalence_of_separable`
(Category/UntwistedFromSeparable, FreeModuleEquivalence, LminusSplitting: full faithfulness from the
free-module adjunction and the transversality `L₊ ∩ L₋ = 0`, essential surjectivity from the
separability of `H/B` and idempotent completeness) and the monoidal equivalence through
`untwisted_vec_equivalence_of_separable` (with the [external] input `hθ`: trivial self-braidings
on `L₋`).  Remaining inputs: the structural facts about
`Rep(B)` and `H/B` (`UntwistedInputs`, with the instance hypotheses: `Rep(B)` braided and
linear monoidal with finite-dimensional Homs, coequalizers preserved by `X ⊗ -` and `- ⊗ X`,
`H/B` commutative) and `hν`.  **The `𝓕`-side content is an input**: `hν` (the tensor embedding
into `𝓕` and the Frobenius–Schur indicator, conditional on `lagrangianCenter`,
`stronglyRational`) supplies `ν₃(a) = 1`, which is the only content of the node used downstream
(`L_rankSixMoments`, `E_izumi`); the identification with the untwisted `Vec_{ℤ/3}` is proved.
-/

namespace HaagerupIzumi.C8.ProofMap

open CategoryTheory MonoidalCategory MonObj Limits Module HaagerupIzumi.C8.RightMod

universe v u

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

attribute [local instance] bimodMonoidal

/-- The monoidal part of the node (lines 3335–3352, the conclusion of
`untwisted_vec_equivalence_of_separable`): for some fusion and unit isomorphisms of the
invertibles, there are `G : ℤ/3 → C` with `G a = S (a, -a)` and a monoidal equivalence
`E : Vec_{ℤ/3} ≌ 𝒞_A` (untwisted symmetric `GrMat` on the left, `𝒞_A` the essential image of
`toBimod A` in `(Bimod A A, ⊗_A)`), equal to realization followed by free induction, whose first
leg `Vec_{ℤ/3} ⥤` (additive closure of `L₋`) is braided. -/
def UntwistedVecNode (𝕜 : Type) [Field 𝕜] (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [Preadditive C] [HasFiniteBiproducts C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive C]
    [Linear 𝕜 C] [MonoidalLinear 𝕜 C] (A : Mon C) [IsCommMonObj A.X]
    (S : ZMod 3 × ZMod 3 → C) : Prop :=
  ∃ (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C),
    haveI := lminusClosure_isMonoidal hfusion hunitS
    ∃ (G : Discrete (Multiplicative (ZMod 3)) ⥤ C)
      (hmem : ∀ X : GrMat (Multiplicative (ZMod 3)) 𝕜, LminusClosure S ((GrMat.real G).obj X))
      (E : GrMat (Multiplicative (ZMod 3)) 𝕜 ≌ (toBimod A).essImage.FullSubcategory)
      (h : E.functor.Monoidal),
      (∀ a : ZMod 3, G.obj ⟨Multiplicative.ofAdd a⟩ = S (a, -a)) ∧
      (letI := h; letI := E.inverseMonoidal; E.IsMonoidal) ∧
      E.functor ⋙ (toBimod A).essImage.ι =
        (LminusClosure S).lift (GrMat.real G) hmem ⋙ freeLminus A S ⋙ toBimod A ∧
      Nonempty ((LminusClosure S).lift (GrMat.real G) hmem).Braided

/-- The concrete `untwistedPointed` node: free `H/B`-module induction from the additive closure of
the three invertibles of `L₋` is an equivalence onto all right `H/B`-modules, and the module
category of `H/B` is monoidally equivalent to the untwisted `Vec_{ℤ/3}` (`UntwistedVecNode`). -/
def UntwistedNode (𝕜 : Type) [Field 𝕜] (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [Preadditive C] [HasFiniteBiproducts C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive C]
    [Linear 𝕜 C] [MonoidalLinear 𝕜 C] (A : Mon C) [IsCommMonObj A.X]
    (S : ZMod 3 × ZMod 3 → C) : Prop :=
  (freeLminus A S).IsEquivalence ∧ UntwistedVecNode 𝕜 C A S

/-- The proof map with `untwistedPointed` made concrete. -/
def untwistedNodes (R : Nodes) (𝕜 : Type) [Field 𝕜] (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [BraidedCategory C] [Preadditive C] [HasFiniteBiproducts C]
    [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive C]
    [Linear 𝕜 C] [MonoidalLinear 𝕜 C] (A : Mon C) [IsCommMonObj A.X]
    (S : ZMod 3 × ZMod 3 → C) : Nodes :=
  { R with untwistedPointed := UntwistedNode 𝕜 C A S }

/-- The remaining inputs of `L_untwisted` on `Rep(B)` and `H/B` (the hypotheses of
`RightMod.freeLminus_isEquivalence_of_separable`), tagged; `disc` is the opaque node
`certDiscriminant`.  They are structural statements about the pointed category `Rep(B)` and the
algebra `H/B`; no VOA-side input on the multiplication of `H` is needed. -/
structure UntwistedInputs (𝕜 : Type) [Field 𝕜] (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [Preadditive C] [Linear 𝕜 C] [MonoidalPreadditive C] [MonoidalLinear 𝕜 C]
    [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] (A : Mon C)
    (S : ZMod 3 × ZMod 3 → C) (disc : Prop) where
  /-- [external] the nine lattice `B`-modules `S v`, `v ∈ (ℤ/3)²` (the discriminant group of
  `certDiscriminant`, [certificate]), are simple and pairwise non-isomorphic, with endomorphisms
  `𝕜` (Dong's classification of lattice VOA modules). -/
  hSchur : disc → ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0
  /-- [external] they multiply by the group law of the discriminant group (fusion rules of lattice
  VOA modules, Dong–Lepowsky). -/
  hfusion : disc → ∀ v w, S v ⊗ S w ≅ S (v + w)
  /-- [certificate] `H/B`, as an object of `Rep(B)`, is the sum of the invertibles on the
  isotropic line `L₊ = {(c, c)}` (line 3331). -/
  hA : disc → (A.X ≅ ⨁ fun c : ZMod 3 => S (c, c))
  /-- [external] the invertible `S (0, 0)` is the vacuum module `B`, the unit of `Rep(B)`. -/
  hunitS : disc → (S (0, 0) ≅ 𝟙_ C)
  /-- [standard/external] `H/B` is a connected étale algebra in the fusion category `Rep(B)`,
  hence separable: a section of its multiplication that is an `H/B`-bimodule map.  (Earlier
  variants used instead the VOA input that homogeneous products in `H` do not vanish
  (`freeLminus_isEquivalence_of_isIdempotentComplete`), or a nondegenerate pairing
  (`freeLminus_isEquivalence_categorical`); separability makes both unnecessary.) -/
  hS : disc → SeparabilitySection A
  /-- [standard] `3 ≠ 0` in `𝕜`. -/
  h3 : (3 : 𝕜) ≠ 0
  /-- [external] `Rep(B)` is semisimple and pointed: every object is a finite sum of the nine
  invertibles (lattice VOA modules, Dong). -/
  hss : disc → ∀ X : C, ∃ (n : ℕ) (w : Fin n → ZMod 3 × ZMod 3),
    Nonempty (X ≅ ⨁ fun j => S (w j))
  /-- [standard] `Rep(B)` is abelian, hence idempotent complete.  (The splitting of idempotents
  of sums of `L₋`-invertibles through sub-sums, formerly an input, is derived from this:
  `Category.RightMod.hsplit_of_isIdempotentComplete`.) -/
  hidem : IsIdempotentComplete C
  /-- [external] the self-braidings of the invertibles on `L₋` are trivial (`q = 0` on the
  isotropic line `L₋`: the twists `e^{2πi q}` are trivial, lines 3335–3340, and for an invertible
  of order three the self-braiding is the twist; braiding of lattice VOA modules, Dong–Lepowsky). -/
  hθ : disc → ∀ a : ZMod 3, (β_ (S (a, -a)) (S (a, -a))).hom = 𝟙 _

/-- **The node from the inputs**: the free-induction equivalence
(`Category.RightMod.freeLminus_isEquivalence_of_separable`) and the monoidal equivalence with the
untwisted `Vec_{ℤ/3}` (`untwisted_vec_equivalence_of_separable`, using also `hθ`).  The structural
hypotheses on `Rep(B)` and `H/B` for the latter (braiding, commutativity of `H/B`, coequalizers
preserved by `X ⊗ -`, `- ⊗ X`, linear monoidal structure) are instance arguments, tagged in
`TRUST_BOUNDARY.md` ([standard]/[external]: `Rep(B)` is a braided fusion category, `H/B` a
commutative algebra in it). -/
theorem untwistedNode_of_inputs (𝕜 : Type) [Field 𝕜] (C : Type u) [Category.{v} C]
    [MonoidalCategory C] [BraidedCategory C] [Preadditive C] [HasFiniteBiproducts C]
    [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive C]
    [Linear 𝕜 C] [MonoidalLinear 𝕜 C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] (A : Mon C)
    [IsCommMonObj A.X] (S : ZMod 3 × ZMod 3 → C) (disc : Prop) (I : UntwistedInputs 𝕜 C A S disc)
    (hd : disc) : UntwistedNode 𝕜 C A S :=
  haveI := I.hidem
  ⟨freeLminus_isEquivalence_of_separable 𝕜 (I.hSchur hd) (I.hfusion hd) (I.hunitS hd) (I.hA hd)
    (I.hS hd) I.h3 (I.hss hd),
   ⟨I.hfusion hd, I.hunitS hd,
    untwisted_vec_equivalence_of_separable A 𝕜 S (I.hSchur hd) (I.hfusion hd) (I.hunitS hd)
      (I.hA hd) (I.hS hd) I.h3 (I.hss hd) (I.hθ hd)⟩⟩

/-- **`L_untwisted`** (lines 3322–3352).

* Concrete nodes: `untwistedPointed` (`UntwistedNode`, and the conjunct `ν₃(a) = 1` of
  `boundaryNodes`), `threeInvertibles` (applied to `hν`).  `certDiscriminant` stays opaque and the
  inputs are conditional on it; the opaque `lagrangianCenter` (`lag`) and `stronglyRational`
  (`rat`) are applied to `hν`.
* Concrete theorems: `RightMod.freeLminus_isEquivalence_of_separable` (Category/
  UntwistedFromSeparable, FreeModuleEquivalence, LminusSplitting): free `H/B`-induction from the
  additive closure of `L₋` is an equivalence onto all `H/B`-modules; and
  `untwisted_vec_equivalence_of_separable` (Category/UntwistedVecEquivalence, GradedMatMonoidal):
  the module category `𝒞_A` is monoidally equivalent to the untwisted symmetric `Vec_{ℤ/3}`,
  braided on the leg `Vec_{ℤ/3} ≃` additive closure of `L₋` (this replaces the Tannakian step
  "symmetric with trivial twists, hence the untwisted `Vec_{ℤ/3}`" of lines 3335–3348, which
  was an [external] Deligne input before).
* Remaining inputs: `UntwistedInputs` (fields tagged, including [external] `hθ`: trivial
  self-braidings on `L₋`), the instance hypotheses on `C` and `A`, and `hν`.  **The `𝓕`-side
  content is an input**: `hν` supplies `ν₃(a) = 1`, the only content of the node used
  downstream.  It stands for [manuscript step] lines 3349–3352 — viewing `H/B`-modules in
  `Rep(U)` (rigid modular, node `stronglyRational`) gives a full tensor embedding of the
  untwisted `Vec_{ℤ/3}` into `𝓕 = Rep(U)_H` (Lagrangian center, node `lagrangianCenter`) whose
  image is the pointed part `{𝟙, a, a*}` (node `threeInvertibles`); [standard] the
  Frobenius–Schur indicator `ν₃` of the generator of the untwisted `Vec_{ℤ/3}` is `1`.  Neither
  `𝓕` nor `ν₃` is part of the categorical model, so this step is not derived. -/
theorem untwisted_arrow (𝕜 : Type) [Field 𝕜] (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [Preadditive C] [HasFiniteBiproducts C] [HasCoequalizers C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive C]
    [Linear 𝕜 C] [MonoidalLinear 𝕜 C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] (A : Mon C)
    [IsCommMonObj A.X] (S : ZMod 3 × ZMod 3 → C) (B : BoundaryData ι κ) (disc lag rat : Prop)
    (I : UntwistedInputs 𝕜 C A S disc)
    (hν : UntwistedNode 𝕜 C A S → disc → lag → rat →
      (Z3Generator B.F B.a ∧ ∀ x, B.F.IsInvertible x → x = B.F.unit ∨ x = B.a ∨ x = B.F.dual B.a) →
      B.ν₃ = 1) :
    (Z3Generator B.F B.a ∧ ∀ x, B.F.IsInvertible x → x = B.F.unit ∨ x = B.a ∨ x = B.F.dual B.a) →
      disc → lag → rat → UntwistedNode 𝕜 C A S ∧ B.ν₃ = 1 := by
  intro h3inv hd hlag hrat
  have h : UntwistedNode 𝕜 C A S := untwistedNode_of_inputs 𝕜 C A S disc I hd
  exact ⟨h, hν h hd hlag hrat h3inv⟩

#print axioms untwistedNode_of_inputs
#print axioms untwisted_arrow

end HaagerupIzumi.C8.ProofMap
