module

public import HaagerupIzumi.C8.Category.FreeModule
public import HaagerupIzumi.C8.Data.Weights
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

@[expose] public section

/-! # Free `H/B`-module induction is fully faithful on the three simples of `L₋`

The fully-faithfulness step in the proof of `L_untwisted` (manuscript
`haagerup_c8_expanded.tex`, lines 3337–3345): "It is fully faithful since
`Hom_{H/B}(x ⊗ (H/B), y ⊗ (H/B)) ≅ Hom_{Rep(B)}(x, y ⊗ (H/B))` has dimension `δ_{x,y}` for
`x, y ∈ L₋`: distinct elements of `L₋` represent distinct cosets of `L₊`."

Setting: `C` is a `𝕜`-linear monoidal category (`𝕜` a field) with finite biproducts,
additive and linear whiskering, and finite-dimensional Hom spaces; `A` is a monoid object
(the algebra `H/B` in `Rep(B)`).

* `homBiproductLinearEquiv`: `Hom(X, ⨁ f) ≃ₗ ∏ Hom(X, f j)`.
* `finrank_hom_tensor_biproduct`: `dim Hom(X, Y ⊗ ⨁ f) = ∑ⱼ dim Hom(X, Y ⊗ f j)`.
* `finrank_hom_free_of_pointed`: for a family of objects `S : G → C` indexed by a group
  `G` with `dim Hom(S v, S w) = δ_{v,w}` and `S v ⊗ S w ≅ S (v + w)`, and
  `A ≅ ⨁ⱼ S (ℓ j)`, the free modules satisfy
  `dim Hom_A(S x ⊗ A, S y ⊗ A) = #{j | x = y + ℓ j}` (free-module adjunction
  `finrank_hom_free`, distributivity, Schur).
* `finrank_hom_free_Lminus`: for `G = (ℤ/3)²`, `A ≅ ⨁_{c ∈ ℤ/3} S (c, c)` (that is,
  `H/B = ⊕_{ℓ ∈ L₊} ℓ`) and `x = (a, -a)`, `y = (b, -b)` in `L₋`, this dimension is
  `δ_{a,b}` (with the arithmetic count `Weights.free_induction_hom_count`).
* `freeMap_bijective_Lminus`: hence free induction `f ↦ f ⊗ A` is a bijection
  `Hom(x, y) ≅ Hom_A(x ⊗ A, y ⊗ A)` for `x, y ∈ L₋`: it is fully faithful on the full
  subcategory spanned by the three simples `S (a, -a)`.  Injectivity for `x = y` uses only
  that both spaces are one-dimensional and that free induction sends `𝟙` to `𝟙 ≠ 0`.  The
  extension to the additive closure (finite direct sums of the three simples), by additivity
  of free induction, is `freeMap_bijective_Lminus_biproduct` (`Category/FreeModuleAdditive.lean`).

Hypotheses (statements about `Rep(B)` and `H/B` that are not formalized here, all phrased as
the structural facts used, none as the conclusion): `hSchur` (the invertible objects `S v`
are simple, pairwise non-isomorphic, with endomorphisms `𝕜`), `hfusion` (they multiply by
the group law of the metric group `(ℤ/3)²` of the local `B`-modules), `hA` (`H/B`, as an
object of `Rep(B)`, is the sum of the invertibles in `L₊`).

Related results: `Category/FreeModuleTensor.lean` (the tensorator `(X ⊗ A) ⊗_A (Y ⊗ A) ≅
(X ⊗ Y) ⊗ A` on objects, the unit isomorphism), `Category/FreeModuleNaturality.lean`,
`Category/FreeModuleMonoidal.lean`, `Category/FreeModuleMonoidalFunctor.lean` (naturality,
coherence, free induction as a monoidal functor to `(Bimod A A, ⊗_A)`),
`Category/FreeModuleSeparable.lean` (every module is a retract of a free module),
`Category/FreeModuleAdditive.lean` (additivity), `Category/FreeModuleGraded.lean`
(`ℓ ⊗ A ≅ A`), `Category/FreeModuleTwistedSeparable.lean` (the separability section of
`H/B`), `Category/FreeModuleEssSurj.lean`, `Category/TwistedGroupAlgebraOfMul.lean`,
`Category/FreeModuleEquivalence.lean` (induction from the additive closure of `L₋` is an
equivalence of categories) and `Category/SimpleModulesLminus.lean` (the three simple
modules).

Status of the remaining steps of `L_untwisted` (manuscript lines 3335–3352), 4 October 2026:
* formalized in the companion files listed above: additivity of free induction and full
  faithfulness on the additive closure of `L₋`; `ℓ ⊗ A ≅ A` for `ℓ ∈ L₊` and "every free
  module is induced from `L₋`"; a separability section for `H/B` (from the hypothesis that its
  multiplication is a twisted group algebra, `TwistedGroupAlgebra`, or from `hmul`);
  essential surjectivity and the equivalence `freeLminus_isEquivalence` (of plain categories);
  the three simple modules (`netCount_simple_modules`); the monoidal-functor coherence of the
  tensorator (for `freeFunctor A ⋙ toBimod A` into `(Bimod A A, ⊗_A)`);
* still hypotheses there: the facts behind `hSchur`, `hfusion`, `hA`; `hmul` (homogeneous
  components of the multiplication of `H/B` are nonzero); `hss` and `hsplit` (semisimplicity
  and Krull–Schmidt for `Rep(B)`).  Later files derive `hmul` from a connected unit and a
  separability section (`TwistedGroupAlgebraOfUnit`, `NondegFromSeparable`) and `hsplit` from
  `IsIdempotentComplete C` (`LminusSplitting`);
* formalized in later files: the monoidal structure on `𝒞_A` (a monoidal full subcategory of
  `(Bimod A A, ⊗_A)`) and the monoidal equivalence (`FreeModuleMonoidalEquivalence`,
  `UntwistedFromSeparable`); the identification with the untwisted `Vec_{ℤ/3}`, given the
  external trivial self-braidings `hθ` on `L₋` (`UntwistedVecEquivalence`); the algebraic core
  of the embedding, `H`-modules over `B`-bimodules as `(H, B)`-bimodules with the comparison of
  relative tensor products (`ModuleTower*`);
* not formalized: that comparison packaged as a monoidal functor, and the embedding into
  `Rep(U)` and `𝓕` by forgetting the locality condition for `B` (lines 3349–3352). -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits Module

universe v u

namespace RightMod

/-- A linear map out of a one-dimensional space that does not vanish is injective. -/
theorem linearMap_injective_of_finrank_eq_one {K V W : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (T : V →ₗ[K] W) (hV : finrank K V = 1) (v : V)
    (hv : T v ≠ 0) : Function.Injective T := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h, map_zero])
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' v hv0).1 hV w
  rw [map_smul] at hw
  rcases smul_eq_zero.1 hw with hc | hc
  · rw [hc, zero_smul]
  · exact absurd hc hv

/-- In a `𝕜`-linear category, an object with one-dimensional endomorphism space has
`𝟙 ≠ 0`. -/
theorem id_ne_zero_of_finrank_eq_one (𝕜 : Type*) [Field 𝕜] {D : Type*} [Category D]
    [Preadditive D] [Linear 𝕜 D] {M : D} (h : finrank 𝕜 (M ⟶ M) = 1) :
    (𝟙 M : M ⟶ M) ≠ 0 := by
  intro h0
  have hsub : Subsingleton (M ⟶ M) := ⟨fun f g => by
    rw [← Category.comp_id f, ← Category.comp_id g, h0, Limits.comp_zero, Limits.comp_zero]⟩
  rw [Module.finrank_zero_of_subsingleton] at h
  exact zero_ne_one h

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [MonoidalPreadditive C]
  [MonoidalLinear 𝕜 C] [HasFiniteBiproducts C]

/-- Morphisms into a finite biproduct, as a `𝕜`-linear equivalence with the product of the
Hom spaces into the summands. -/
noncomputable def homBiproductLinearEquiv {J : Type} [Finite J] (X : C) (f : J → C) :
    (X ⟶ ⨁ f) ≃ₗ[𝕜] (∀ j, X ⟶ f j) where
  toFun g j := g ≫ biproduct.π f j
  invFun h := biproduct.lift h
  left_inv g := biproduct.hom_ext _ _ fun j => biproduct.lift_π _ j
  right_inv h := funext fun j => biproduct.lift_π h j
  map_add' g g' := by
    funext j
    exact Preadditive.add_comp _ _ _ _ _ _
  map_smul' r g := by
    funext j
    exact Linear.smul_comp _ _ _ _ _ _

variable [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]

omit [MonoidalLinear 𝕜 C] in
/-- `dim Hom(X, Y ⊗ ⨁ⱼ f j) = ∑ⱼ dim Hom(X, Y ⊗ f j)` (distributivity of `⊗` over `⊕`). -/
theorem finrank_hom_tensor_biproduct {J : Type} [Fintype J] (X Y : C) (f : J → C) :
    finrank 𝕜 (X ⟶ Y ⊗ ⨁ f) = ∑ j, finrank 𝕜 (X ⟶ Y ⊗ f j) := by
  rw [(Linear.homCongr 𝕜 (Iso.refl X) (leftDistributor Y f)).finrank_eq,
    (homBiproductLinearEquiv 𝕜 X (fun j => Y ⊗ f j)).finrank_eq, Module.finrank_pi_fintype]

/-- **Hom count for free modules over a pointed algebra.**  Let `S : G → C` be objects with
`dim Hom(S v, S w) = δ_{v,w}` and `S v ⊗ S w ≅ S (v + w)`, and let `A ≅ ⨁ⱼ S (ℓ j)`.  Then
`dim Hom_A(S x ⊗ A, S y ⊗ A) = #{j | x = y + ℓ j}`. -/
theorem finrank_hom_free_of_pointed {G : Type*} [Add G] [DecidableEq G] {J : Type} [Fintype J]
    (A : Mon C) (S : G → C) (ℓ : J → G)
    (hSchur : ∀ v w : G, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w : G, S v ⊗ S w ≅ S (v + w))
    (hA : A.X ≅ ⨁ fun j => S (ℓ j)) (x y : G) :
    finrank 𝕜 (free A (S x) ⟶ free A (S y)) =
      (Finset.univ.filter fun j => x = y + ℓ j).card := by
  rw [finrank_hom_free 𝕜 A,
    (Linear.homCongr 𝕜 (Iso.refl (S x)) (whiskerLeftIso (S y) hA)).finrank_eq,
    finrank_hom_tensor_biproduct, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(Linear.homCongr 𝕜 (Iso.refl (S x)) (hfusion y (ℓ j))).finrank_eq, hSchur]

/-- `(a, -a) = (b, -b)` in `(ℤ/3)²` iff `a = b`, in the form needed for the Schur count. -/
theorem Lminus_ite_eq : ∀ a b : ZMod 3,
    (if ((a, -a) : ZMod 3 × ZMod 3) = (b, -b) then 1 else 0 : ℕ) = if a = b then 1 else 0 := by
  decide

/-- **The fully-faithfulness count** (manuscript lines 3340–3345): for `A = H/B ≅ ⊕_{ℓ ∈ L₊} ℓ`
and `x = (a, -a)`, `y = (b, -b)` in `L₋`, `dim Hom_A(x ⊗ A, y ⊗ A) = δ_{a,b}`. -/
theorem finrank_hom_free_Lminus (A : Mon C) (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
    (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)) (a b : ZMod 3) :
    finrank 𝕜 (free A (S (a, -a)) ⟶ free A (S (b, -b))) = if a = b then 1 else 0 := by
  rw [finrank_hom_free_of_pointed 𝕜 A S (fun c : ZMod 3 => (c, c)) hSchur hfusion hA]
  exact Weights.free_induction_hom_count a b

/-- **Free induction is fully faithful on the three simples of `L₋`** (manuscript
lines 3338–3345): for `x = (a, -a)`, `y = (b, -b)` in `L₋`, `f ↦ f ⊗ A` is a bijection
`Hom(x, y) ≅ Hom_A(x ⊗ A, y ⊗ A)`. -/
theorem freeMap_bijective_Lminus (A : Mon C) (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
    (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)) (a b : ZMod 3) :
    Function.Bijective (fun f : S (a, -a) ⟶ S (b, -b) => (freeFunctor A).map f) := by
  have hW := finrank_hom_free_Lminus 𝕜 A S hSchur hfusion hA a b
  have hV : finrank 𝕜 (S (a, -a) ⟶ S (b, -b)) = if a = b then 1 else 0 :=
    (hSchur _ _).trans (Lminus_ite_eq a b)
  have : FiniteDimensional 𝕜 (free A (S (a, -a)) ⟶ free A (S (b, -b))) :=
    LinearEquiv.finiteDimensional (freeHomLinearEquiv 𝕜 A _ _).symm
  have hinj : Function.Injective (freeMapLinear 𝕜 A (S (a, -a)) (S (b, -b))) := by
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl] at hV hW
      refine linearMap_injective_of_finrank_eq_one _ hV (𝟙 _) ?_
      have h1 : freeMapLinear 𝕜 A (S (a, -a)) (S (a, -a)) (𝟙 _) = 𝟙 (free A (S (a, -a))) :=
        hom_ext (MonoidalCategory.id_whiskerRight _ _)
      rw [h1]
      exact id_ne_zero_of_finrank_eq_one 𝕜 hW
    · rw [if_neg hab] at hV
      have : Subsingleton (S (a, -a) ⟶ S (b, -b)) := Module.finrank_zero_iff.1 hV
      exact Function.injective_of_subsingleton _
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hV.trans hW.symm)).1
    hinj⟩

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.linearMap_injective_of_finrank_eq_one
#print axioms HaagerupIzumi.C8.RightMod.id_ne_zero_of_finrank_eq_one
#print axioms HaagerupIzumi.C8.RightMod.homBiproductLinearEquiv
#print axioms HaagerupIzumi.C8.RightMod.finrank_hom_tensor_biproduct
#print axioms HaagerupIzumi.C8.RightMod.finrank_hom_free_of_pointed
#print axioms HaagerupIzumi.C8.RightMod.finrank_hom_free_Lminus
#print axioms HaagerupIzumi.C8.RightMod.freeMap_bijective_Lminus
