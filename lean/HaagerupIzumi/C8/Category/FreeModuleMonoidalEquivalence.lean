module

public import HaagerupIzumi.C8.Category.FreeModuleEquivalence
public import HaagerupIzumi.C8.Category.FreeModuleMonoidalFunctor
public import HaagerupIzumi.C8.Category.RelativeTensor
public import HaagerupIzumi.C8.Category.TwistedGroupAlgebraOfUnit
public import Mathlib.CategoryTheory.Monoidal.Subcategory

@[expose] public section

/-! # Free induction from the additive closure of `L₋` is a monoidal equivalence

"Free `H/B`-module induction is tensor on this subcategory. ... Thus induction identifies the
entire all-module category for `H/B` with this untwisted pointed category" (manuscript
`haagerup_c8_expanded.tex`, lines 3335–3352).  This file upgrades the equivalence of plain
categories `freeLminus_isEquivalence` (`Category/FreeModuleEquivalence.lean`) to a monoidal
equivalence.

* **The L₋ closure is monoidal.**  `lminusClosure_isMonoidal`: if `S v ⊗ S w ≅ S (v + w)`
  (`hfusion`) and `S (0, 0) ≅ 𝟙_ C` (`hunitS`; both part of the pointed structure of `Rep(B)`),
  the additive closure `LminusClosure S` of the invertibles `S (a, -a)` contains `𝟙_ C` and is
  closed under `⊗` (distributivity of `⊗` over finite biproducts, and `L₋` is a subgroup).  Its
  full subcategory is then a monoidal category (Mathlib's `fullMonoidalSubcategory`).
* **The module category is monoidal.**  `RightMod A` is realized by `toBimod A` as the full
  subcategory of `A`-bimodules with `actLeft = c_{A,X} ≫ actRight`
  (`Category/BraidedModules.lean`); `essImage_toBimod_isMonoidal`: this subcategory contains
  the unit `A` and is closed under `⊗_A` (`Category/RelativeTensor.lean`), so it is a monoidal
  full subcategory of `(Bimod A A, ⊗_A)` (`RightMod.bimodMonoidal`).  Write `𝒞_A` for it.
* **Induction is monoidal.**  `freeLminusLift A S : LminusClosure ⥤ 𝒞_A` is free induction
  `X ↦ X ⊗ A` (its composite with the inclusion of `𝒞_A` is `freeLminus A S ⋙ toBimod A`,
  `freeLminusLift_comp_ι`); `freeLminusLiftCoreMonoidal`: it is a (strong) monoidal functor, with
  tensorator `freeTensorIso` and unit `freeUnitIso⁻¹` (the coherence axioms are those of
  `Category/FreeModuleMonoidal.lean`).
* **Monoidal equivalence.**  `freeLminusLift_isEquivalence`: it is an equivalence of categories
  as soon as `freeLminus A S` is (`freeLminus_isEquivalence`); `freeLminusMonoidalEquivalence`:
  the resulting equivalence, whose functor is monoidal; its inverse is monoidal
  (`Equivalence.inverseMonoidal`) and `freeLminusMonoidalEquivalence_isMonoidal`: the
  equivalence is a monoidal equivalence in Mathlib's sense (`Equivalence.IsMonoidal`).
  `freeLminus_monoidalEquivalence`: the whole statement under the named hypotheses of
  `freeLminus_isEquivalence` plus `hunitS`.

Hypotheses: `C` braided, preadditive with finite biproducts and additive tensor products, with
coequalizers preserved by `X ⊗ -` and `- ⊗ X` (Mathlib's `Bimod.tensorBimod`; for a separable
`A` the relevant coequalizers are split, `Category/SeparableCoequalizer.lean`, but Mathlib's
typeclasses ask for all coequalizers); `A` commutative.  For the equivalence, those of
`freeLminus_isEquivalence` (`hSchur`, `hfusion`, `hA`, `hmul`, `3 ≠ 0`, `hss`, `hsplit`), and
`hunitS : S (0, 0) ≅ 𝟙_ C`.

Not formalized here: a braiding on `𝒞_A` (it exists only on local modules); the monoidal
structure transported to `RightMod A` itself (here `𝒞_A` is its image in `Bimod A A`,
`toBimod A` being fully faithful).

Status of the Tannakian step for `L₋` (4 October 2026): the abelian 3-cocycle of the pointed
braided category on the invertibles `S (a, -a)` is constructed in `Category/PointedCocycle.lean`
(`pentagon_scalar`, `hexagon_forward_scalar`, `hexagon_reverse_scalar`) and trivialized in
`Category/PointedCocycleZ3.lean` (`Lminus_untwisted_symmetric`); the resulting braided monoidal
functor from the symmetric discrete `ℤ/3` is `Lminus_braided_vec`
(`Category/LminusBraidedVec.lean`), and into `LminusClosure S` with its own monoidal structure
and inherited braiding it is `Lminus_closure_braided_functor`
(`Category/LminusClosureFunctor.lean`); `LminusClosure S` is symmetric and equivalent, as a
category, to the additive envelope of its simples (`Category/LminusEnvelope.lean`).  Remaining
external: `hθ` (the self-braiding of each invertible of `L₋` in `Rep(B)` is trivial).  The monoidal comparison on general graded objects is
`GrMat.Lminus_graded_braided_equivalence` and `Lminus_vec_braided_equivalence`
(`Category/GradedMat.lean`, `Category/GradedMatMonoidal.lean`).  Composed with free induction it is
`untwisted_vec_equivalence_of_separable` (`Category/UntwistedVecEquivalence.lean`). -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

section LminusMonoidal

variable [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]
  {S : ZMod 3 × ZMod 3 → C}

/-- The tensor product of two finite sums of `L₋`-invertibles is a finite sum of
`L₋`-invertibles (distributivity, and `(a, -a) + (b, -b) = (a + b, -(a + b))`). -/
theorem lminus_biproduct_tensor_mem (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) {n m : ℕ}
    (a : Fin n → ZMod 3) (b : Fin m → ZMod 3) :
    LminusClosure S ((⨁ fun j => S (a j, -a j)) ⊗ (⨁ fun k => S (b k, -b k))) := by
  obtain ⟨e⟩ : Nonempty ((Σ _ : Fin n, Fin m) ≃ Fin (n * m)) :=
    ⟨(Equiv.sigmaEquivProd (Fin n) (Fin m)).trans finProdFinEquiv⟩
  refine ⟨n * m, fun i => a (e.symm i).1 + b (e.symm i).2, ⟨?_⟩⟩
  refine rightDistributor (fun j => S (a j, -a j)) (⨁ fun k => S (b k, -b k)) ≪≫
    biproduct.mapIso (fun j => leftDistributor (S (a j, -a j)) (fun k => S (b k, -b k))) ≪≫
    biproductBiproductIso (fun _ : Fin n => Fin m)
      (fun j k => S (a j, -a j) ⊗ S (b k, -b k)) ≪≫
    biproduct.whiskerEquiv e (fun p => ?_)
  refine eqToIso ?_ ≪≫ (hfusion _ _).symm
  simp only [Equiv.symm_apply_apply]
  congr 1
  exact Prod.ext rfl (neg_add _ _)

/-- **The additive closure of `L₋` is a monoidal subcategory**, given `S v ⊗ S w ≅ S (v + w)`
and `S (0, 0) ≅ 𝟙_ C`. -/
theorem lminusClosure_isMonoidal (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
    (hunitS : S (0, 0) ≅ 𝟙_ C) : (LminusClosure S).IsMonoidal where
  prop_unit :=
    ⟨1, fun _ => 0, ⟨hunitS.symm ≪≫ eqToIso (by rw [neg_zero]) ≪≫
      (biproductUniqueIso (fun _ : Fin 1 => S ((0 : ZMod 3), -(0 : ZMod 3)))).symm⟩⟩
  prop_tensor X Y hX hY := by
    obtain ⟨n, a, ⟨eX⟩⟩ := hX
    obtain ⟨m, b, ⟨eY⟩⟩ := hY
    obtain ⟨N, c, ⟨i⟩⟩ := lminus_biproduct_tensor_mem hfusion a b
    exact ⟨N, c, ⟨tensorIso eX eY ≪≫ i⟩⟩

end LminusMonoidal

variable [BraidedCategory C] [Preadditive C] [HasFiniteBiproducts C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A : Mon C) [IsCommMonObj A.X]

attribute [local instance] bimodMonoidal

/-- **The module category is monoidal**: the essential image of `toBimod A` (right modules,
as bimodules with `actLeft = c_{A,X} ≫ actRight`) contains the unit `A` and is closed under
`⊗_A`. -/
instance essImage_toBimod_isMonoidal : (toBimod A).essImage.IsMonoidal where
  prop_unit := regular_mem_essImage A
  prop_tensor _ _ hX hY := tensorBimod_mem_essImage_of_mem A hX hY

variable (S : ZMod 3 × ZMod 3 → C)

/-- Free induction from the additive closure of `L₋` into the module category `𝒞_A`
(the essential image of `toBimod A` in `Bimod A A`). -/
def freeLminusLift :
    (LminusClosure S).FullSubcategory ⥤ (toBimod A).essImage.FullSubcategory :=
  (toBimod A).essImage.lift (freeLminus A S ⋙ toBimod A)
    (fun X => ⟨(freeLminus A S).obj X, ⟨Iso.refl _⟩⟩)

omit [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
theorem freeLminusLift_comp_ι :
    freeLminusLift A S ⋙ (toBimod A).essImage.ι = freeLminus A S ⋙ toBimod A := rfl

section Monoidal

variable [MonoidalPreadditive C] [(LminusClosure S).IsMonoidal]

set_option backward.isDefEq.respectTransparency false in
/-- **Free induction is a monoidal functor** `LminusClosure S ⥤ 𝒞_A`, with tensorator
`freeTensorIso` and unit `freeUnitIso⁻¹`. -/
noncomputable def freeLminusLiftCoreMonoidal : (freeLminusLift A S).CoreMonoidal where
  εIso := (toBimod A).essImage.isoMk (freeUnitIso A).symm
  μIso X Y := (toBimod A).essImage.isoMk (freeTensorIso A X.obj Y.obj)
  μIso_hom_natural_left {X _} f X' := by
    apply ObjectProperty.hom_ext
    exact freeTensorIso_natural_left A X.obj X'.obj f.hom
  μIso_hom_natural_right {X _} X' f := by
    apply ObjectProperty.hom_ext
    exact freeTensorIso_natural_right A X'.obj X.obj f.hom
  associativity X Y Z := by
    apply ObjectProperty.hom_ext
    exact freeTensorIso_associativity A X.obj Y.obj Z.obj
  left_unitality X := by
    apply ObjectProperty.hom_ext
    exact freeTensorIso_leftUnitality A X.obj
  right_unitality X := by
    apply ObjectProperty.hom_ext
    exact freeTensorIso_rightUnitality A X.obj

/-- The monoidal structure of `freeLminusLift A S`. -/
@[instance_reducible]
noncomputable def freeLminusLiftMonoidal : (freeLminusLift A S).Monoidal :=
  (freeLminusLiftCoreMonoidal A S).toMonoidal

omit [MonoidalPreadditive C] [(LminusClosure S).IsMonoidal] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- `freeLminusLift A S` is an equivalence as soon as `freeLminus A S` is. -/
theorem freeLminusLift_isEquivalence (hE : (freeLminus A S).IsEquivalence) :
    (freeLminusLift A S).IsEquivalence := by
  have := hE
  have : (toBimod A).Full := (toBimodFullyFaithful A).full
  have : (toBimod A).Faithful := (toBimodFullyFaithful A).faithful
  have hfull : (freeLminusLift A S ⋙ (toBimod A).essImage.ι).Full :=
    (inferInstance : (freeLminus A S ⋙ toBimod A).Full)
  have hfaith : (freeLminusLift A S ⋙ (toBimod A).essImage.ι).Faithful :=
    (inferInstance : (freeLminus A S ⋙ toBimod A).Faithful)
  refine
    { faithful := Functor.Faithful.of_comp _ (toBimod A).essImage.ι
      full := Functor.Full.of_comp_faithful _ (toBimod A).essImage.ι
      essSurj := ⟨fun Y => ?_⟩ }
  obtain ⟨R, ⟨e⟩⟩ := Y.property
  exact ⟨(freeLminus A S).objPreimage R,
    ⟨(toBimod A).essImage.isoMk
      ((toBimod A).mapIso ((freeLminus A S).objObjPreimageIso R) ≪≫ e)⟩⟩

/-- **Induction is a monoidal equivalence** `LminusClosure S ≌ 𝒞_A`: the equivalence of
categories with functor `freeLminusLift A S`. -/
noncomputable def freeLminusMonoidalEquivalence (hE : (freeLminus A S).IsEquivalence) :
    (LminusClosure S).FullSubcategory ≌ (toBimod A).essImage.FullSubcategory :=
  @Functor.asEquivalence _ _ _ _ (freeLminusLift A S) (freeLminusLift_isEquivalence A S hE)

/-- The functor of `freeLminusMonoidalEquivalence` is monoidal. -/
@[instance_reducible]
noncomputable def freeLminusMonoidalEquivalence_functorMonoidal
    (hE : (freeLminus A S).IsEquivalence) :
    (freeLminusMonoidalEquivalence A S hE).functor.Monoidal :=
  freeLminusLiftMonoidal A S

omit [MonoidalPreadditive C] in
set_option backward.isDefEq.respectTransparency false in
/-- **The equivalence is monoidal** in Mathlib's sense: with the monoidal structure on the
functor and the induced one on the inverse, the unit and counit are monoidal.  (This is
automatic once the inverse carries Mathlib's `Equivalence.inverseMonoidal`; it is recorded for
citation.) -/
theorem freeLminusMonoidalEquivalence_isMonoidal (hE : (freeLminus A S).IsEquivalence) :
    letI := freeLminusMonoidalEquivalence_functorMonoidal A S hE
    letI := (freeLminusMonoidalEquivalence A S hE).inverseMonoidal
    (freeLminusMonoidalEquivalence A S hE).IsMonoidal := by
  let := freeLminusMonoidalEquivalence_functorMonoidal A S hE
  let := (freeLminusMonoidalEquivalence A S hE).inverseMonoidal
  infer_instance

end Monoidal

section Summary

variable {S} [MonoidalPreadditive C] (𝕜 : Type*) [Field 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C]
  [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]

/-- **Free `H/B`-module induction is a monoidal equivalence** from the additive closure of
`L₋` onto the module category `𝒞_A` (manuscript lines 3335–3352), under the named hypotheses
of `freeLminus_isEquivalence` and `hunitS : S (0, 0) ≅ 𝟙_ C`: there is an equivalence `e` whose
functor is monoidal, which is a monoidal equivalence (`Equivalence.IsMonoidal`, with the
induced monoidal structure on the inverse), and whose functor is free induction
`freeLminus A S ⋙ toBimod A` (after the inclusion of `𝒞_A` into `Bimod A A`). -/
theorem freeLminus_monoidalEquivalence
    (hSchur : ∀ v w, Module.finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c)) (hmul : ∀ c d : ZMod 3, mulComp hA c d ≠ 0)
    (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j)))
    (hsplit : ∀ (n : ℕ) (a : Fin n → ZMod 3)
      (e : (⨁ fun j => S (a j, -a j)) ⟶ (⨁ fun j => S (a j, -a j))), e ≫ e = e →
        ∃ (m : ℕ) (b : Fin m → ZMod 3)
          (R : Retract (⨁ fun k => S (b k, -b k)) (⨁ fun j => S (a j, -a j))), R.r ≫ R.i = e) :
    haveI := lminusClosure_isMonoidal hfusion hunitS
    ∃ (e : (LminusClosure S).FullSubcategory ≌ (toBimod A).essImage.FullSubcategory)
      (h : e.functor.Monoidal),
        (letI := h; letI := e.inverseMonoidal; e.IsMonoidal) ∧
          e.functor ⋙ (toBimod A).essImage.ι = freeLminus A S ⋙ toBimod A := by
  have := lminusClosure_isMonoidal hfusion hunitS
  have hE := freeLminus_isEquivalence 𝕜 hSchur hfusion hA hmul h3 hss hsplit
  exact ⟨freeLminusMonoidalEquivalence A S hE,
    freeLminusMonoidalEquivalence_functorMonoidal A S hE,
    freeLminusMonoidalEquivalence_isMonoidal A S hE, rfl⟩

/-- The monoidal equivalence from categorical inputs only: `hmul` replaced by `hunit`
(the unit of `A` lies in `S (0, 0)`) and `hnondeg` (nonzero pairing components), and `hsplit`
by `IsIdempotentComplete C` (`Category/TwistedGroupAlgebraOfUnit.lean`). -/
theorem freeLminus_monoidalEquivalence_categorical [IsIdempotentComplete C]
    (hSchur : ∀ v w, Module.finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c))
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0)
    (hnondeg : ∀ d : ZMod 3, mulComp hA d (-d) ≠ 0) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    haveI := lminusClosure_isMonoidal hfusion hunitS
    ∃ (e : (LminusClosure S).FullSubcategory ≌ (toBimod A).essImage.FullSubcategory)
      (h : e.functor.Monoidal),
        (letI := h; letI := e.inverseMonoidal; e.IsMonoidal) ∧
          e.functor ⋙ (toBimod A).essImage.ι = freeLminus A S ⋙ toBimod A := by
  have := lminusClosure_isMonoidal hfusion hunitS
  have hE := freeLminus_isEquivalence_categorical 𝕜 hSchur hfusion hA hunit hnondeg h3 hss
  exact ⟨freeLminusMonoidalEquivalence A S hE,
    freeLminusMonoidalEquivalence_functorMonoidal A S hE,
    freeLminusMonoidalEquivalence_isMonoidal A S hE, rfl⟩

end Summary

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.lminus_biproduct_tensor_mem
#print axioms HaagerupIzumi.C8.RightMod.lminusClosure_isMonoidal
#print axioms HaagerupIzumi.C8.RightMod.essImage_toBimod_isMonoidal
#print axioms HaagerupIzumi.C8.RightMod.freeLminusLiftCoreMonoidal
#print axioms HaagerupIzumi.C8.RightMod.freeLminusLift_isEquivalence
#print axioms HaagerupIzumi.C8.RightMod.freeLminusMonoidalEquivalence
#print axioms HaagerupIzumi.C8.RightMod.freeLminusMonoidalEquivalence_isMonoidal
#print axioms HaagerupIzumi.C8.RightMod.freeLminus_monoidalEquivalence
#print axioms HaagerupIzumi.C8.RightMod.freeLminus_monoidalEquivalence_categorical
