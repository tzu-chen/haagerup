module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor

@[expose] public section

/-! # The double-dual functor of a right rigid monoidal category (DRAFT, not in the source tree)

Status (2026-10-01, moved out of `HaagerupIzumi/C8/Category/` at the user's checkpoint request):
* Section `Pairing` (`ev_injective`, `rightDualIso_hom_ev`, `tensor_ev_whiskerLeft`,
  `tensor_ev_whiskerRight`, `tensor_ev_associator`) passed `c8q check` (exit 0, request
  200052-f796a0).  The `_iso` corollaries were added afterwards and are unchecked.
* Section `Rigid` (the dual-of-tensor isomorphism `rightDualTensorIso` is natural, associative and
  unital; the double-dual functor `doubleDual C`, its tensorator `μIso`, unit `εIso`, the
  `CoreMonoidal` structure and the `Monoidal` instance) has never been compiled: request
  200506-686cdf was still waiting in the shared queue when work stopped.
* To resume: move back to `HaagerupIzumi/C8/Category/DoubleDual.lean`, run `c8q check`, fix
  errors; then write `Category/Pivotal.lean` (pivotal structure = monoidal natural iso
  `𝟭 C ≅ doubleDual C`, uniqueness from `Fusion.IsHIRing.monoidalIso_eq`). -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory ExactPairing

universe v u

namespace DoubleDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section Pairing

/-- Morphisms into a right dual are determined by their pairing with the evaluation. -/
theorem ev_injective {Z A B : C} [ExactPairing A B] {g h : Z ⟶ B}
    (w : g ▷ A ≫ ε_ A B = h ▷ A ≫ ε_ A B) : g = h := by
  have key : ∀ k : Z ⟶ B,
      (tensorRightHomEquiv Z A B (𝟙_ C)) (k ▷ A ≫ ε_ A B) = k ≫ (λ_ B).inv :=
    fun k => @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ A Z ⟨B⟩ k
  have hw := congrArg (tensorRightHomEquiv Z A B (𝟙_ C)) w
  rw [key, key] at hw
  simpa using hw

/-- The canonical isomorphism between two right duals is compatible with the evaluations. -/
theorem rightDualIso_hom_ev {X Y₁ Y₂ : C} (p₁ : ExactPairing X Y₁) (p₂ : ExactPairing X Y₂) :
    (rightDualIso p₁ p₂).hom ▷ X ≫ @ExactPairing.evaluation C _ _ X Y₂ p₂ =
      @ExactPairing.evaluation C _ _ X Y₁ p₁ := by
  have h := @rightAdjointMate_comp_evaluation C _ _ X X ⟨Y₂⟩ ⟨Y₁⟩ (𝟙 X)
  rw [whiskerLeft_id, Category.id_comp] at h
  exact h

/-- Changing the first dual factor of a tensor pairing. -/
theorem tensor_ev_whiskerLeft {X₁ X₁' X₂ Y₁ Y₁' Y₂ : C} [ExactPairing X₁ Y₁]
    [ExactPairing X₁' Y₁'] [ExactPairing X₂ Y₂] (k : Y₁' ⟶ Y₁) (f : X₁ ⟶ X₁')
    (hk : k ▷ X₁ ≫ ε_ X₁ Y₁ = Y₁' ◁ f ≫ ε_ X₁' Y₁') :
    (Y₂ ◁ k) ▷ (X₁ ⊗ X₂) ≫ ε_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) =
      (Y₂ ⊗ Y₁') ◁ (f ▷ X₂) ≫ ε_ (X₁' ⊗ X₂) (Y₂ ⊗ Y₁') := by
  simp only [tensor_evaluation]
  calc _ = 𝟙 _ ⊗≫ Y₂ ◁ ((k ▷ X₁ ≫ ε_ X₁ Y₁) ▷ X₂) ⊗≫ ε_ X₂ Y₂ := by monoidal
    _ = 𝟙 _ ⊗≫ Y₂ ◁ ((Y₁' ◁ f ≫ ε_ X₁' Y₁') ▷ X₂) ⊗≫ ε_ X₂ Y₂ := by rw [hk]
    _ = _ := by monoidal

/-- Changing the second dual factor of a tensor pairing. -/
theorem tensor_ev_whiskerRight {X₁ X₂ X₂' Y₁ Y₂ Y₂' : C} [ExactPairing X₁ Y₁]
    [ExactPairing X₂ Y₂] [ExactPairing X₂' Y₂'] (k : Y₂' ⟶ Y₂) (f : X₂ ⟶ X₂')
    (hk : k ▷ X₂ ≫ ε_ X₂ Y₂ = Y₂' ◁ f ≫ ε_ X₂' Y₂') :
    (k ▷ Y₁) ▷ (X₁ ⊗ X₂) ≫ ε_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) =
      (Y₂' ⊗ Y₁) ◁ (X₁ ◁ f) ≫ ε_ (X₁ ⊗ X₂') (Y₂' ⊗ Y₁) := by
  simp only [tensor_evaluation]
  calc _ = 𝟙 _ ⊗≫ (k ▷ (Y₁ ⊗ X₁) ≫ Y₂ ◁ ε_ X₁ Y₁) ▷ X₂ ⊗≫ ε_ X₂ Y₂ := by monoidal
    _ = 𝟙 _ ⊗≫ (Y₂' ◁ ε_ X₁ Y₁ ≫ k ▷ 𝟙_ C) ▷ X₂ ⊗≫ ε_ X₂ Y₂ := by
      rw [← whisker_exchange]
    _ = 𝟙 _ ⊗≫ Y₂' ◁ (ε_ X₁ Y₁ ▷ X₂) ⊗≫ (k ▷ X₂ ≫ ε_ X₂ Y₂) := by monoidal
    _ = 𝟙 _ ⊗≫ Y₂' ◁ (ε_ X₁ Y₁ ▷ X₂) ⊗≫ (Y₂' ◁ f ≫ ε_ X₂' Y₂') := by rw [hk]
    _ = 𝟙 _ ⊗≫ Y₂' ◁ (ε_ X₁ Y₁ ▷ X₂ ≫ 𝟙_ C ◁ f) ⊗≫ ε_ X₂' Y₂' := by monoidal
    _ = 𝟙 _ ⊗≫ Y₂' ◁ ((Y₁ ⊗ X₁) ◁ f ≫ ε_ X₁ Y₁ ▷ X₂') ⊗≫ ε_ X₂' Y₂' := by
      rw [← whisker_exchange]
    _ = _ := by monoidal

/-- `tensor_ev_whiskerLeft` for two duals of the same object. -/
theorem tensor_ev_whiskerLeft_iso {X₁ X₂ Y₁ Y₁' Y₂ : C} [ExactPairing X₁ Y₁]
    [ExactPairing X₁ Y₁'] [ExactPairing X₂ Y₂] (k : Y₁' ⟶ Y₁)
    (hk : k ▷ X₁ ≫ ε_ X₁ Y₁ = ε_ X₁ Y₁') :
    (Y₂ ◁ k) ▷ (X₁ ⊗ X₂) ≫ ε_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) = ε_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁') := by
  rw [tensor_ev_whiskerLeft k (𝟙 X₁) (by rw [whiskerLeft_id, Category.id_comp]; exact hk)]
  simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp]

/-- `tensor_ev_whiskerRight` for two duals of the same object. -/
theorem tensor_ev_whiskerRight_iso {X₁ X₂ Y₁ Y₂ Y₂' : C} [ExactPairing X₁ Y₁]
    [ExactPairing X₂ Y₂] [ExactPairing X₂ Y₂'] (k : Y₂' ⟶ Y₂)
    (hk : k ▷ X₂ ≫ ε_ X₂ Y₂ = ε_ X₂ Y₂') :
    (k ▷ Y₁) ▷ (X₁ ⊗ X₂) ≫ ε_ (X₁ ⊗ X₂) (Y₂ ⊗ Y₁) = ε_ (X₁ ⊗ X₂) (Y₂' ⊗ Y₁) := by
  rw [tensor_ev_whiskerRight k (𝟙 X₂) (by rw [whiskerLeft_id, Category.id_comp]; exact hk)]
  simp only [whiskerLeft_id, Category.id_comp]

/-- The associator is compatible with the evaluations of iterated tensor pairings. -/
theorem tensor_ev_associator {X Y Z X' Y' Z' : C} [ExactPairing X X'] [ExactPairing Y Y']
    [ExactPairing Z Z'] :
    (α_ Z' Y' X').hom ▷ ((X ⊗ Y) ⊗ Z) ≫ ε_ ((X ⊗ Y) ⊗ Z) (Z' ⊗ (Y' ⊗ X')) =
      ((Z' ⊗ Y') ⊗ X') ◁ (α_ X Y Z).hom ≫ ε_ (X ⊗ (Y ⊗ Z)) ((Z' ⊗ Y') ⊗ X') := by
  simp only [tensor_evaluation]
  monoidal

end Pairing

section Rigid

variable [RightRigidCategory C]

-- In a right rigid category the dual of `𝟙_ C` used below is the chosen one.
attribute [-instance] hasRightDualUnit

/-- `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` is compatible with the evaluations. -/
theorem tensorIso_hom_ev (X Y : C) :
    (rightDualTensorIso X Y).hom ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (Yᘁ ⊗ Xᘁ) =
      ε_ (X ⊗ Y) ((X ⊗ Y)ᘁ) :=
  rightDualIso_hom_ev _ _

/-- Naturality of `(X ⊗ B)ᘁ ≅ Bᘁ ⊗ Xᘁ` in `X`. -/
theorem tensorIso_natural_left {X X' : C} (f : X ⟶ X') (B : C) :
    (f ▷ B)ᘁ ≫ (rightDualTensorIso X B).hom = (rightDualTensorIso X' B).hom ≫ Bᘁ ◁ fᘁ := by
  apply ev_injective (A := X ⊗ B)
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc, tensorIso_hom_ev,
    rightAdjointMate_comp_evaluation,
    tensor_ev_whiskerLeft (fᘁ) f (rightAdjointMate_comp_evaluation f),
    ← whisker_exchange_assoc, tensorIso_hom_ev]

/-- Naturality of `(A ⊗ Y)ᘁ ≅ Yᘁ ⊗ Aᘁ` in `Y`. -/
theorem tensorIso_natural_right (A : C) {Y Y' : C} (g : Y ⟶ Y') :
    (A ◁ g)ᘁ ≫ (rightDualTensorIso A Y).hom = (rightDualTensorIso A Y').hom ≫ gᘁ ▷ Aᘁ := by
  apply ev_injective (A := A ⊗ Y)
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc, tensorIso_hom_ev,
    rightAdjointMate_comp_evaluation,
    tensor_ev_whiskerRight (gᘁ) g (rightAdjointMate_comp_evaluation g),
    ← whisker_exchange_assoc, tensorIso_hom_ev]

/-- Associativity (hexagon) of `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`. -/
theorem tensorIso_assoc (X Y Z : C) :
    (α_ X Y Z).homᘁ ≫ (rightDualTensorIso (X ⊗ Y) Z).hom ≫ Zᘁ ◁ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso X (Y ⊗ Z)).hom ≫ (rightDualTensorIso Y Z).hom ▷ Xᘁ ≫
        (α_ Zᘁ Yᘁ Xᘁ).hom := by
  apply ev_injective (A := (X ⊗ Y) ⊗ Z)
  simp only [comp_whiskerRight, Category.assoc]
  rw [tensor_ev_whiskerLeft_iso _ (tensorIso_hom_ev X Y), tensorIso_hom_ev,
    rightAdjointMate_comp_evaluation, tensor_ev_associator, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, tensor_ev_whiskerRight_iso _ (tensorIso_hom_ev Y Z),
    tensorIso_hom_ev]

/-- The chosen right dual of the unit is isomorphic to the unit. -/
def unitDualIso : (𝟙_ C)ᘁ ≅ 𝟙_ C := rightDualIso HasRightDual.exact exactPairingUnit

theorem unitDualIso_hom_ev :
    unitDualIso.hom ▷ 𝟙_ C ≫ ε_ (𝟙_ C) (𝟙_ C) = ε_ (𝟙_ C) ((𝟙_ C)ᘁ) :=
  rightDualIso_hom_ev _ _

theorem ev_unit : ε_ (𝟙_ C) (𝟙_ C) = (ρ_ (𝟙_ C)).hom := rfl

/-- Left unitality of `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`. -/
theorem tensorIso_unit_left (X : C) :
    (λ_ X).homᘁ ≫ (rightDualTensorIso (𝟙_ C) X).hom ≫ Xᘁ ◁ unitDualIso.hom = (ρ_ Xᘁ).inv := by
  apply ev_injective (A := 𝟙_ C ⊗ X)
  simp only [comp_whiskerRight, Category.assoc]
  rw [tensor_ev_whiskerLeft_iso _ unitDualIso_hom_ev, tensorIso_hom_ev,
    rightAdjointMate_comp_evaluation]
  simp only [tensor_evaluation, ev_unit]
  monoidal

/-- Right unitality of `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`. -/
theorem tensorIso_unit_right (A : C) :
    (ρ_ A).homᘁ ≫ (rightDualTensorIso A (𝟙_ C)).hom ≫ unitDualIso.hom ▷ Aᘁ = (λ_ Aᘁ).inv := by
  apply ev_injective (A := A ⊗ 𝟙_ C)
  simp only [comp_whiskerRight, Category.assoc]
  rw [tensor_ev_whiskerRight_iso _ unitDualIso_hom_ev, tensorIso_hom_ev,
    rightAdjointMate_comp_evaluation]
  simp only [tensor_evaluation, ev_unit]
  monoidal

/-! ### Inverse forms -/

@[reassoc]
theorem tensorIso_natural_left_inv {X X' : C} (f : X ⟶ X') (B : C) :
    Bᘁ ◁ fᘁ ≫ (rightDualTensorIso X B).inv = (rightDualTensorIso X' B).inv ≫ (f ▷ B)ᘁ := by
  rw [Iso.comp_inv_eq, Category.assoc, tensorIso_natural_left, Iso.inv_hom_id_assoc]

@[reassoc]
theorem tensorIso_natural_right_inv (A : C) {Y Y' : C} (g : Y ⟶ Y') :
    gᘁ ▷ Aᘁ ≫ (rightDualTensorIso A Y).inv = (rightDualTensorIso A Y').inv ≫ (A ◁ g)ᘁ := by
  rw [Iso.comp_inv_eq, Category.assoc, tensorIso_natural_right, Iso.inv_hom_id_assoc]

@[reassoc]
theorem tensorIso_assoc_inv (X Y Z : C) :
    (rightDualTensorIso Y Z).inv ▷ Xᘁ ≫ (rightDualTensorIso X (Y ⊗ Z)).inv ≫ (α_ X Y Z).homᘁ =
      (α_ Zᘁ Yᘁ Xᘁ).hom ≫ Zᘁ ◁ (rightDualTensorIso X Y).inv ≫
        (rightDualTensorIso (X ⊗ Y) Z).inv := by
  rw [← cancel_mono ((rightDualTensorIso (X ⊗ Y) Z).hom ≫ Zᘁ ◁ (rightDualTensorIso X Y).hom)]
  simp [tensorIso_assoc]

/-- The adjoint mate of an isomorphism. -/
@[simps]
def dualIso {X Y : C} (i : X ≅ Y) : Yᘁ ≅ Xᘁ where
  hom := i.homᘁ
  inv := i.invᘁ
  hom_inv_id := by rw [← comp_rightAdjointMate, i.inv_hom_id, rightAdjointMate_id]
  inv_hom_id := by rw [← comp_rightAdjointMate, i.hom_inv_id, rightAdjointMate_id]

theorem tensorIso_unit_left_inv (A : C) :
    Aᘁ ◁ unitDualIso.inv ≫ (rightDualTensorIso (𝟙_ C) A).inv ≫ (λ_ A).invᘁ = (ρ_ Aᘁ).hom := by
  rw [← cancel_epi (ρ_ Aᘁ).inv, Iso.inv_hom_id, ← tensorIso_unit_left]
  simp only [Category.assoc, whiskerLeft_hom_inv_assoc, Iso.hom_inv_id_assoc]
  exact (dualIso (λ_ A)).hom_inv_id

theorem tensorIso_unit_right_inv (A : C) :
    unitDualIso.inv ▷ Aᘁ ≫ (rightDualTensorIso A (𝟙_ C)).inv ≫ (ρ_ A).invᘁ = (λ_ Aᘁ).hom := by
  rw [← cancel_epi (λ_ Aᘁ).inv, Iso.inv_hom_id, ← tensorIso_unit_right]
  simp only [Category.assoc, hom_inv_whiskerRight_assoc, Iso.hom_inv_id_assoc]
  exact (dualIso (ρ_ A)).hom_inv_id

/-! ### The double-dual functor -/

variable (C) in
/-- The double-dual functor `X ↦ Xᘁᘁ`, `f ↦ fᘁᘁ`. -/
@[simps]
def doubleDual : C ⥤ C where
  obj X := Xᘁᘁ
  map f := fᘁᘁ
  map_id X := by simp only [rightAdjointMate_id]
  map_comp f g := by simp only [comp_rightAdjointMate]

/-- The tensorator `Xᘁᘁ ⊗ Yᘁᘁ ≅ (X ⊗ Y)ᘁᘁ`: the inverse of `(Yᘁ ⊗ Xᘁ)ᘁ ≅ Xᘁᘁ ⊗ Yᘁᘁ`
followed by the mate of `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ`. -/
def μIso (X Y : C) : Xᘁᘁ ⊗ Yᘁᘁ ≅ (X ⊗ Y)ᘁᘁ :=
  (rightDualTensorIso Yᘁ Xᘁ).symm ≪≫ dualIso (rightDualTensorIso X Y)

theorem μIso_hom (X Y : C) :
    (μIso X Y).hom = (rightDualTensorIso Yᘁ Xᘁ).inv ≫ (rightDualTensorIso X Y).homᘁ := rfl

variable (C) in
/-- The unit `𝟙_ C ≅ (𝟙_ C)ᘁᘁ`. -/
def εIso : 𝟙_ C ≅ (𝟙_ C)ᘁᘁ := unitDualIso.symm ≪≫ dualIso unitDualIso

theorem εIso_hom : (εIso C).hom = unitDualIso.inv ≫ unitDualIso.homᘁ := rfl

theorem μIso_natural_left {X Y : C} (f : X ⟶ Y) (X' : C) :
    fᘁᘁ ▷ X'ᘁᘁ ≫ (μIso Y X').hom = (μIso X X').hom ≫ (f ▷ X')ᘁᘁ := by
  rw [μIso_hom, μIso_hom]
  calc _ = (rightDualTensorIso X'ᘁ Xᘁ).inv ≫ (X'ᘁ ◁ fᘁ)ᘁ ≫ (rightDualTensorIso Y X').homᘁ := by
        rw [← Category.assoc, tensorIso_natural_right_inv, Category.assoc]
    _ = (rightDualTensorIso X'ᘁ Xᘁ).inv ≫
          ((rightDualTensorIso Y X').hom ≫ X'ᘁ ◁ fᘁ)ᘁ := by
        rw [comp_rightAdjointMate]
    _ = (rightDualTensorIso X'ᘁ Xᘁ).inv ≫ ((f ▷ X')ᘁ ≫ (rightDualTensorIso X X').hom)ᘁ := by
        rw [tensorIso_natural_left]
    _ = _ := by rw [comp_rightAdjointMate, Category.assoc]

theorem μIso_natural_right {X Y : C} (X' : C) (f : X ⟶ Y) :
    X'ᘁᘁ ◁ fᘁᘁ ≫ (μIso X' Y).hom = (μIso X' X).hom ≫ (X' ◁ f)ᘁᘁ := by
  rw [μIso_hom, μIso_hom]
  calc _ = (rightDualTensorIso Xᘁ X'ᘁ).inv ≫ (fᘁ ▷ X'ᘁ)ᘁ ≫ (rightDualTensorIso X' Y).homᘁ := by
        rw [← Category.assoc, tensorIso_natural_left_inv, Category.assoc]
    _ = (rightDualTensorIso Xᘁ X'ᘁ).inv ≫
          ((rightDualTensorIso X' Y).hom ≫ fᘁ ▷ X'ᘁ)ᘁ := by
        rw [comp_rightAdjointMate]
    _ = (rightDualTensorIso Xᘁ X'ᘁ).inv ≫ ((X' ◁ f)ᘁ ≫ (rightDualTensorIso X' X).hom)ᘁ := by
        rw [tensorIso_natural_right]
    _ = _ := by rw [comp_rightAdjointMate, Category.assoc]

theorem μIso_assoc (X Y Z : C) :
    (μIso X Y).hom ▷ Zᘁᘁ ≫ (μIso (X ⊗ Y) Z).hom ≫ (α_ X Y Z).homᘁᘁ =
      (α_ Xᘁᘁ Yᘁᘁ Zᘁᘁ).hom ≫ Xᘁᘁ ◁ (μIso Y Z).hom ≫ (μIso X (Y ⊗ Z)).hom := by
  have h1 : (Zᘁ ◁ (rightDualTensorIso X Y).hom)ᘁ ≫ (rightDualTensorIso (X ⊗ Y) Z).homᘁ ≫
      (α_ X Y Z).homᘁᘁ = (α_ Zᘁ Yᘁ Xᘁ).homᘁ ≫ ((rightDualTensorIso Y Z).hom ▷ Xᘁ)ᘁ ≫
        (rightDualTensorIso X (Y ⊗ Z)).homᘁ := by
    calc _ = ((α_ X Y Z).homᘁ ≫ (rightDualTensorIso (X ⊗ Y) Z).hom ≫
          Zᘁ ◁ (rightDualTensorIso X Y).hom)ᘁ := by
          rw [comp_rightAdjointMate, comp_rightAdjointMate, Category.assoc]
      _ = ((rightDualTensorIso X (Y ⊗ Z)).hom ≫ (rightDualTensorIso Y Z).hom ▷ Xᘁ ≫
          (α_ Zᘁ Yᘁ Xᘁ).hom)ᘁ := by rw [tensorIso_assoc]
      _ = _ := by rw [comp_rightAdjointMate, comp_rightAdjointMate, Category.assoc]
  simp only [μIso_hom, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [tensorIso_natural_right_inv_assoc, h1, tensorIso_assoc_inv_assoc,
    tensorIso_natural_left_inv_assoc]

theorem μIso_unit_left (X : C) :
    (λ_ Xᘁᘁ).hom = (εIso C).hom ▷ Xᘁᘁ ≫ (μIso (𝟙_ C) X).hom ≫ (λ_ X).homᘁᘁ := by
  have h2 : (Xᘁ ◁ unitDualIso.hom)ᘁ ≫ (rightDualTensorIso (𝟙_ C) X).homᘁ ≫ (λ_ X).homᘁᘁ =
      (ρ_ Xᘁ).invᘁ := by
    calc _ = ((λ_ X).homᘁ ≫ (rightDualTensorIso (𝟙_ C) X).hom ≫ Xᘁ ◁ unitDualIso.hom)ᘁ := by
          rw [comp_rightAdjointMate, comp_rightAdjointMate, Category.assoc]
      _ = _ := by rw [tensorIso_unit_left]
  simp only [εIso_hom, μIso_hom, comp_whiskerRight, Category.assoc]
  rw [tensorIso_natural_right_inv_assoc, h2, tensorIso_unit_right_inv]

theorem μIso_unit_right (X : C) :
    (ρ_ Xᘁᘁ).hom = Xᘁᘁ ◁ (εIso C).hom ≫ (μIso X (𝟙_ C)).hom ≫ (ρ_ X).homᘁᘁ := by
  have h3 : (unitDualIso.hom ▷ Xᘁ)ᘁ ≫ (rightDualTensorIso X (𝟙_ C)).homᘁ ≫ (ρ_ X).homᘁᘁ =
      (λ_ Xᘁ).invᘁ := by
    calc _ = ((ρ_ X).homᘁ ≫ (rightDualTensorIso X (𝟙_ C)).hom ≫ unitDualIso.hom ▷ Xᘁ)ᘁ := by
          rw [comp_rightAdjointMate, comp_rightAdjointMate, Category.assoc]
      _ = _ := by rw [tensorIso_unit_right]
  simp only [εIso_hom, μIso_hom, MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [tensorIso_natural_left_inv_assoc, h3, tensorIso_unit_left_inv]

/-- The double dual is a monoidal functor, with tensorator `μIso` and unit `εIso`. -/
def coreMonoidal : (doubleDual C).CoreMonoidal where
  εIso := εIso C
  μIso := μIso
  μIso_hom_natural_left f X' := μIso_natural_left f X'
  μIso_hom_natural_right X' f := μIso_natural_right X' f
  associativity X Y Z := μIso_assoc X Y Z
  left_unitality X := μIso_unit_left X
  right_unitality X := μIso_unit_right X

instance : (doubleDual C).Monoidal := coreMonoidal.toMonoidal

theorem doubleDual_ε : Functor.LaxMonoidal.ε (doubleDual C) = (εIso C).hom := rfl

theorem doubleDual_μ (X Y : C) : Functor.LaxMonoidal.μ (doubleDual C) X Y = (μIso X Y).hom := rfl

end Rigid

end DoubleDual

end HaagerupIzumi.C8
