module

public import HaagerupIzumi.C8.Category.FreeModule
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.EpiMono

@[expose] public section

/-! # Separability: every module is a summand of a free module

The last categorical step of the proof of `L_untwisted` (manuscript `haagerup_c8_expanded.tex`,
lines 3345–3347): "Every free module is a direct sum of these three simple modules, and
separability makes every module a summand of a free module."

* `SeparabilitySection A`: a separability structure on a monoid object `A` of a monoidal
  category `C`, i.e. a morphism `sep : A ⟶ A ⊗ A` with `sep ≫ μ = 𝟙` that is a morphism of
  `A`-bimodules (`μ ≫ sep = (sep ▷ A) ≫ α ≫ (A ◁ μ)` and
  `μ ≫ sep = (A ◁ sep) ≫ α⁻¹ ≫ (μ ▷ A)`).  This is the definition of a separable algebra
  (for `H/B` it is supplied by the normalized separability idempotent of a connected étale
  algebra in a fusion category; for a twisted group algebra, the shape of `H/B`, the section
  is constructed in `Category/FreeModuleTwistedSeparable.lean`,
  `RightMod.twistedSeparabilitySection`).
* `sepSplit hS M : M ⟶ M ⊗ A`, `m ↦ m · sep(1)`, satisfies `sepSplit ≫ act = 𝟙`
  (`sepSplit_act`) and is a module map (`act_sepSplit`, `sepSplit_whiskerRight_freeAct`:
  both sides equal `m ⊗ a ↦ m · sep(a)`, by left resp. right `A`-linearity of `sep`).
* `retractFree hS M : Retract M (free A M.X)`: **every right `A`-module is a retract, in
  `𝒞_A`, of the free module on its underlying object**, with retraction the action
  `actHom M`; `isSplitEpi_counit`: the counit of the free-module adjunction is a split
  epimorphism.

No hypotheses beyond the monoidal structure, the monoid axioms and the separability
section; no external-theorem or certificate inputs. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A separability structure on a monoid object `A`: an `A`-bimodule section
`sep : A ⟶ A ⊗ A` of the multiplication. -/
structure SeparabilitySection (A : Mon C) where
  /-- The section of the multiplication. -/
  sep : A.X ⟶ A.X ⊗ A.X
  /-- `μ ∘ sep = 𝟙`. -/
  sep_mul : sep ≫ μ[A.X] = 𝟙 A.X
  /-- Right `A`-linearity: `sep(a b) = sep(a) b`. -/
  mul_sep_right : μ[A.X] ≫ sep = sep ▷ A.X ≫ (α_ A.X A.X A.X).hom ≫ A.X ◁ μ[A.X]
  /-- Left `A`-linearity: `sep(a b) = a sep(b)`. -/
  mul_sep_left : μ[A.X] ≫ sep = A.X ◁ sep ≫ (α_ A.X A.X A.X).inv ≫ μ[A.X] ▷ A.X

namespace RightMod

variable {A : Mon C}

/-- Interchange of the action on the first two factors with the multiplication on the last
two: `((m a) b) c ↦ (m a)(b c)`. -/
theorem act_whiskerRight_whiskerRight_mul (M : RightMod A) :
    (M.act ▷ A.X) ▷ A.X ≫ (α_ M.X A.X A.X).hom ≫ M.X ◁ μ[A.X] =
      (α_ (M.X ⊗ A.X) A.X A.X).hom ≫ (M.X ⊗ A.X) ◁ μ[A.X] ≫ M.act ▷ A.X := by
  rw [MonoidalCategory.associator_naturality_left_assoc, ← MonoidalCategory.whisker_exchange]

/-- The action `M ⊗ A ⟶ M` intertwines the free action and the action of `M`. -/
theorem freeAct_act (M : RightMod A) : freeAct A M.X ≫ M.act = M.act ▷ A.X ≫ M.act := by
  unfold freeAct
  rw [Category.assoc, act_whiskerRight_act]

/-- The action as a module map `M ⊗ A ⟶ M` (the counit of the free-module adjunction). -/
def actHom (M : RightMod A) : free A M.X ⟶ M :=
  ⟨M.act, freeAct_act M⟩

variable (hS : SeparabilitySection A)

/-- The splitting `m ↦ m · sep(1)` of the action. -/
def sepSplit (M : RightMod A) : M.X ⟶ M.X ⊗ A.X :=
  (ρ_ M.X).inv ≫ M.X ◁ η[A.X] ≫ M.X ◁ hS.sep ≫ (α_ M.X A.X A.X).inv ≫ M.act ▷ A.X

/-- `(m · sep(1)) · μ = m`: the splitting is a section of the action. -/
theorem sepSplit_act (M : RightMod A) : sepSplit hS M ≫ M.act = 𝟙 M.X := by
  unfold sepSplit
  have h : M.X ◁ hS.sep ≫ M.X ◁ μ[A.X] = 𝟙 _ := by
    rw [← MonoidalCategory.whiskerLeft_comp, hS.sep_mul, MonoidalCategory.whiskerLeft_id]
  simp only [Category.assoc]
  rw [act_whiskerRight_act, Iso.inv_hom_id_assoc, reassoc_of% h, M.act_one, Iso.inv_hom_id]

/-- `(m a) · sep(1) = m · sep(a)`, by left `A`-linearity of `sep`. -/
theorem act_sepSplit (M : RightMod A) :
    M.act ≫ sepSplit hS M = M.X ◁ hS.sep ≫ (α_ M.X A.X A.X).inv ≫ M.act ▷ A.X := by
  calc M.act ≫ (ρ_ M.X).inv ≫ M.X ◁ η[A.X] ≫ M.X ◁ hS.sep ≫ (α_ M.X A.X A.X).inv ≫
        M.act ▷ A.X
      = (ρ_ (M.X ⊗ A.X)).inv ≫ (M.X ⊗ A.X) ◁ η[A.X] ≫ (M.X ⊗ A.X) ◁ hS.sep ≫
          M.act ▷ (A.X ⊗ A.X) ≫ (α_ M.X A.X A.X).inv ≫ M.act ▷ A.X := by
        rw [MonoidalCategory.rightUnitor_inv_naturality_assoc,
          ← MonoidalCategory.whisker_exchange_assoc, ← MonoidalCategory.whisker_exchange_assoc]
    _ = (ρ_ (M.X ⊗ A.X)).inv ≫ (M.X ⊗ A.X) ◁ η[A.X] ≫ (M.X ⊗ A.X) ◁ hS.sep ≫
          (α_ (M.X ⊗ A.X) A.X A.X).inv ≫ (M.act ▷ A.X ≫ M.act) ▷ A.X := by
        rw [MonoidalCategory.associator_inv_naturality_left_assoc,
          ← MonoidalCategory.comp_whiskerRight]
    _ = (ρ_ (M.X ⊗ A.X)).inv ≫ (M.X ⊗ A.X) ◁ η[A.X] ≫ (M.X ⊗ A.X) ◁ hS.sep ≫
          (α_ (M.X ⊗ A.X) A.X A.X).inv ≫
          ((α_ M.X A.X A.X).hom ≫ M.X ◁ μ[A.X] ≫ M.act) ▷ A.X := by
        rw [act_whiskerRight_act]
    _ = M.X ◁ ((ρ_ A.X).inv ≫ A.X ◁ η[A.X] ≫ A.X ◁ hS.sep ≫ (α_ A.X A.X A.X).inv ≫
          μ[A.X] ▷ A.X) ≫ (α_ M.X A.X A.X).inv ≫ M.act ▷ A.X := by
        monoidal
    _ = M.X ◁ ((ρ_ A.X).inv ≫ A.X ◁ η[A.X] ≫ μ[A.X] ≫ hS.sep) ≫ (α_ M.X A.X A.X).inv ≫
          M.act ▷ A.X := by
        rw [← hS.mul_sep_left]
    _ = M.X ◁ hS.sep ≫ (α_ M.X A.X A.X).inv ≫ M.act ▷ A.X := by
        rw [MonObj.mul_one_assoc, Iso.inv_hom_id_assoc]

/-- `(m · sep(1)) · a = m · sep(a)` in the free module, by right `A`-linearity of `sep`. -/
theorem sepSplit_whiskerRight_freeAct (M : RightMod A) :
    sepSplit hS M ▷ A.X ≫ freeAct A M.X =
      M.X ◁ hS.sep ≫ (α_ M.X A.X A.X).inv ≫ M.act ▷ A.X := by
  calc ((ρ_ M.X).inv ≫ M.X ◁ η[A.X] ≫ M.X ◁ hS.sep ≫ (α_ M.X A.X A.X).inv ≫
        M.act ▷ A.X) ▷ A.X ≫ (α_ M.X A.X A.X).hom ≫ M.X ◁ μ[A.X]
      = ((ρ_ M.X).inv ≫ M.X ◁ η[A.X] ≫ M.X ◁ hS.sep ≫ (α_ M.X A.X A.X).inv) ▷ A.X ≫
          (M.act ▷ A.X) ▷ A.X ≫ (α_ M.X A.X A.X).hom ≫ M.X ◁ μ[A.X] := by
        simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = ((ρ_ M.X).inv ≫ M.X ◁ η[A.X] ≫ M.X ◁ hS.sep ≫ (α_ M.X A.X A.X).inv) ▷ A.X ≫
          (α_ (M.X ⊗ A.X) A.X A.X).hom ≫ (M.X ⊗ A.X) ◁ μ[A.X] ≫ M.act ▷ A.X := by
        rw [act_whiskerRight_whiskerRight_mul]
    _ = M.X ◁ ((λ_ A.X).inv ≫ η[A.X] ▷ A.X ≫ hS.sep ▷ A.X ≫ (α_ A.X A.X A.X).hom ≫
          A.X ◁ μ[A.X]) ≫ (α_ M.X A.X A.X).inv ≫ M.act ▷ A.X := by
        monoidal
    _ = M.X ◁ ((λ_ A.X).inv ≫ η[A.X] ▷ A.X ≫ μ[A.X] ≫ hS.sep) ≫ (α_ M.X A.X A.X).inv ≫
          M.act ▷ A.X := by
        rw [← hS.mul_sep_right]
    _ = M.X ◁ hS.sep ≫ (α_ M.X A.X A.X).inv ≫ M.act ▷ A.X := by
        rw [MonObj.one_mul_assoc, Iso.inv_hom_id_assoc]

/-- The splitting as a module map `M ⟶ M ⊗ A`. -/
def sepSplitHom (M : RightMod A) : M ⟶ free A M.X :=
  ⟨sepSplit hS M, (act_sepSplit hS M).trans (sepSplit_whiskerRight_freeAct hS M).symm⟩

/-- **Separability makes every module a summand of a free module** (manuscript
lines 3345–3347): every right `A`-module `M` is a retract, in `𝒞_A`, of the free module
`M ⊗ A`, with retraction the action. -/
def retractFree (M : RightMod A) : Retract M (free A M.X) where
  i := sepSplitHom hS M
  r := actHom M
  retract := hom_ext (sepSplit_act hS M)

include hS in
/-- The counit `M ⊗ A ⟶ M` of the free-module adjunction is a split epimorphism. -/
theorem isSplitEpi_counit (M : RightMod A) :
    IsSplitEpi ((freeAdjunction A).counit.app M) :=
  IsSplitEpi.mk' ⟨sepSplitHom hS M, hom_ext
    ((congrArg (fun φ : M.X ⊗ A.X ⟶ M.X => sepSplit hS M ≫ φ)
      (freeAdjunction_counit_app_hom A M)).trans (sepSplit_act hS M))⟩

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.sepSplit_act
#print axioms HaagerupIzumi.C8.RightMod.act_sepSplit
#print axioms HaagerupIzumi.C8.RightMod.sepSplit_whiskerRight_freeAct
#print axioms HaagerupIzumi.C8.RightMod.sepSplitHom
#print axioms HaagerupIzumi.C8.RightMod.retractFree
#print axioms HaagerupIzumi.C8.RightMod.isSplitEpi_counit
