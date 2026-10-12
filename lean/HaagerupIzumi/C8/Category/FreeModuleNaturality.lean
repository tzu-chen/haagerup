module

public import HaagerupIzumi.C8.Category.FreeModuleTensor

@[expose] public section

/-! # Naturality of the tensorator of free induction

Continuation of `Category/FreeModuleTensor.lean`, toward the first sentence of the
identification step of `L_untwisted` (manuscript `haagerup_c8_expanded.tex`, lines
3337–3338): "Free `H/B`-module induction is tensor on this subcategory."  For a commutative
algebra `A` in a braided monoidal category `C`, the bimodule isomorphism
`freeTensorIso A X Y : (X ⊗ A) ⊗_A (Y ⊗ A) ≅ (X ⊗ Y) ⊗ A` is natural in `X`
(`freeTensorIso_natural_left`) and in `Y` (`freeTensorIso_natural_right`), the relative tensor
product of morphisms being Mathlib's whiskerings `Bimod.whiskerRight`, `Bimod.whiskerLeft`
in the bicategory of bimodules.

Proof: `freeTensorIso` is `freeTensorXIso` followed by the associator
(`freeTensorIso_hom_hom`); `freeTensorXIso` is natural in `X` and in the bimodule
(`freeTensorXIso_whiskerRight`, `freeTensorXIso_whiskerLeft`), and the associator is natural.

Hypotheses: those of `Category/FreeModuleTensor.lean` (`C` has coequalizers, `X ⊗ -` and
`- ⊗ X` preserve them, `A` commutative).  No external-theorem or certificate inputs. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

variable [BraidedCategory C] (A : Mon C) [IsCommMonObj A.X] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] (X Y : C)

set_option backward.isDefEq.respectTransparency false in
/-- `freeTensorIso` is natural in `X`. -/
theorem freeTensorIso_natural_left {X' : C} (f : X ⟶ X') :
    Bimod.whiskerRight ((toBimod A).map (freeMap A f)) ((toBimod A).obj (free A Y)) ≫
        (freeTensorIso A X' Y).hom =
      (freeTensorIso A X Y).hom ≫ (toBimod A).map (freeMap A (f ▷ Y)) := by
  apply Bimod.hom_ext
  have h : (Bimod.whiskerRight ((toBimod A).map (freeMap A f))
        ((toBimod A).obj (free A Y))).hom ≫
        (freeTensorXIso A X' ((toBimod A).obj (free A Y))).hom =
      (freeTensorXIso A X ((toBimod A).obj (free A Y))).hom ≫ f ▷ (Y ⊗ A.X) :=
    freeTensorXIso_whiskerRight A X ((toBimod A).obj (free A Y)) f
  rw [Bimod.comp_hom', Bimod.comp_hom', freeTensorIso_hom_hom, freeTensorIso_hom_hom]
  exact (Category.assoc _ _ (α_ X' Y A.X).inv).symm.trans
    ((congrArg (· ≫ (α_ X' Y A.X).inv) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg ((freeTensorXIso A X ((toBimod A).obj (free A Y))).hom ≫ ·)
          (MonoidalCategory.associator_inv_naturality_left f Y A.X)).trans
          (Category.assoc _ _ _).symm)))

set_option backward.isDefEq.respectTransparency false in
/-- `freeTensorIso` is natural in `Y`. -/
theorem freeTensorIso_natural_right {Y' : C} (g : Y ⟶ Y') :
    Bimod.whiskerLeft ((toBimod A).obj (free A X)) ((toBimod A).map (freeMap A g)) ≫
        (freeTensorIso A X Y').hom =
      (freeTensorIso A X Y).hom ≫ (toBimod A).map (freeMap A (X ◁ g)) := by
  apply Bimod.hom_ext
  have h : (Bimod.whiskerLeft ((toBimod A).obj (free A X))
        ((toBimod A).map (freeMap A g))).hom ≫
        (freeTensorXIso A X ((toBimod A).obj (free A Y'))).hom =
      (freeTensorXIso A X ((toBimod A).obj (free A Y))).hom ≫ X ◁ (g ▷ A.X) :=
    freeTensorXIso_whiskerLeft A X ((toBimod A).map (freeMap A g))
  rw [Bimod.comp_hom', Bimod.comp_hom', freeTensorIso_hom_hom, freeTensorIso_hom_hom]
  exact (Category.assoc _ _ (α_ X Y' A.X).inv).symm.trans
    ((congrArg (· ≫ (α_ X Y' A.X).inv) h).trans
      ((Category.assoc _ _ _).trans
        ((congrArg ((freeTensorXIso A X ((toBimod A).obj (free A Y))).hom ≫ ·)
          (MonoidalCategory.associator_inv_naturality_middle X g A.X)).trans
          (Category.assoc _ _ _).symm)))

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.freeTensorIso_natural_left
#print axioms HaagerupIzumi.C8.RightMod.freeTensorIso_natural_right
