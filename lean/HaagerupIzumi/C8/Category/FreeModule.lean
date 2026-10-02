module

public import HaagerupIzumi.C8.Category.BraidedModules
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

@[expose] public section

/-! # Free modules over an algebra object and the free-module adjunction

Categorical input of the paragraph identifying the all-module category of `H/B` with the
untwisted `Vec_{ℤ/3}` (proof of `L_untwisted`, manuscript `haagerup_c8_expanded.tex`,
lines 3327–3352): "Free `H/B`-module induction is tensor on this subcategory.  It is fully
faithful since `Hom_{H/B}(x ⊗ (H/B), y ⊗ (H/B)) ≅ Hom_{Rep(B)}(x, y ⊗ (H/B))` ...".

Mathlib has module objects (`Mod`, left actions) but no free-module functor; we work with
the project's right modules `RightMod A` (`Category/BraidedModules.lean`), matching the
manuscript's `x ⊗ (H/B)`.  For a monoid object `A` of a monoidal category `C`:

* `RightMod.free A X`: the free right module `X ⊗ A` with action `(x ⊗ a) · b = x ⊗ ab`
  (`freeAct`); `freeFunctor A : C ⥤ RightMod A` and `RightMod.forget A : RightMod A ⥤ C`
  (not to be confused with `CategoryTheory.forget`).
* `freeHomEquiv A X M : (free A X ⟶ M) ≃ (X ⟶ M.X)`, `g ↦ (x ↦ x ⊗ 1) ≫ g`, with inverse
  `f ↦ (f ▷ A) ≫ act` (**the free-module adjunction**), and `freeAdjunction A :
  freeFunctor A ⊣ forget A`, with unit `freeUnit A X = ρ⁻¹ ≫ X ◁ η`
  (`freeAdjunction_unit_app`) and counit the action (`freeAdjunction_counit_app_hom`).
* `freeHomEquivFree`: `Hom_A(X ⊗ A, Y ⊗ A) ≃ Hom_C(X, Y ⊗ A)` (the displayed isomorphism).
* `freeFunctor_map_injective`: if the unit `η` of `A` is a split monomorphism
  (`η ≫ ε = 𝟙`), free induction is faithful.
* For `C` preadditive (resp. `𝕜`-linear) with additive (resp. linear) whiskering,
  `RightMod A` is preadditive (resp. `𝕜`-linear); `freeHomLinearEquiv` is the adjunction
  bijection as a `𝕜`-linear equivalence, `freeMapLinear` is free induction on morphisms as
  a `𝕜`-linear map, and `finrank_hom_free`:
  `dim Hom_A(X ⊗ A, Y ⊗ A) = dim Hom_C(X, Y ⊗ A)`.

No hypotheses beyond the monoidal (preadditive, linear) structure and the monoid axioms;
no external-theorem or certificate inputs.  Companion files: `Category/FreeModuleUntwisted.lean`
(the Hom count `δ_{x,y}` on `L₋` and full faithfulness there),
`Category/FreeModuleSeparable.lean` (every module is a retract of a free module),
`Category/FreeModuleTensor.lean` (the tensorator `(X ⊗ A) ⊗_A (Y ⊗ A) ≅ (X ⊗ Y) ⊗ A` on
objects, its naturality, and the unit isomorphism `𝟙 ⊗ A ≅ A`). -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

section Basic

variable {A : Mon C}

@[ext]
theorem hom_ext {M N : RightMod A} {f g : M ⟶ N} (h : f.hom = g.hom) : f = g :=
  Hom.ext h

theorem hom_injective {M N : RightMod A} :
    Function.Injective (fun f : M ⟶ N => f.hom) :=
  fun _ _ h => Hom.ext h

@[simp]
theorem id_hom' (M : RightMod A) : (𝟙 M : M ⟶ M).hom = 𝟙 M.X := rfl

@[simp]
theorem comp_hom' {M N P : RightMod A} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

/-- Associativity of a right action in the form `(m · a) · b = m · (a b)`. -/
@[reassoc]
theorem act_whiskerRight_act (M : RightMod A) :
    M.act ▷ A.X ≫ M.act = (α_ M.X A.X A.X).hom ≫ M.X ◁ μ[A.X] ≫ M.act := by
  rw [M.act_assoc, Iso.hom_inv_id_assoc]

end Basic

section Free

variable (A : Mon C)

/-- The action of the free module `X ⊗ A`: `(x ⊗ a) · b = x ⊗ ab`. -/
def freeAct (X : C) : (X ⊗ A.X) ⊗ A.X ⟶ X ⊗ A.X :=
  (α_ X A.X A.X).hom ≫ X ◁ μ[A.X]

theorem freeAct_one (X : C) :
    (X ⊗ A.X) ◁ η[A.X] ≫ freeAct A X = (ρ_ (X ⊗ A.X)).hom := by
  unfold freeAct
  calc (X ⊗ A.X) ◁ η[A.X] ≫ (α_ X A.X A.X).hom ≫ X ◁ μ[A.X]
      = (α_ X A.X (𝟙_ C)).hom ≫ X ◁ (A.X ◁ η[A.X] ≫ μ[A.X]) := by monoidal
    _ = (ρ_ (X ⊗ A.X)).hom := by rw [MonObj.mul_one]; monoidal

theorem freeAct_assoc (X : C) :
    (X ⊗ A.X) ◁ μ[A.X] ≫ freeAct A X =
      (α_ (X ⊗ A.X) A.X A.X).inv ≫ freeAct A X ▷ A.X ≫ freeAct A X := by
  unfold freeAct
  calc (X ⊗ A.X) ◁ μ[A.X] ≫ (α_ X A.X A.X).hom ≫ X ◁ μ[A.X]
      = (α_ X A.X (A.X ⊗ A.X)).hom ≫ X ◁ (A.X ◁ μ[A.X] ≫ μ[A.X]) := by monoidal
    _ = (α_ X A.X (A.X ⊗ A.X)).hom ≫
          X ◁ ((α_ A.X A.X A.X).inv ≫ μ[A.X] ▷ A.X ≫ μ[A.X]) := by
        rw [MonObj.mul_assoc_flip]
    _ = (α_ (X ⊗ A.X) A.X A.X).inv ≫ ((α_ X A.X A.X).hom ≫ X ◁ μ[A.X]) ▷ A.X ≫
          (α_ X A.X A.X).hom ≫ X ◁ μ[A.X] := by monoidal

/-- The free right `A`-module `X ⊗ A` on an object `X` (manuscript: `x ⊗ (H/B)`). -/
def free (X : C) : RightMod A where
  X := X ⊗ A.X
  act := freeAct A X
  act_one := freeAct_one A X
  act_assoc := freeAct_assoc A X

theorem free_X (X : C) : (free A X).X = X ⊗ A.X := rfl

@[simp]
theorem free_act (X : C) : (free A X).act = freeAct A X := rfl

theorem freeAct_whiskerRight {X Y : C} (f : X ⟶ Y) :
    freeAct A X ≫ f ▷ A.X = (f ▷ A.X) ▷ A.X ≫ freeAct A Y := by
  unfold freeAct
  rw [Category.assoc, MonoidalCategory.whisker_exchange,
    MonoidalCategory.associator_naturality_left_assoc]

/-- Free induction on morphisms: `f ↦ f ⊗ A`. -/
def freeMap {X Y : C} (f : X ⟶ Y) : free A X ⟶ free A Y :=
  ⟨f ▷ A.X, freeAct_whiskerRight A f⟩

@[simp]
theorem freeMap_hom {X Y : C} (f : X ⟶ Y) : (freeMap A f).hom = f ▷ A.X := rfl

/-- Free induction `X ↦ X ⊗ A` as a functor `C ⥤ 𝒞_A`. -/
@[simps]
def freeFunctor : C ⥤ RightMod A where
  obj X := free A X
  map f := freeMap A f
  map_id X := hom_ext (MonoidalCategory.id_whiskerRight X A.X)
  map_comp f g := hom_ext (MonoidalCategory.comp_whiskerRight f g A.X)

/-- The forgetful functor `𝒞_A ⥤ C`.  (Inside `namespace RightMod` the name `forget` refers to
this functor; outside, write `RightMod.forget A` to avoid confusion with
`CategoryTheory.forget`.) -/
@[simps]
def forget : RightMod A ⥤ C where
  obj M := M.X
  map f := f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The unit `X ⟶ X ⊗ A` of free induction, `x ↦ x ⊗ 1`. -/
def freeUnit (X : C) : X ⟶ X ⊗ A.X :=
  (ρ_ X).inv ≫ X ◁ η[A.X]

/-- Naturality of the unit: `f x ⊗ 1 = (f ⊗ A)(x ⊗ 1)`. -/
@[reassoc]
theorem freeUnit_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ freeUnit A Y = freeUnit A X ≫ f ▷ A.X := by
  unfold freeUnit
  rw [Category.assoc, MonoidalCategory.whisker_exchange,
    MonoidalCategory.rightUnitor_inv_naturality_assoc]

/-- Triangle identity: `(x ⊗ 1) · a = x ⊗ a`. -/
@[reassoc]
theorem freeUnit_whiskerRight_freeAct (X : C) :
    freeUnit A X ▷ A.X ≫ freeAct A X = 𝟙 (X ⊗ A.X) := by
  unfold freeUnit freeAct
  calc ((ρ_ X).inv ≫ X ◁ η[A.X]) ▷ A.X ≫ (α_ X A.X A.X).hom ≫ X ◁ μ[A.X]
      = (ρ_ X).inv ▷ A.X ≫ (α_ X (𝟙_ C) A.X).hom ≫ X ◁ (η[A.X] ▷ A.X ≫ μ[A.X]) := by
        monoidal
    _ = 𝟙 (X ⊗ A.X) := by rw [MonObj.one_mul]; monoidal

/-- The extension `(f ▷ A) ≫ act` of `f : X ⟶ M` is a module map. -/
theorem freeLift_comm {X : C} (M : RightMod A) (f : X ⟶ M.X) :
    freeAct A X ≫ f ▷ A.X ≫ M.act = (f ▷ A.X ≫ M.act) ▷ A.X ≫ M.act := by
  unfold freeAct
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [act_whiskerRight_act, MonoidalCategory.associator_naturality_left_assoc,
    MonoidalCategory.whisker_exchange_assoc]

/-- A morphism `φ : X ⊗ A ⟶ M` intertwining the actions is the extension of its restriction
`x ↦ φ(x ⊗ 1)`. -/
theorem freeUnit_lift {X : C} (M : RightMod A) (φ : X ⊗ A.X ⟶ M.X)
    (hφ : freeAct A X ≫ φ = φ ▷ A.X ≫ M.act) :
    (freeUnit A X ≫ φ) ▷ A.X ≫ M.act = φ := by
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc, ← hφ,
    freeUnit_whiskerRight_freeAct_assoc]

/-- **The free-module adjunction** as a bijection: module maps `X ⊗ A ⟶ M` correspond to
morphisms `X ⟶ M` of `C`, by restriction along `x ↦ x ⊗ 1`; the inverse sends `f` to
`x ⊗ a ↦ f(x) · a`. -/
def freeHomEquiv (X : C) (M : RightMod A) : (free A X ⟶ M) ≃ (X ⟶ M.X) where
  toFun g := freeUnit A X ≫ g.hom
  invFun f := ⟨f ▷ A.X ≫ M.act, freeLift_comm A M f⟩
  left_inv g := hom_ext (freeUnit_lift A M g.hom g.act_hom)
  right_inv f := by
    show freeUnit A X ≫ f ▷ A.X ≫ M.act = f
    unfold freeUnit
    rw [Category.assoc, MonoidalCategory.whisker_exchange_assoc, M.act_one,
      ← MonoidalCategory.rightUnitor_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

theorem freeHomEquiv_apply (X : C) (M : RightMod A) (g : free A X ⟶ M) :
    freeHomEquiv A X M g = freeUnit A X ≫ g.hom := rfl

theorem freeHomEquiv_symm_apply_hom (X : C) (M : RightMod A) (f : X ⟶ M.X) :
    ((freeHomEquiv A X M).symm f).hom = f ▷ A.X ≫ M.act := rfl

/-- **The free-module adjunction** `free ⊣ forget` between `C` and `𝒞_A`. -/
def freeAdjunction : freeFunctor A ⊣ forget A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X M => freeHomEquiv A X M
      homEquiv_naturality_left_symm := fun {X' X M} f g => by
        apply hom_ext
        show (f ≫ g) ▷ A.X ≫ M.act = f ▷ A.X ≫ g ▷ A.X ≫ M.act
        rw [MonoidalCategory.comp_whiskerRight]
        exact Category.assoc _ _ _
      homEquiv_naturality_right := fun {X M M'} g h =>
        (Category.assoc (freeUnit A X) g.hom h.hom).symm }

theorem freeAdjunction_homEquiv (X : C) (M : RightMod A) :
    (freeAdjunction A).homEquiv X M = freeHomEquiv A X M :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) X) M

/-- The unit of the free-module adjunction is `x ↦ x ⊗ 1`. -/
theorem freeAdjunction_unit_app (X : C) : (freeAdjunction A).unit.app X = freeUnit A X := by
  rw [← Adjunction.homEquiv_id, freeAdjunction_homEquiv]
  exact Category.comp_id (freeUnit A X)

/-- The counit of the free-module adjunction is the action `M ⊗ A ⟶ M`. -/
theorem freeAdjunction_counit_app_hom (M : RightMod A) :
    ((freeAdjunction A).counit.app M).hom = M.act := by
  rw [← Adjunction.homEquiv_symm_id, freeAdjunction_homEquiv]
  show 𝟙 M.X ▷ A.X ≫ M.act = M.act
  rw [MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- The manuscript's displayed isomorphism `Hom_A(X ⊗ A, Y ⊗ A) ≅ Hom_C(X, Y ⊗ A)`
(lines 3340–3343). -/
def freeHomEquivFree (X Y : C) : (free A X ⟶ free A Y) ≃ (X ⟶ Y ⊗ A.X) :=
  freeHomEquiv A X (free A Y)

/-- Under the adjunction bijection, free induction of `f : X ⟶ Y` corresponds to
`f ≫ (y ↦ y ⊗ 1)`. -/
theorem freeHomEquiv_freeMap {X Y : C} (f : X ⟶ Y) :
    freeHomEquiv A X (free A Y) (freeMap A f) = f ≫ freeUnit A Y :=
  (freeUnit_naturality A f).symm

/-- If the unit of `A` is a split monomorphism (`η ≫ ε = 𝟙`; for a connected separable
algebra in a semisimple category with simple unit this holds), free induction is faithful:
`f` is recovered from `f ⊗ A`. -/
theorem freeFunctor_map_injective (ε : A.X ⟶ 𝟙_ C) (hε : η[A.X] ≫ ε = 𝟙 (𝟙_ C)) {X Y : C} :
    Function.Injective (fun f : X ⟶ Y => (freeFunctor A).map f) := by
  have key : ∀ f : X ⟶ Y, f = freeUnit A X ≫ f ▷ A.X ≫ Y ◁ ε ≫ (ρ_ Y).hom := by
    intro f
    rw [← freeUnit_naturality_assoc]
    unfold freeUnit
    rw [Category.assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hε,
      MonoidalCategory.whiskerLeft_id, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  intro f g h
  have h' : f ▷ A.X = g ▷ A.X := congrArg RightMod.Hom.hom h
  rw [key f, key g, h']

end Free

section Preadditive

variable [Preadditive C] [MonoidalPreadditive C]

section Instances

variable {A : Mon C} {M N : RightMod A}

theorem neg_whiskerRight' {X Y : C} (f : X ⟶ Y) (Z : C) : (-f) ▷ Z = -(f ▷ Z) :=
  Functor.map_neg (tensorRight Z)

theorem sub_whiskerRight' {X Y : C} (f g : X ⟶ Y) (Z : C) : (f - g) ▷ Z = f ▷ Z - g ▷ Z :=
  Functor.map_sub (tensorRight Z)

theorem nsmul_whiskerRight' {X Y : C} (n : ℕ) (f : X ⟶ Y) (Z : C) :
    (n • f) ▷ Z = n • (f ▷ Z) :=
  Functor.map_nsmul (tensorRight Z)

theorem zsmul_whiskerRight' {X Y : C} (n : ℤ) (f : X ⟶ Y) (Z : C) :
    (n • f) ▷ Z = n • (f ▷ Z) :=
  Functor.map_zsmul (tensorRight Z)

instance : Zero (M ⟶ N) where
  zero := ⟨0, by simp⟩

instance : Add (M ⟶ N) where
  add f g := ⟨f.hom + g.hom, by
    rw [Preadditive.comp_add, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp,
      f.act_hom, g.act_hom]⟩

instance : Neg (M ⟶ N) where
  neg f := ⟨-f.hom, by
    rw [Preadditive.comp_neg, neg_whiskerRight', Preadditive.neg_comp, f.act_hom]⟩

instance : Sub (M ⟶ N) where
  sub f g := ⟨f.hom - g.hom, by
    rw [Preadditive.comp_sub, sub_whiskerRight', Preadditive.sub_comp, f.act_hom, g.act_hom]⟩

instance : SMul ℕ (M ⟶ N) where
  smul n f := ⟨n • f.hom, by
    rw [Preadditive.comp_nsmul, nsmul_whiskerRight', Preadditive.nsmul_comp, f.act_hom]⟩

instance : SMul ℤ (M ⟶ N) where
  smul n f := ⟨n • f.hom, by
    rw [Preadditive.comp_zsmul, zsmul_whiskerRight', Preadditive.zsmul_comp, f.act_hom]⟩

@[simp] theorem zero_hom' : (0 : M ⟶ N).hom = 0 := rfl
@[simp] theorem add_hom' (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl
@[simp] theorem neg_hom' (f : M ⟶ N) : (-f).hom = -f.hom := rfl
@[simp] theorem sub_hom' (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

/-- `𝒞_A` is preadditive when `C` is preadditive with additive whiskering. -/
instance preadditive : Preadditive (RightMod A) where
  homGroup P Q := Function.Injective.addCommGroup (fun f : P ⟶ Q => f.hom) hom_injective rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  add_comp P Q R f f' g := hom_ext (by
    show (f.hom + f'.hom) ≫ g.hom = f.hom ≫ g.hom + f'.hom ≫ g.hom
    exact Preadditive.add_comp _ _ _ _ _ _)
  comp_add P Q R f g g' := hom_ext (by
    show f.hom ≫ (g.hom + g'.hom) = f.hom ≫ g.hom + f.hom ≫ g'.hom
    exact Preadditive.comp_add _ _ _ _ _ _)

/-- `Hom.hom` as an additive group homomorphism. -/
def homAddMonoidHom (M N : RightMod A) : (M ⟶ N) →+ (M.X ⟶ N.X) where
  toFun f := f.hom
  map_zero' := rfl
  map_add' _ _ := rfl

variable (𝕜 : Type*) [Semiring 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C]

instance : SMul 𝕜 (M ⟶ N) where
  smul r f := ⟨r • f.hom, by
    rw [Linear.comp_smul, MonoidalLinear.smul_whiskerRight, Linear.smul_comp, f.act_hom]⟩

@[simp] theorem smul_hom' (r : 𝕜) (f : M ⟶ N) : (r • f).hom = r • f.hom := rfl

/-- `𝒞_A` is `𝕜`-linear when `C` is `𝕜`-linear with linear whiskering. -/
instance linear : Linear 𝕜 (RightMod A) where
  homModule P Q := Function.Injective.module 𝕜 (homAddMonoidHom P Q) hom_injective
    (fun _ _ => rfl)
  smul_comp P Q R r f g := hom_ext (by
    show (r • f.hom) ≫ g.hom = r • (f.hom ≫ g.hom)
    exact Linear.smul_comp _ _ _ _ _ _)
  comp_smul P Q R f r g := hom_ext (by
    show f.hom ≫ (r • g.hom) = r • (f.hom ≫ g.hom)
    exact Linear.comp_smul _ _ _ _ _ _)

end Instances

section LinearEquiv

variable (𝕜 : Type*) [Semiring 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C] (A : Mon C)

/-- **The free-module adjunction is `𝕜`-linear**: `Hom_A(X ⊗ A, M) ≃ₗ Hom_C(X, M)`. -/
def freeHomLinearEquiv (X : C) (M : RightMod A) : (free A X ⟶ M) ≃ₗ[𝕜] (X ⟶ M.X) where
  toFun g := freeUnit A X ≫ g.hom
  invFun := (freeHomEquiv A X M).invFun
  left_inv := (freeHomEquiv A X M).left_inv
  right_inv := (freeHomEquiv A X M).right_inv
  map_add' f g := by
    show freeUnit A X ≫ (f.hom + g.hom) = freeUnit A X ≫ f.hom + freeUnit A X ≫ g.hom
    exact Preadditive.comp_add _ _ _ _ _ _
  map_smul' r f := by
    show freeUnit A X ≫ (r • f.hom) = r • (freeUnit A X ≫ f.hom)
    exact Linear.comp_smul _ _ _ _ _ _

theorem freeHomLinearEquiv_apply (X : C) (M : RightMod A) (g : free A X ⟶ M) :
    freeHomLinearEquiv 𝕜 A X M g = freeUnit A X ≫ g.hom := rfl

/-- Free induction on morphisms, `f ↦ f ⊗ A`, as a `𝕜`-linear map. -/
def freeMapLinear (X Y : C) : (X ⟶ Y) →ₗ[𝕜] (free A X ⟶ free A Y) where
  toFun f := freeMap A f
  map_add' f g := hom_ext (by
    show (f + g) ▷ A.X = f ▷ A.X + g ▷ A.X
    exact MonoidalPreadditive.add_whiskerRight f g)
  map_smul' r f := hom_ext (by
    show (r • f) ▷ A.X = r • (f ▷ A.X)
    exact MonoidalLinear.smul_whiskerRight r f A.X)

theorem freeMapLinear_apply (X Y : C) (f : X ⟶ Y) :
    freeMapLinear 𝕜 A X Y f = (freeFunctor A).map f := rfl

/-- **Hom count for free modules** (manuscript lines 3340–3345):
`dim_𝕜 Hom_A(X ⊗ A, Y ⊗ A) = dim_𝕜 Hom_C(X, Y ⊗ A)`. -/
theorem finrank_hom_free (X Y : C) :
    Module.finrank 𝕜 (free A X ⟶ free A Y) = Module.finrank 𝕜 (X ⟶ Y ⊗ A.X) :=
  (freeHomLinearEquiv 𝕜 A X (free A Y)).finrank_eq

end LinearEquiv

end Preadditive

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.free
#print axioms HaagerupIzumi.C8.RightMod.freeFunctor
#print axioms HaagerupIzumi.C8.RightMod.freeHomEquiv
#print axioms HaagerupIzumi.C8.RightMod.freeAdjunction
#print axioms HaagerupIzumi.C8.RightMod.freeAdjunction_homEquiv
#print axioms HaagerupIzumi.C8.RightMod.freeAdjunction_unit_app
#print axioms HaagerupIzumi.C8.RightMod.freeAdjunction_counit_app_hom
#print axioms HaagerupIzumi.C8.RightMod.freeHomEquivFree
#print axioms HaagerupIzumi.C8.RightMod.freeHomEquiv_freeMap
#print axioms HaagerupIzumi.C8.RightMod.freeFunctor_map_injective
#print axioms HaagerupIzumi.C8.RightMod.preadditive
#print axioms HaagerupIzumi.C8.RightMod.linear
#print axioms HaagerupIzumi.C8.RightMod.freeHomLinearEquiv
#print axioms HaagerupIzumi.C8.RightMod.freeMapLinear
#print axioms HaagerupIzumi.C8.RightMod.finrank_hom_free
