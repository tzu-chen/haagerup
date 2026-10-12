module

public import HaagerupIzumi.C8.Category.FreeModuleSeparable
public import Mathlib.CategoryTheory.Monoidal.Bimod
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.CategoryTheory.Idempotents.Basic

@[expose] public section

/-! # The coequalizer identification: `M ⊗_A N` is the image of the separability idempotent

Second paragraph of the proof of Lemma `lem:analytic-unitary-all-modules` (manuscript
`haagerup_c8_expanded.tex`, lines 4900–4934): "The relative tensor product is obtained by
splitting the separability idempotent on `M ⊗ N`."  Mathlib's relative tensor product
`Bimod.tensorBimod` is the coequalizer of
`f = r_M ▷ N : (M ⊗ A) ⊗ N ⟶ M ⊗ N` and `g = α ≫ M ◁ l_N`.  For a monoid object `A` with a
separability section `sep : A ⟶ A ⊗ A` (`SeparabilitySection A`, an `A`-bimodule section of
the multiplication; `Category/FreeModuleSeparable.lean`), write `sep(1) = s₁ ⊗ s₂`.

* `leftSplit hS N : N ⟶ A ⊗ N`, `n ↦ s₁ ⊗ s₂ n`, a section of the left action
  (`leftSplit_actLeft`); `actLeft_leftSplit`, `whiskerLeft_leftSplit_mul`: both
  `a ⊗ n ↦ s₁ ⊗ s₂ (a n)` and `a ⊗ n ↦ a s₁ ⊗ s₂ n` equal `a ⊗ n ↦ sep(a) · n` (right resp.
  left `A`-linearity of `sep`).
* `sepIdem hS M N : M ⊗ N ⟶ M ⊗ N`, `m ⊗ n ↦ m s₁ ⊗ s₂ n`: **the separability idempotent**
  (`sepIdem_idem`); it coequalizes the pair (`actRight_sepIdem`: `f ≫ e = g ≫ e`).
* `isSplitCoequalizer hS M N π s`: for any splitting `π ≫ s = e`, `s ≫ π = 𝟙` of the
  idempotent, `π` is a **split coequalizer** of `f, g` (Mathlib's `IsSplitCoequalizer`, with
  left section `m ⊗ n ↦ (m ⊗ s₁) ⊗ s₂ n`).  Hence:
  - `hasSplitCoequalizer`, `hasCoequalizer`: if idempotents split in `C`
    (`IsIdempotentComplete C`), the pair defining `M ⊗_A N` has a coequalizer; no general
    coequalizers are needed;
  - `tensorBimodXIso`: when `C` has coequalizers, Mathlib's `M ⊗_A N` is isomorphic to the image
    `Z` of the idempotent, compatibly with the projections (`π_tensorBimodXIso_hom`);
  - `isCoequalizerMap`: the coequalizer is absolute (preserved by every functor), so the
    hypotheses of `Bimod.tensorBimod` that `X ⊗ -` and `- ⊗ X` preserve coequalizers hold
    automatically for these coequalizers.  (Mathlib's `Bimod.tensorBimod` still requires the
    global preservation instances as typeclass arguments.)

Generality: `C` any monoidal category (no braiding, no linearity), `A` a monoid object with a
separability section, `M` a right and `N` a left `A`-module (as bimodules `Bimod R A`,
`Bimod A T`).  Only the right action of `M` and the left action of `N` are used.  For `H/B`
a section is `RightMod.twistedSeparabilitySection` (`Category/FreeModuleTwistedSeparable.lean`),
which presupposes `hmul`; in the chain `hS ⇒ hnondeg` (`Category/NondegFromSeparable.lean`) the
section must instead come from outside (the Q-system / étale structure of `H/B`).
No external-theorem or certificate inputs. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace SeparableTensor

variable {R A T : Mon C} (hS : SeparabilitySection A)

section Left

variable (N : Bimod A T)

/-- `n ↦ s₁ ⊗ s₂ n`. -/
def leftSplit : N.X ⟶ A.X ⊗ N.X :=
  (λ_ N.X).inv ≫ η[A.X] ▷ N.X ≫ hS.sep ▷ N.X ≫ (α_ A.X A.X N.X).hom ≫ A.X ◁ N.actLeft

/-- `s₁ (s₂ n) = n`. -/
theorem leftSplit_actLeft : leftSplit hS N ≫ N.actLeft = 𝟙 N.X := by
  simp only [leftSplit, Category.assoc]
  rw [← N.left_assoc, ← MonoidalCategory.comp_whiskerRight_assoc hS.sep μ[A.X] N.X, hS.sep_mul,
    MonoidalCategory.id_whiskerRight, Category.id_comp, N.one_actLeft, Iso.inv_hom_id]

/-- `s₁ ⊗ s₂ (a n) = sep(a) · n` (right `A`-linearity of `sep`). -/
theorem actLeft_leftSplit :
    N.actLeft ≫ leftSplit hS N = hS.sep ▷ N.X ≫ (α_ A.X A.X N.X).hom ≫ A.X ◁ N.actLeft := by
  have hsep : hS.sep = (λ_ A.X).inv ≫ η[A.X] ▷ A.X ≫ hS.sep ▷ A.X ≫ (α_ A.X A.X A.X).hom ≫
      A.X ◁ μ[A.X] := by
    rw [← hS.mul_sep_right, MonObj.one_mul_assoc, Iso.inv_hom_id_assoc]
  calc N.actLeft ≫ leftSplit hS N
      = (λ_ (A.X ⊗ N.X)).inv ≫ η[A.X] ▷ (A.X ⊗ N.X) ≫ hS.sep ▷ (A.X ⊗ N.X) ≫
          (A.X ⊗ A.X) ◁ N.actLeft ≫ (α_ A.X A.X N.X).hom ≫ A.X ◁ N.actLeft := by
        simp only [leftSplit]
        rw [MonoidalCategory.leftUnitor_inv_naturality_assoc,
          MonoidalCategory.whisker_exchange_assoc, MonoidalCategory.whisker_exchange_assoc]
    _ = (λ_ (A.X ⊗ N.X)).inv ≫ η[A.X] ▷ (A.X ⊗ N.X) ≫ hS.sep ▷ (A.X ⊗ N.X) ≫
          (α_ A.X A.X (A.X ⊗ N.X)).hom ≫ A.X ◁ (A.X ◁ N.actLeft ≫ N.actLeft) := by
        rw [MonoidalCategory.associator_naturality_right_assoc, MonoidalCategory.whiskerLeft_comp]
    _ = (λ_ (A.X ⊗ N.X)).inv ≫ η[A.X] ▷ (A.X ⊗ N.X) ≫ hS.sep ▷ (A.X ⊗ N.X) ≫
          (α_ A.X A.X (A.X ⊗ N.X)).hom ≫
            A.X ◁ ((α_ A.X A.X N.X).inv ≫ μ[A.X] ▷ N.X ≫ N.actLeft) := by
        rw [N.left_assoc, Iso.inv_hom_id_assoc]
    _ = ((λ_ A.X).inv ≫ η[A.X] ▷ A.X ≫ hS.sep ▷ A.X ≫ (α_ A.X A.X A.X).hom ≫
          A.X ◁ μ[A.X]) ▷ N.X ≫ (α_ A.X A.X N.X).hom ≫ A.X ◁ N.actLeft := by
        monoidal
    _ = hS.sep ▷ N.X ≫ (α_ A.X A.X N.X).hom ≫ A.X ◁ N.actLeft := by
        rw [← hsep]

/-- `a s₁ ⊗ s₂ n = sep(a) · n` (left `A`-linearity of `sep`). -/
theorem whiskerLeft_leftSplit_mul :
    A.X ◁ leftSplit hS N ≫ (α_ A.X A.X N.X).inv ≫ μ[A.X] ▷ N.X =
      hS.sep ▷ N.X ≫ (α_ A.X A.X N.X).hom ≫ A.X ◁ N.actLeft := by
  have hsep : hS.sep = (ρ_ A.X).inv ≫ A.X ◁ η[A.X] ≫ A.X ◁ hS.sep ≫ (α_ A.X A.X A.X).inv ≫
      μ[A.X] ▷ A.X := by
    rw [← hS.mul_sep_left, MonObj.mul_one_assoc, Iso.inv_hom_id_assoc]
  calc A.X ◁ leftSplit hS N ≫ (α_ A.X A.X N.X).inv ≫ μ[A.X] ▷ N.X
      = A.X ◁ ((λ_ N.X).inv ≫ η[A.X] ▷ N.X ≫ hS.sep ▷ N.X ≫ (α_ A.X A.X N.X).hom) ≫
          (α_ A.X A.X (A.X ⊗ N.X)).inv ≫ μ[A.X] ▷ (A.X ⊗ N.X) ≫ A.X ◁ N.actLeft := by
        simp only [leftSplit, MonoidalCategory.whiskerLeft_comp, Category.assoc]
        rw [MonoidalCategory.associator_inv_naturality_right_assoc,
          MonoidalCategory.whisker_exchange]
    _ = ((ρ_ A.X).inv ≫ A.X ◁ η[A.X] ≫ A.X ◁ hS.sep ≫ (α_ A.X A.X A.X).inv ≫
          μ[A.X] ▷ A.X) ▷ N.X ≫ (α_ A.X A.X N.X).hom ≫ A.X ◁ N.actLeft := by
        monoidal
    _ = hS.sep ▷ N.X ≫ (α_ A.X A.X N.X).hom ≫ A.X ◁ N.actLeft := by
        rw [← hsep]

end Left

variable (M : Bimod R A) (N : Bimod A T)

/-- The left section `m ⊗ n ↦ (m ⊗ s₁) ⊗ s₂ n` of the pair. -/
def sepSection : M.X ⊗ N.X ⟶ (M.X ⊗ A.X) ⊗ N.X :=
  M.X ◁ leftSplit hS N ≫ (α_ M.X A.X N.X).inv

/-- **The separability idempotent** `m ⊗ n ↦ m s₁ ⊗ s₂ n` on `M ⊗ N`. -/
def sepIdem : M.X ⊗ N.X ⟶ M.X ⊗ N.X :=
  sepSection hS M N ≫ M.actRight ▷ N.X

/-- `m ⊗ s₁ s₂ n = m ⊗ n`. -/
theorem sepSection_bottom :
    sepSection hS M N ≫ ((α_ M.X A.X N.X).hom ≫ M.X ◁ N.actLeft) = 𝟙 (M.X ⊗ N.X) := by
  rw [sepSection, Category.assoc, Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp,
    leftSplit_actLeft, MonoidalCategory.whiskerLeft_id]

/-- The separability idempotent coequalizes the pair: `(m a) s₁ ⊗ s₂ n = m s₁ ⊗ s₂ (a n)`. -/
@[reassoc]
theorem actRight_sepIdem :
    M.actRight ▷ N.X ≫ sepIdem hS M N =
      (α_ M.X A.X N.X).hom ≫ M.X ◁ N.actLeft ≫ sepIdem hS M N := by
  have hR : M.actRight ▷ A.X ≫ M.actRight = (α_ M.X A.X A.X).hom ≫ M.X ◁ μ[A.X] ≫ M.actRight :=
    (Iso.inv_comp_eq _).1 M.right_assoc.symm
  calc M.actRight ▷ N.X ≫ sepIdem hS M N
      = (M.X ⊗ A.X) ◁ leftSplit hS N ≫ (α_ (M.X ⊗ A.X) A.X N.X).inv ≫
          (M.actRight ▷ A.X ≫ M.actRight) ▷ N.X := by
        simp only [sepIdem, sepSection, Category.assoc]
        rw [← MonoidalCategory.whisker_exchange_assoc,
          MonoidalCategory.associator_inv_naturality_left_assoc,
          MonoidalCategory.comp_whiskerRight]
    _ = (M.X ⊗ A.X) ◁ leftSplit hS N ≫ (α_ (M.X ⊗ A.X) A.X N.X).inv ≫
          ((α_ M.X A.X A.X).hom ≫ M.X ◁ μ[A.X] ≫ M.actRight) ▷ N.X := by
        rw [hR]
    _ = (α_ M.X A.X N.X).hom ≫
          M.X ◁ (A.X ◁ leftSplit hS N ≫ (α_ A.X A.X N.X).inv ≫ μ[A.X] ▷ N.X) ≫
            (α_ M.X A.X N.X).inv ≫ M.actRight ▷ N.X := by
        monoidal
    _ = (α_ M.X A.X N.X).hom ≫ M.X ◁ (N.actLeft ≫ leftSplit hS N) ≫
          (α_ M.X A.X N.X).inv ≫ M.actRight ▷ N.X := by
        rw [whiskerLeft_leftSplit_mul, actLeft_leftSplit]
    _ = (α_ M.X A.X N.X).hom ≫ M.X ◁ N.actLeft ≫ sepIdem hS M N := by
        simp only [sepIdem, sepSection, MonoidalCategory.whiskerLeft_comp, Category.assoc]

/-- The separability idempotent is idempotent. -/
theorem sepIdem_idem : sepIdem hS M N ≫ sepIdem hS M N = sepIdem hS M N := by
  calc sepIdem hS M N ≫ sepIdem hS M N
      = sepSection hS M N ≫ (M.actRight ▷ N.X ≫ sepIdem hS M N) := by
        simp only [sepIdem, Category.assoc]
    _ = (sepSection hS M N ≫ ((α_ M.X A.X N.X).hom ≫ M.X ◁ N.actLeft)) ≫ sepIdem hS M N := by
        rw [actRight_sepIdem]
        simp only [Category.assoc]
    _ = sepIdem hS M N := by
        rw [sepSection_bottom, Category.id_comp]

/-- **The coequalizer identification**: a splitting `π ≫ s = e`, `s ≫ π = 𝟙` of the separability
idempotent `e` on `M ⊗ N` is a split coequalizer of the pair `r_M ▷ N`, `α ≫ M ◁ l_N` defining
the relative tensor product `M ⊗_A N`. -/
def isSplitCoequalizer {Z : C} (π : M.X ⊗ N.X ⟶ Z) (s : Z ⟶ M.X ⊗ N.X)
    (hπs : π ≫ s = sepIdem hS M N) (hsπ : s ≫ π = 𝟙 Z) :
    IsSplitCoequalizer (M.actRight ▷ N.X) ((α_ M.X A.X N.X).hom ≫ M.X ◁ N.actLeft) π where
  rightSection := s
  leftSection := sepSection hS M N
  condition := by
    have hπ : π = sepIdem hS M N ≫ π := by
      rw [← hπs, Category.assoc, hsπ, Category.comp_id]
    rw [hπ]
    simp only [Category.assoc]
    rw [actRight_sepIdem_assoc]
  rightSection_π := hsπ
  leftSection_bottom := sepSection_bottom hS M N
  leftSection_top := hπs.symm

include hS in
/-- If idempotents split in `C`, the pair defining `M ⊗_A N` has a split coequalizer. -/
theorem hasSplitCoequalizer [IsIdempotentComplete C] :
    HasSplitCoequalizer (M.actRight ▷ N.X) ((α_ M.X A.X N.X).hom ≫ M.X ◁ N.actLeft) := by
  obtain ⟨Z, i, p, h1, h2⟩ :=
    IsIdempotentComplete.idempotents_split _ (sepIdem hS M N) (sepIdem_idem hS M N)
  exact ⟨⟨Z, p, ⟨isSplitCoequalizer hS M N p i h2 h1⟩⟩⟩

include hS in
/-- **`M ⊗_A N` exists as soon as idempotents split** (no general coequalizers needed). -/
theorem hasCoequalizer [IsIdempotentComplete C] :
    HasCoequalizer (M.actRight ▷ N.X) ((α_ M.X A.X N.X).hom ≫ M.X ◁ N.actLeft) := by
  have := hasSplitCoequalizer hS M N
  infer_instance

/-- The coequalizer is absolute: its image under any functor `G` is again a coequalizer (in
particular under `X ⊗ -` and `- ⊗ X`). -/
def isCoequalizerMap {D : Type*} [Category D] (G : C ⥤ D) {Z : C} (π : M.X ⊗ N.X ⟶ Z)
    (s : Z ⟶ M.X ⊗ N.X) (hπs : π ≫ s = sepIdem hS M N) (hsπ : s ≫ π = 𝟙 Z) :
    IsColimit ((isSplitCoequalizer hS M N π s hπs hsπ).map G).asCofork :=
  ((isSplitCoequalizer hS M N π s hπs hsπ).map G).isCoequalizer

section Mathlib

variable [HasCoequalizers C]

set_option backward.isDefEq.respectTransparency false in
/-- **Mathlib's relative tensor product is the image of the separability idempotent**:
`M ⊗_A N ≅ Z` for any splitting `π ≫ s = e`, `s ≫ π = 𝟙` of `e = sepIdem hS M N`. -/
noncomputable def tensorBimodXIso {Z : C} (π : M.X ⊗ N.X ⟶ Z) (s : Z ⟶ M.X ⊗ N.X)
    (hπs : π ≫ s = sepIdem hS M N) (hsπ : s ≫ π = 𝟙 Z) : Bimod.TensorBimod.X M N ≅ Z where
  hom := coequalizer.desc π (isSplitCoequalizer hS M N π s hπs hsπ).condition
  inv := s ≫ coequalizer.π _ _
  hom_inv_id := by
    dsimp only [Bimod.TensorBimod.X]
    apply coequalizer.hom_ext
    rw [coequalizer.π_desc_assoc, ← Category.assoc, hπs, Category.comp_id]
    show (sepSection hS M N ≫ M.actRight ▷ N.X) ≫ _ = _
    rw [Category.assoc, coequalizer.condition, ← Category.assoc, sepSection_bottom,
      Category.id_comp]
  inv_hom_id := by
    dsimp only [Bimod.TensorBimod.X]
    rw [Category.assoc, coequalizer.π_desc, hsπ]

set_option backward.isDefEq.respectTransparency false in
theorem π_tensorBimodXIso_hom {Z : C} (π : M.X ⊗ N.X ⟶ Z) (s : Z ⟶ M.X ⊗ N.X)
    (hπs : π ≫ s = sepIdem hS M N) (hsπ : s ≫ π = 𝟙 Z) :
    coequalizer.π (M.actRight ▷ N.X) ((α_ M.X A.X N.X).hom ≫ M.X ◁ N.actLeft) ≫
        (tensorBimodXIso hS M N π s hπs hsπ).hom = π :=
  coequalizer.π_desc _ _

end Mathlib

end SeparableTensor

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.SeparableTensor.leftSplit_actLeft
#print axioms HaagerupIzumi.C8.SeparableTensor.actLeft_leftSplit
#print axioms HaagerupIzumi.C8.SeparableTensor.whiskerLeft_leftSplit_mul
#print axioms HaagerupIzumi.C8.SeparableTensor.actRight_sepIdem
#print axioms HaagerupIzumi.C8.SeparableTensor.sepIdem_idem
#print axioms HaagerupIzumi.C8.SeparableTensor.isSplitCoequalizer
#print axioms HaagerupIzumi.C8.SeparableTensor.hasSplitCoequalizer
#print axioms HaagerupIzumi.C8.SeparableTensor.hasCoequalizer
#print axioms HaagerupIzumi.C8.SeparableTensor.isCoequalizerMap
#print axioms HaagerupIzumi.C8.SeparableTensor.tensorBimodXIso
#print axioms HaagerupIzumi.C8.SeparableTensor.π_tensorBimodXIso_hom
