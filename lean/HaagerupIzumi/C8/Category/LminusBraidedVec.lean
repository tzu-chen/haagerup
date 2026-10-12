module

public import HaagerupIzumi.C8.Category.PointedCocycleZ3
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Discrete

@[expose] public section

/-! # The pointed part on `L₋` is the image of a braided functor from symmetric `ℤ/3`

Functor-level packaging of `Lminus_untwisted_symmetric` (`Category/PointedCocycleZ3.lean`), the
Tannakian step of `L_untwisted` (manuscript `haagerup_c8_expanded.tex`, lines 3335–3337: "The
pointed subcategory on `L₋` is symmetric with trivial twists, hence Tannakian; as a tensor
category it is the untwisted `Vec_{ℤ/3}`").

**What "untwisted `Vec_{ℤ/3}`" means here.**  The source is Mathlib's discrete monoidal
category `Discrete (Multiplicative (ZMod 3))` (objects `ℤ/3`, only identity morphisms,
tensor product `a ⊗ b = a + b`, identity associator and unitors), with Mathlib's braiding of
a commutative monoid (`Discrete.eqToIso (mul_comm _ _)`), which is symmetric
(`discreteSymmetric`).  This is the skeleton of `Vec_{ℤ/3}` with trivial 3-cocycle and trivial
braiding, *before* `𝕜`-linearization: `Vec_{ℤ/3}` itself is its `𝕜`-linear additive envelope
(finite direct sums of the simples `δ_a`).  The theorems below give a braided monoidal functor
from this discrete category; its extension to the additive envelope (and the resulting
braided equivalence onto the additive closure of `L₋`) is not formalized here.

* `discreteSymmetric`: the braiding of `Discrete M` (`M` a commutative monoid) is symmetric.
* `lminusFunctor S : Discrete (Multiplicative (ZMod 3)) ⥤ C`, `a ↦ S a`.
* `lminusCoreMonoidal`: for isomorphisms `φ'_{a,b} : S a ⊗ S b ≅ S (a + b)` with trivial
  associator (`hα`, the equation of `Lminus_untwisted_symmetric`) and a unit
  `u : S 0 ≅ 𝟙_ C`, the functor is monoidal with tensorator `φ'` and unit `u⁻¹` rescaled by a
  scalar (`unitScalar`; the triangle identity and `hα` at `(a, 0, b)` show that the left and
  right unit scalars are one constant `t`, `lsc_eq_rsc`); Mathlib's associativity axiom is
  exactly `hα`.
* `lminusBraided`: if moreover the braiding is trivial in `φ'` (`hβ`), the functor is braided;
  Mathlib's braided-functor axiom is exactly `hβ`.
* `Lminus_braided_vec`: **for the module-category data (`S : (ℤ/3)² → C` with `hSchur`,
  `hfusion`, `hunitS`) and trivial self-braidings on `L₋` (`hθ`), there is a braided monoidal
  functor `F` from the symmetric discrete `ℤ/3` with `F (a) = S (a, -a)`, and
  `dim Hom(F a, F b) = δ_{a,b}`** (so `F` becomes fully faithful after `𝕜`-linearization of
  the source, and it is faithful).

Hypotheses: `hSchur`, `hfusion`, `hunitS` as in `Category/FreeModuleMonoidalEquivalence.lean`;
**`hθ` [external]**: the self-braiding of each invertible `S (a, -a)` of `L₋` is the identity.
For `Rep(B)`: the twist is `θ = e^{2πi L₀}` (Huang, 2008), for an invertible `ℓ` (`d_ℓ = 1`) the
self-braiding is `c_{ℓ,ℓ} = θ_ℓ`, and `h_ℓ ≡ q(ℓ) mod 1` (equivalently, the lattice braiding on
simple currents is `e^{πi(λ,μ)}`, Dong–Lepowsky); with `q = 0` on `L₋`
(`Weights.Lminus_symmetric_trivial_twists`) this gives `hθ`.  No certificate inputs. -/

set_option linter.unusedSectionVars false

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory Module

universe v u

namespace PointedCocycle

/-- The braiding of the discrete monoidal category of a commutative monoid is symmetric. -/
instance discreteSymmetric (M : Type*) [CommMonoid M] : SymmetricCategory (Discrete M) where
  toBraidedCategory := inferInstance
  symmetry _ _ := Subsingleton.elim _ _

section Functor

variable {C : Type u} [Category.{v} C] (S : ZMod 3 → C)

/-- The functor `a ↦ S a` on the discrete category of `ℤ/3` (written multiplicatively). -/
def lminusFunctor : Discrete (Multiplicative (ZMod 3)) ⥤ C where
  obj X := S (Multiplicative.toAdd X.as)
  map f := eqToHom (congrArg (fun x => S (Multiplicative.toAdd x)) (Discrete.eq_of_hom f))
  map_id _ := by simp
  map_comp _ _ := by simp

theorem lminusFunctor_obj (a : ZMod 3) :
    (lminusFunctor S).obj (Discrete.mk (Multiplicative.ofAdd a)) = S a := rfl

end Functor

section Monoidal

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] (𝕜 : Type*) [Field 𝕜] [Linear 𝕜 C] [MonoidalLinear 𝕜 C]
  (S : ZMod 3 → C) (hEnd : ∀ a, finrank 𝕜 (S a ⟶ S a) = 1)
  (φ : ∀ a b : ZMod 3, S a ⊗ S b ≅ S (a + b)) (u : S 0 ≅ 𝟙_ C)
  (hα : ∀ a b c, (α_ (S a) (S b) (S c)).hom ≫ S a ◁ (φ b c).hom ≫ (φ a (b + c)).hom =
    (φ a b).hom ▷ S c ≫ (φ (a + b) c).hom ≫ eqToHom (congrArg S (add_assoc a b c)))

/-- The left unit scalar at `a`. -/
noncomputable def lsc (a : ZMod 3) : 𝕜 :=
  scal 𝕜 S hEnd ((λ_ (S a)).inv ≫ u.inv ▷ S a ≫ (φ 0 a).hom ≫ eqToHom (congrArg S (zero_add a)))

/-- The right unit scalar at `a`. -/
noncomputable def rsc (a : ZMod 3) : 𝕜 :=
  scal 𝕜 S hEnd ((ρ_ (S a)).inv ≫ S a ◁ u.inv ≫ (φ a 0).hom ≫ eqToHom (congrArg S (add_zero a)))

theorem lsc_rel (a : ZMod 3) :
    u.inv ▷ S a ≫ (φ 0 a).hom = lsc 𝕜 S hEnd φ u a •
      ((λ_ (S a)).hom ≫ eqToHom (congrArg S (zero_add a).symm)) := by
  have h := scal_smul 𝕜 S hEnd
    ((λ_ (S a)).inv ≫ u.inv ▷ S a ≫ (φ 0 a).hom ≫ eqToHom (congrArg S (zero_add a)))
  calc u.inv ▷ S a ≫ (φ 0 a).hom = (λ_ (S a)).hom ≫ ((λ_ (S a)).inv ≫ u.inv ▷ S a ≫
      (φ 0 a).hom ≫ eqToHom (congrArg S (zero_add a))) ≫
        eqToHom (congrArg S (zero_add a).symm) := by simp
    _ = _ := by
      rw [← h]
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
      rfl

theorem rsc_rel (a : ZMod 3) :
    S a ◁ u.inv ≫ (φ a 0).hom = rsc 𝕜 S hEnd φ u a •
      ((ρ_ (S a)).hom ≫ eqToHom (congrArg S (add_zero a).symm)) := by
  have h := scal_smul 𝕜 S hEnd
    ((ρ_ (S a)).inv ≫ S a ◁ u.inv ≫ (φ a 0).hom ≫ eqToHom (congrArg S (add_zero a)))
  calc S a ◁ u.inv ≫ (φ a 0).hom = (ρ_ (S a)).hom ≫ ((ρ_ (S a)).inv ≫ S a ◁ u.inv ≫
      (φ a 0).hom ≫ eqToHom (congrArg S (add_zero a))) ≫
        eqToHom (congrArg S (add_zero a).symm) := by simp
    _ = _ := by
      rw [← h]
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp]
      rfl

include hα in
/-- The left and right unit scalars agree and are constant (triangle identity and the trivial
associator at `(a, 0, b)`). -/
theorem lsc_eq_rsc (a b : ZMod 3) : lsc 𝕜 S hEnd φ u b = rsc 𝕜 S hEnd φ u a := by
  have hL : (S a ◁ u.inv) ▷ S b ≫ (α_ (S a) (S 0) (S b)).hom ≫ S a ◁ (φ 0 b).hom ≫
      (φ a (0 + b)).hom = lsc 𝕜 S hEnd φ u b •
        ((ρ_ (S a)).hom ▷ S b ≫ (φ a b).hom ≫
          eqToHom (congrArg S (congrArg (a + ·) (zero_add b).symm))) := by
    rw [MonoidalCategory.associator_naturality_middle_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, lsc_rel 𝕜 S hEnd φ u b,
      MonoidalLinear.whiskerLeft_smul (R := 𝕜), Linear.smul_comp, Linear.comp_smul,
      MonoidalCategory.whiskerLeft_comp_assoc, natL S φ a (zero_add b).symm,
      MonoidalCategory.triangle_assoc]
  have hR : (S a ◁ u.inv) ▷ S b ≫ (φ a 0).hom ▷ S b ≫ (φ (a + 0) b).hom ≫
      eqToHom (congrArg S (add_assoc a 0 b)) = rsc 𝕜 S hEnd φ u a •
        ((ρ_ (S a)).hom ▷ S b ≫ (φ a b).hom ≫
          eqToHom (congrArg S (congrArg (· + b) (add_zero a).symm)) ≫
            eqToHom (congrArg S (add_assoc a 0 b))) := by
    rw [← MonoidalCategory.comp_whiskerRight_assoc, rsc_rel 𝕜 S hEnd φ u a,
      MonoidalLinear.smul_whiskerRight (R := 𝕜), Linear.smul_comp,
      MonoidalCategory.comp_whiskerRight_assoc, natR_assoc S φ (add_zero a).symm b]
  have key : lsc 𝕜 S hEnd φ u b •
        ((ρ_ (S a)).hom ▷ S b ≫ (φ a b).hom ≫
          eqToHom (congrArg S (congrArg (a + ·) (zero_add b).symm))) =
      rsc 𝕜 S hEnd φ u a •
        ((ρ_ (S a)).hom ▷ S b ≫ (φ a b).hom ≫
          eqToHom (congrArg S (congrArg (· + b) (add_zero a).symm)) ≫
            eqToHom (congrArg S (add_assoc a 0 b))) := by
    rw [← hL, ← hR, hα]
  simp only [eqToHom_trans] at key
  exact smul_cancel 𝕜 S hEnd _ key

/-- The common unit scalar. -/
noncomputable def unitScalar : 𝕜 := lsc 𝕜 S hEnd φ u 0

theorem unitScalar_ne_zero : unitScalar 𝕜 S hEnd φ u ≠ 0 := by
  unfold unitScalar lsc
  exact scal_ne_zero 𝕜 S hEnd _

/-- The rescaled unit `𝟙_ C ≅ S 0`. -/
@[simps]
noncomputable def unitIso : 𝟙_ C ≅ S 0 where
  hom := (unitScalar 𝕜 S hEnd φ u)⁻¹ • u.inv
  inv := unitScalar 𝕜 S hEnd φ u • u.hom
  hom_inv_id := by
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul, Iso.inv_hom_id,
      inv_mul_cancel₀ (unitScalar_ne_zero 𝕜 S hEnd φ u), one_smul]
  inv_hom_id := by
    rw [Linear.smul_comp, Linear.comp_smul, smul_smul, Iso.hom_inv_id,
      mul_inv_cancel₀ (unitScalar_ne_zero 𝕜 S hEnd φ u), one_smul]

/-- **Free monoidal structure**: `a ↦ S a` is a monoidal functor from the discrete `ℤ/3`, with
tensorator `φ` and unit `unitIso`; associativity is exactly `hα`. -/
noncomputable def lminusCoreMonoidal : (lminusFunctor S).CoreMonoidal where
  εIso := unitIso 𝕜 S hEnd φ u
  μIso X Y := φ (Multiplicative.toAdd X.as) (Multiplicative.toAdd Y.as)
  μIso_hom_natural_left {X Y} f X' := by
    obtain rfl : X = Y := Discrete.as_bijective.injective (Discrete.eq_of_hom f)
    obtain rfl : f = 𝟙 X := Subsingleton.elim _ _
    simp
  μIso_hom_natural_right {X Y} X' f := by
    obtain rfl : X = Y := Discrete.as_bijective.injective (Discrete.eq_of_hom f)
    obtain rfl : f = 𝟙 X := Subsingleton.elim _ _
    simp
  associativity X Y Z := by
    show (φ _ _).hom ▷ S _ ≫ (φ _ _).hom ≫
        eqToHom (congrArg S (add_assoc (Multiplicative.toAdd X.as) (Multiplicative.toAdd Y.as)
          (Multiplicative.toAdd Z.as))) = _
    exact (hα _ _ _).symm
  left_unitality X := by
    show (λ_ (S (Multiplicative.toAdd X.as))).hom =
      ((unitScalar 𝕜 S hEnd φ u)⁻¹ • u.inv) ▷ S (Multiplicative.toAdd X.as) ≫
        (φ 0 (Multiplicative.toAdd X.as)).hom ≫ eqToHom (congrArg S (zero_add _))
    have hl : lsc 𝕜 S hEnd φ u (Multiplicative.toAdd X.as) = unitScalar 𝕜 S hEnd φ u := by
      unfold unitScalar
      rw [lsc_eq_rsc 𝕜 S hEnd φ u hα 0, lsc_eq_rsc 𝕜 S hEnd φ u hα 0]
    rw [MonoidalLinear.smul_whiskerRight (R := 𝕜), Linear.smul_comp,
      ← Category.assoc (u.inv ▷ _), lsc_rel 𝕜 S hEnd φ u, hl, Linear.smul_comp, smul_smul,
      inv_mul_cancel₀ (unitScalar_ne_zero 𝕜 S hEnd φ u), one_smul]
    simp
  right_unitality X := by
    show (ρ_ (S (Multiplicative.toAdd X.as))).hom =
      S (Multiplicative.toAdd X.as) ◁ ((unitScalar 𝕜 S hEnd φ u)⁻¹ • u.inv) ≫
        (φ (Multiplicative.toAdd X.as) 0).hom ≫ eqToHom (congrArg S (add_zero _))
    have hr : rsc 𝕜 S hEnd φ u (Multiplicative.toAdd X.as) = unitScalar 𝕜 S hEnd φ u := by
      unfold unitScalar
      rw [lsc_eq_rsc 𝕜 S hEnd φ u hα _ 0]
    rw [MonoidalLinear.whiskerLeft_smul (R := 𝕜), Linear.smul_comp,
      ← Category.assoc (_ ◁ u.inv), rsc_rel 𝕜 S hEnd φ u, hr, Linear.smul_comp, smul_smul,
      inv_mul_cancel₀ (unitScalar_ne_zero 𝕜 S hEnd φ u), one_smul]
    simp

section Braided

variable [BraidedCategory C]
  (hβ : ∀ a b, (β_ (S a) (S b)).hom ≫ (φ b a).hom =
    (φ a b).hom ≫ eqToHom (congrArg S (add_comm a b)))

/-- **The functor is braided**: Mathlib's braided-functor axiom is exactly `hβ`. -/
@[instance_reducible]
noncomputable def lminusBraided : (lminusFunctor S).Braided :=
  { (lminusCoreMonoidal 𝕜 S hEnd φ u hα).toMonoidal with
    braided := fun X Y => by
      show (φ _ _).hom ≫ eqToHom (congrArg S (add_comm (Multiplicative.toAdd X.as)
        (Multiplicative.toAdd Y.as))) = (β_ _ _).hom ≫ (φ _ _).hom
      exact (hβ _ _).symm }

end Braided

end Monoidal

section Lminus

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C] (𝕜 : Type*) [Field 𝕜] [Linear 𝕜 C]
  [MonoidalLinear 𝕜 C]

/-- `(a, -a) + (b, -b) = (a + b, -(a + b))`. -/
theorem Lminus_add (a b : ZMod 3) :
    ((a, -a) : ZMod 3 × ZMod 3) + (b, -b) = (a + b, -(a + b)) :=
  Prod.ext rfl (neg_add a b).symm

/-- **The pointed part on `L₋` is the image of a braided monoidal functor from the symmetric
discrete `ℤ/3`** (the untwisted, symmetric `Vec_{ℤ/3}` before linearization).  Inputs: the
pointed structure of `Rep(B)` (`hSchur`, `hfusion`, `hunitS`) and **[external]** `hθ`, the
triviality of the self-braiding on the invertibles of `L₋`. -/
theorem Lminus_braided_vec (S : ZMod 3 × ZMod 3 → C)
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w)) (hunitS : S (0, 0) ≅ 𝟙_ C)
    (hθ : ∀ a : ZMod 3, (β_ (S (a, -a)) (S (a, -a))).hom = 𝟙 _) :
    ∃ (F : Discrete (Multiplicative (ZMod 3)) ⥤ C) (_ : F.Braided),
      (∀ a : ZMod 3, F.obj (Discrete.mk (Multiplicative.ofAdd a)) = S (a, -a)) ∧
        ∀ X Y, finrank 𝕜 (F.obj X ⟶ F.obj Y) = if X = Y then 1 else 0 := by
  let S' : ZMod 3 → C := fun a => S (a, -a)
  have hEnd : ∀ a, finrank 𝕜 (S' a ⟶ S' a) = 1 := fun a => by
    show finrank 𝕜 (S (a, -a) ⟶ S (a, -a)) = 1
    rw [hSchur, if_pos rfl]
  let φ : ∀ a b : ZMod 3, S' a ⊗ S' b ≅ S' (a + b) := fun a b =>
    hfusion (a, -a) (b, -b) ≪≫ eqToIso (congrArg S (Lminus_add a b))
  obtain ⟨φ', hα, hβ⟩ := Lminus_untwisted_symmetric 𝕜 S' hEnd φ hθ
  let u : S' 0 ≅ 𝟙_ C := eqToIso (congrArg S (Prod.ext rfl neg_zero)) ≪≫ hunitS
  refine ⟨lminusFunctor S', lminusBraided 𝕜 S' hEnd φ' u hα hβ, fun a => rfl, fun X Y => ?_⟩
  show finrank 𝕜 (S (Multiplicative.toAdd X.as, -Multiplicative.toAdd X.as) ⟶
    S (Multiplicative.toAdd Y.as, -Multiplicative.toAdd Y.as)) = _
  rw [hSchur]
  by_cases h : X = Y
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    apply Discrete.as_bijective.injective
    exact Multiplicative.toAdd.injective (congrArg Prod.fst h')

end Lminus

end PointedCocycle

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.PointedCocycle.discreteSymmetric
#print axioms HaagerupIzumi.C8.PointedCocycle.lsc_eq_rsc
#print axioms HaagerupIzumi.C8.PointedCocycle.lminusCoreMonoidal
#print axioms HaagerupIzumi.C8.PointedCocycle.lminusBraided
#print axioms HaagerupIzumi.C8.PointedCocycle.Lminus_braided_vec
