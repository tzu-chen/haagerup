module

public import HaagerupIzumi.C8.Category.TwistedGroupAlgebraOfUnit

@[expose] public section

/-! # The pairing hypothesis `hnondeg` from separability

`Category/TwistedGroupAlgebraOfUnit.lean` derives `hmul` (all homogeneous components of the
multiplication of `A ≅ ⊕_{c ∈ ℤ/3} S (c, c)` are nonzero) from `hunit` (the unit of `A` lies in
`S (0, 0)`) and `hnondeg` (`mulComp hA d (-d) ≠ 0`).  Here `hnondeg` is derived from a
separability section of `A` (`SeparabilitySection A`), `hunit` and `S (0, 0) ≅ 𝟙_ C`.

Argument (with `A_c = S (c, c)`, `sep(1) = σ = Σ σ_{c,e}`, `σ_{c,e} ∈ A_c ⊗ A_e`):
* `mulComp_pairing_swap`: if `A_{-d} A_d ≠ 0` then `A_d A_{-d} ≠ 0` (for `y ∈ A_{-d}` with
  `y x` invertible, `x = x (y x) = (x y) x`; this is associativity, as in
  `mulComp_ne_zero_of_unit_of_nondegenerate`, `mulComp_ne_zero_of_pairing`).
* Suppose `d ≠ 0` and `A_d A_{-d} = 0 = A_{-d} A_d`.  For `x ∈ A_d`, `x σ = sep(x) = σ x`
  (`sep_left_form`, `sep_right_form`: bimodule linearity of `sep`).  The `(d, 0)` component of
  `σ x` vanishes (it is `σ_{d,-d} x`, and `A_{-d} A_d = 0`), while that of `x σ` is
  `x σ_{0,0}` with `x · : A_0 → A_d` invertible.  Hence `A_d ◁ σ_{0,0} = 0`, so `σ_{0,0} = 0`
  (`S (d, d)` is invertible).  Then the degree-0 part of `μ(σ) = 1` is
  `μ(σ_{0,0}) + μ(σ_{d,-d}) + μ(σ_{-d,d}) = 0` (`ℤ/3 = {0, d, -d}`), so the unit of `A` is
  zero, a contradiction (`A ≠ 0`).
* `mulComp_pairing_ne_zero_of_separable`: hence `mulComp hA d (-d) ≠ 0` for all `d` (for
  `d = 0` from `hunit`).  `netCount_simple_modules_separable` and
  `freeLminus_isEquivalence_separable`: the count `9/3 = 3` and the equivalence with `hnondeg`
  replaced by the separability section, `hunit` and `S (0, 0) ≅ 𝟙_ C`.

No external-theorem or certificate inputs beyond the named hypotheses. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits Module

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

section General

variable [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C] {A : Mon C}

omit [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C] in
/-- `x · sep(1) = sep(x)` (left `A`-linearity of `sep`). -/
theorem sep_left_form (hS : SeparabilitySection A) {X : C} (x : X ⟶ A.X) :
    (ρ_ X).inv ≫ x ▷ 𝟙_ C ≫ A.X ◁ (η[A.X] ≫ hS.sep) ≫ (α_ A.X A.X A.X).inv ≫
      μ[A.X] ▷ A.X = x ≫ hS.sep := by
  calc _ = x ≫ (ρ_ A.X).inv ≫ A.X ◁ η[A.X] ≫ A.X ◁ hS.sep ≫ (α_ A.X A.X A.X).inv ≫
        μ[A.X] ▷ A.X := by
        rw [← MonoidalCategory.rightUnitor_inv_naturality_assoc,
          MonoidalCategory.whiskerLeft_comp_assoc]
    _ = x ≫ (ρ_ A.X).inv ≫ A.X ◁ η[A.X] ≫ μ[A.X] ≫ hS.sep := by rw [hS.mul_sep_left]
    _ = x ≫ hS.sep := by rw [MonObj.mul_one_assoc, Iso.inv_hom_id_assoc]

omit [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C] in
/-- `sep(1) · x = sep(x)` (right `A`-linearity of `sep`). -/
theorem sep_right_form (hS : SeparabilitySection A) {X : C} (x : X ⟶ A.X) :
    (λ_ X).inv ≫ 𝟙_ C ◁ x ≫ (η[A.X] ≫ hS.sep) ▷ A.X ≫ (α_ A.X A.X A.X).hom ≫
      A.X ◁ μ[A.X] = x ≫ hS.sep := by
  calc _ = x ≫ (λ_ A.X).inv ≫ η[A.X] ▷ A.X ≫ hS.sep ▷ A.X ≫ (α_ A.X A.X A.X).hom ≫
        A.X ◁ μ[A.X] := by
        rw [← MonoidalCategory.leftUnitor_inv_naturality_assoc,
          MonoidalCategory.comp_whiskerRight_assoc]
    _ = x ≫ (λ_ A.X).inv ≫ η[A.X] ▷ A.X ≫ μ[A.X] ≫ hS.sep := by rw [hS.mul_sep_right]
    _ = x ≫ hS.sep := by rw [MonObj.one_mul_assoc, Iso.inv_hom_id_assoc]

omit [HasFiniteBiproducts C] in
/-- Tensoring on the left with an object `Y` having a left inverse `T ⊗ Y ≅ 𝟙` reflects zero
morphisms out of `𝟙`. -/
theorem eq_zero_of_whiskerLeft_eq_zero {Y T Z : C} (φ : T ⊗ Y ≅ 𝟙_ C) (f : 𝟙_ C ⟶ Z)
    (h : Y ◁ f = 0) : f = 0 := by
  have h1 : (T ⊗ Y) ◁ f = 0 := by
    rw [MonoidalCategory.tensor_whiskerLeft, h, MonoidalPreadditive.whiskerLeft_zero, zero_comp,
      comp_zero]
  have h2 : 𝟙_ C ◁ f = 0 := by
    have : φ.hom ▷ 𝟙_ C ≫ 𝟙_ C ◁ f = 0 := by
      rw [← MonoidalCategory.whisker_exchange, h1, zero_comp]
    rw [← Category.id_comp (𝟙_ C ◁ f), ← MonoidalCategory.inv_hom_whiskerRight φ (𝟙_ C),
      Category.assoc, this, comp_zero]
  rw [← Iso.inv_hom_id_assoc (λ_ (𝟙_ C)) f, ← MonoidalCategory.leftUnitor_naturality, h2,
    zero_comp, comp_zero]

end General

variable (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [MonoidalPreadditive C]
  [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]
  {A : Mon C} {S : ZMod 3 × ZMod 3 → C}
  (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
  (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
  (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c))

section Components

include hSchur hfusion in
/-- Only one summand of the second factor contributes to `x · a ∈ A_f` for `x ∈ A_c`. -/
theorem incl_whiskerRight_mul_proj (c f e₀ : ZMod 3) (he : c + e₀ = f) :
    summandIncl hA c ▷ A.X ≫ μ[A.X] ≫ summandProj hA f =
      S (c, c) ◁ summandProj hA e₀ ≫ (summandIncl hA c ⊗ₘ summandIncl hA e₀) ≫ μ[A.X] ≫
        summandProj hA f := by
  have hsum : summandIncl hA c ▷ A.X =
      ∑ e, S (c, c) ◁ summandProj hA e ≫ (summandIncl hA c ⊗ₘ summandIncl hA e) := by
    rw [← Category.comp_id (summandIncl hA c ▷ A.X), ← MonoidalCategory.whiskerLeft_id,
      ← summand_total hA, whiskerLeft_sum, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [MonoidalCategory.whiskerLeft_comp, ← Category.assoc,
      ← MonoidalCategory.whisker_exchange, Category.assoc, ← MonoidalCategory.tensorHom_def]
  rw [hsum, Preadditive.sum_comp, Finset.sum_eq_single e₀]
  · simp only [Category.assoc]
  · intro e _ hne
    have hne' : c + e ≠ f := fun h => hne (add_left_cancel (h.trans he.symm))
    rw [Category.assoc, ← Category.assoc (summandIncl hA c ⊗ₘ summandIncl hA e),
      mul_eq_mulComp 𝕜 hSchur hfusion hA, Category.assoc, summandIncl_proj_ne hA hne',
      comp_zero, comp_zero]
  · intro h
    exact absurd (Finset.mem_univ e₀) h

include hSchur hfusion in
/-- Only one summand of the first factor contributes to `a · x ∈ A_f` for `x ∈ A_c`. -/
theorem whiskerLeft_incl_mul_proj (c f e₀ : ZMod 3) (he : e₀ + c = f) :
    A.X ◁ summandIncl hA c ≫ μ[A.X] ≫ summandProj hA f =
      summandProj hA e₀ ▷ S (c, c) ≫ (summandIncl hA e₀ ⊗ₘ summandIncl hA c) ≫ μ[A.X] ≫
        summandProj hA f := by
  have hsum : A.X ◁ summandIncl hA c =
      ∑ e, summandProj hA e ▷ S (c, c) ≫ (summandIncl hA e ⊗ₘ summandIncl hA c) := by
    rw [← Category.id_comp (A.X ◁ summandIncl hA c), ← MonoidalCategory.id_whiskerRight,
      ← summand_total hA, sum_whiskerRight, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [MonoidalCategory.comp_whiskerRight, Category.assoc, ← MonoidalCategory.tensorHom_def]
  rw [hsum, Preadditive.sum_comp, Finset.sum_eq_single e₀]
  · simp only [Category.assoc]
  · intro e _ hne
    have hne' : e + c ≠ f := fun h => hne (add_right_cancel (h.trans he.symm))
    rw [Category.assoc, ← Category.assoc (summandIncl hA e ⊗ₘ summandIncl hA c),
      mul_eq_mulComp 𝕜 hSchur hfusion hA, Category.assoc, summandIncl_proj_ne hA hne',
      comp_zero, comp_zero]
  · intro h
    exact absurd (Finset.mem_univ e₀) h

omit [Linear 𝕜 C] [MonoidalPreadditive C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] in
theorem isIso_incl_proj_of_eq {c c' : ZMod 3} (h : c = c') :
    IsIso (summandIncl hA c ≫ summandProj hA c') := by
  subst h
  rw [summandIncl_proj_self]
  infer_instance

end Components

section Pairing

include hSchur hfusion in
/-- Pointwise form of `mulComp_ne_zero_of_unit_of_nondegenerate`: if `A_d A_{-d} ≠ 0` then
`A_c A_d ≠ 0` for every `c`. -/
theorem mulComp_ne_zero_of_pairing
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0) {d : ZMod 3}
    (hd : mulComp hA d (-d) ≠ 0) (c : ZMod 3) : mulComp hA c d ≠ 0 := by
  intro h0
  have hright : ∀ e : ZMod 3, e = 0 → mulComp hA c e ≠ 0 := by
    intro e he
    subst he
    exact mulComp_zero_right_ne_zero 𝕜 hSchur hfusion hA hunit c
  have i1 : IsIso (mulComp hA d (-d)) := isIso_mulComp 𝕜 hSchur hfusion hA d (-d) hd
  have i2 : IsIso (mulComp hA c (d + -d)) :=
    isIso_mulComp 𝕜 hSchur hfusion hA c (d + -d) (hright _ (add_neg_cancel d))
  have hL : ((summandIncl hA c ⊗ₘ summandIncl hA d) ⊗ₘ summandIncl hA (-d)) ≫
      μ[A.X] ▷ A.X ≫ μ[A.X] = 0 := by
    rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      mul_eq_mulComp 𝕜 hSchur hfusion hA c d, h0, zero_comp, MonoidalPreadditive.zero_tensor,
      zero_comp]
  have hR : ((summandIncl hA c ⊗ₘ summandIncl hA d) ⊗ₘ summandIncl hA (-d)) ≫
      μ[A.X] ▷ A.X ≫ μ[A.X] =
        (α_ _ _ _).hom ≫ S (c, c) ◁ mulComp hA d (-d) ≫ mulComp hA c (d + -d) ≫
          summandIncl hA (c + (d + -d)) := by
    rw [MonObj.mul_assoc, MonoidalCategory.associator_naturality_assoc]
    congr 1
    calc (summandIncl hA c ⊗ₘ (summandIncl hA d ⊗ₘ summandIncl hA (-d))) ≫ A.X ◁ μ[A.X] ≫
          μ[A.X]
        = (summandIncl hA c ⊗ₘ ((summandIncl hA d ⊗ₘ summandIncl hA (-d)) ≫ μ[A.X])) ≫
            μ[A.X] := by
          rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
            Category.comp_id]
      _ = (summandIncl hA c ⊗ₘ (mulComp hA d (-d) ≫ summandIncl hA (d + -d))) ≫ μ[A.X] := by
          rw [mul_eq_mulComp 𝕜 hSchur hfusion hA d (-d)]
      _ = S (c, c) ◁ mulComp hA d (-d) ≫ (summandIncl hA c ⊗ₘ summandIncl hA (d + -d)) ≫
            μ[A.X] := by
          rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
            Category.id_comp]
      _ = S (c, c) ◁ mulComp hA d (-d) ≫ mulComp hA c (d + -d) ≫
            summandIncl hA (c + (d + -d)) := by
          rw [mul_eq_mulComp 𝕜 hSchur hfusion hA c (d + -d)]
  have hz := hR.symm.trans hL
  apply summandIncl_ne_zero 𝕜 hSchur hA (c + (d + -d))
  refine (cancel_epi ((α_ (S (c, c)) (S (d, d)) (S (-d, -d))).hom ≫
    S (c, c) ◁ mulComp hA d (-d) ≫ mulComp hA c (d + -d))).1 ?_
  rw [comp_zero]
  simpa only [Category.assoc] using hz

include hSchur hfusion in
/-- If `A_{-d} A_d ≠ 0` then `A_d A_{-d} ≠ 0`. -/
theorem mulComp_pairing_swap
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0) {d : ZMod 3}
    (h : mulComp hA (-d) d ≠ 0) : mulComp hA d (-d) ≠ 0 := by
  have h' : ∀ e : ZMod 3, e = d → mulComp hA (-d) e ≠ 0 := by
    rintro e rfl
    exact h
  exact mulComp_ne_zero_of_pairing 𝕜 hSchur hfusion hA hunit (d := -d) (h' _ (neg_neg d)) d

end Pairing

section Separable

/-- `ℤ/3 = {0, d, -d}` for `d ≠ 0`. -/
theorem zmod3_cases : ∀ c d : ZMod 3, d ≠ 0 → c = 0 ∨ c = d ∨ c = -d := by decide

include hSchur hfusion in
/-- **Separability excludes a vanishing pairing**: for `d ≠ 0`, `A_d A_{-d}` and `A_{-d} A_d`
cannot both vanish. -/
theorem not_pairing_zero_of_separable (hS : SeparabilitySection A)
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0)
    (hunitS : S (0, 0) ≅ 𝟙_ C) {d : ZMod 3} (hd : d ≠ 0)
    (h1 : mulComp hA d (-d) = 0) (h2 : mulComp hA (-d) d = 0) : False := by
  -- notation
  set σ : 𝟙_ C ⟶ A.X ⊗ A.X := η[A.X] ≫ hS.sep with hσ
  -- (d,0)-component of `σ x` vanishes
  have hR0 : A.X ◁ summandIncl hA d ≫ μ[A.X] ≫ summandProj hA 0 = 0 := by
    rw [whiskerLeft_incl_mul_proj 𝕜 hSchur hfusion hA d 0 (-d) (neg_add_cancel d),
      ← Category.assoc (summandIncl hA (-d) ⊗ₘ summandIncl hA d),
      mul_eq_mulComp 𝕜 hSchur hfusion hA, h2, zero_comp, zero_comp, comp_zero]
  have hRside : (λ_ (S (d, d))).inv ≫ 𝟙_ C ◁ summandIncl hA d ≫ σ ▷ A.X ≫
      (α_ A.X A.X A.X).hom ≫ A.X ◁ μ[A.X] ≫ (summandProj hA d ⊗ₘ summandProj hA 0) = 0 := by
    rw [MonoidalCategory.tensorHom_def', MonoidalCategory.whisker_exchange_assoc,
      MonoidalCategory.associator_naturality_right_assoc]
    simp only [← MonoidalCategory.whiskerLeft_comp_assoc, hR0,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp, comp_zero]
  -- (d,0)-component of `x σ` is `x σ₀₀`
  set k : S (d, d) ⊗ S (0, 0) ⟶ S (d, d) :=
    (summandIncl hA d ⊗ₘ summandIncl hA 0) ≫ μ[A.X] ≫ summandProj hA d with hk
  have hkIso : IsIso k := by
    have i1 : IsIso (mulComp hA d 0) :=
      isIso_mulComp 𝕜 hSchur hfusion hA d 0 (mulComp_zero_right_ne_zero 𝕜 hSchur hfusion hA hunit d)
    have i2 := isIso_incl_proj_of_eq hA (add_zero d)
    have : k = mulComp hA d 0 ≫ (summandIncl hA (d + 0) ≫ summandProj hA d) := by
      rw [hk, ← Category.assoc (summandIncl hA d ⊗ₘ summandIncl hA 0),
        mul_eq_mulComp 𝕜 hSchur hfusion hA, Category.assoc]
    rw [this]
    infer_instance
  have hLd : summandIncl hA d ▷ A.X ≫ μ[A.X] ≫ summandProj hA d =
      S (d, d) ◁ summandProj hA 0 ≫ k := by
    rw [incl_whiskerRight_mul_proj 𝕜 hSchur hfusion hA d d 0 (add_zero d)]
  have hLside : (ρ_ (S (d, d))).inv ≫ summandIncl hA d ▷ 𝟙_ C ≫ A.X ◁ σ ≫
      (α_ A.X A.X A.X).inv ≫ μ[A.X] ▷ A.X ≫ (summandProj hA d ⊗ₘ summandProj hA 0) =
        (ρ_ (S (d, d))).inv ≫ S (d, d) ◁ (σ ≫ (summandProj hA 0 ⊗ₘ summandProj hA 0)) ≫
          (α_ (S (d, d)) (S (0, 0)) (S (0, 0))).inv ≫ k ▷ S (0, 0) := by
    calc _ = (ρ_ (S (d, d))).inv ≫ S (d, d) ◁ σ ≫ (α_ (S (d, d)) A.X A.X).inv ≫
          (summandIncl hA d ▷ A.X ≫ μ[A.X] ≫ summandProj hA d) ▷ A.X ≫
            S (d, d) ◁ summandProj hA 0 := by
          rw [MonoidalCategory.tensorHom_def, ← MonoidalCategory.whisker_exchange_assoc,
            MonoidalCategory.associator_inv_naturality_left_assoc]
          simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
      _ = (ρ_ (S (d, d))).inv ≫ S (d, d) ◁ σ ≫ (α_ (S (d, d)) A.X A.X).inv ≫
          (S (d, d) ◁ summandProj hA 0 ≫ k) ▷ A.X ≫ S (d, d) ◁ summandProj hA 0 := by
          rw [hLd]
      _ = (ρ_ (S (d, d))).inv ≫ S (d, d) ◁ σ ≫ (α_ (S (d, d)) A.X A.X).inv ≫
          (S (d, d) ◁ summandProj hA 0) ▷ A.X ≫ (S (d, d) ⊗ S (0, 0)) ◁ summandProj hA 0 ≫
            k ▷ S (0, 0) := by
          rw [MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.whisker_exchange]
      _ = _ := by
          rw [MonoidalCategory.tensorHom_def]
          monoidal
  have hEq : (ρ_ (S (d, d))).inv ≫ S (d, d) ◁ (σ ≫ (summandProj hA 0 ⊗ₘ summandProj hA 0)) ≫
      (α_ (S (d, d)) (S (0, 0)) (S (0, 0))).inv ≫ k ▷ S (0, 0) = 0 := by
    rw [← hLside, ← hRside]
    have hL := sep_left_form hS (summandIncl hA d)
    have hR := sep_right_form hS (summandIncl hA d)
    rw [← hσ] at hL hR
    rw [reassoc_of% hL, reassoc_of% hR]
  have hσ00 : σ ≫ (summandProj hA 0 ⊗ₘ summandProj hA 0) = 0 := by
    have hw : S (d, d) ◁ (σ ≫ (summandProj hA 0 ⊗ₘ summandProj hA 0)) = 0 := by
      have h' : S (d, d) ◁ (σ ≫ (summandProj hA 0 ⊗ₘ summandProj hA 0)) ≫
          ((α_ (S (d, d)) (S (0, 0)) (S (0, 0))).inv ≫ k ▷ S (0, 0)) = 0 := by
        rw [← cancel_epi (ρ_ (S (d, d))).inv, comp_zero]
        simpa only [Category.assoc] using hEq
      exact (cancel_mono _).1 (h'.trans zero_comp.symm)
    have φ : S (-d, -d) ⊗ S (d, d) ≅ 𝟙_ C :=
      hfusion (-d, -d) (d, d) ≪≫ eqToIso (by
        congr 1
        exact Prod.ext (neg_add_cancel d) (neg_add_cancel d)) ≪≫ hunitS
    exact eq_zero_of_whiskerLeft_eq_zero φ _ hw
  -- degree-0 part of `μ ∘ σ = η`
  have hzero : ∀ c : ZMod 3, c ≠ 0 →
      summandIncl hA c ▷ A.X ≫ μ[A.X] ≫ summandProj hA 0 = 0 := by
    intro c hc
    have hcz : mulComp hA c (-c) = 0 := by
      rcases zmod3_cases c d hd with h | h | h
      · exact absurd h hc
      · have t : ∀ c' : ZMod 3, c' = d → mulComp hA c' (-c') = 0 := by
          rintro c' rfl
          exact h1
        exact t c h
      · have h2' : ∀ e : ZMod 3, e = d → mulComp hA (-d) e = 0 := by
          rintro e rfl
          exact h2
        have t : ∀ c' : ZMod 3, c' = -d → mulComp hA c' (-c') = 0 := by
          rintro c' rfl
          exact h2' _ (neg_neg d)
        exact t c h
    rw [incl_whiskerRight_mul_proj 𝕜 hSchur hfusion hA c 0 (-c) (add_neg_cancel c),
      ← Category.assoc (summandIncl hA c ⊗ₘ summandIncl hA (-c)),
      mul_eq_mulComp 𝕜 hSchur hfusion hA, hcz, zero_comp, zero_comp, comp_zero]
  have hη : η[A.X] ≫ summandProj hA 0 = 0 := by
    have e1 : η[A.X] = σ ≫ μ[A.X] := by rw [hσ, Category.assoc, hS.sep_mul, Category.comp_id]
    have e2 : μ[A.X] ≫ summandProj hA 0 =
        ∑ c, summandProj hA c ▷ A.X ≫ summandIncl hA c ▷ A.X ≫ μ[A.X] ≫
          summandProj hA 0 := by
      calc μ[A.X] ≫ summandProj hA 0
          = (∑ c, (summandProj hA c ≫ summandIncl hA c) ▷ A.X) ≫ μ[A.X] ≫
              summandProj hA 0 := by
            rw [← sum_whiskerRight, summand_total, MonoidalCategory.id_whiskerRight,
              Category.id_comp]
        _ = _ := by
            rw [Preadditive.sum_comp]
            simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [e1, Category.assoc, e2, Preadditive.comp_sum, Finset.sum_eq_single (0 : ZMod 3)]
    · rw [incl_whiskerRight_mul_proj 𝕜 hSchur hfusion hA 0 0 0 (add_zero 0)]
      rw [← Category.assoc (summandProj hA 0 ▷ A.X), ← MonoidalCategory.tensorHom_def,
        ← Category.assoc, hσ00, zero_comp]
    · intro c _ hc
      rw [hzero c hc, comp_zero, comp_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  obtain ⟨u, hu⟩ := hunit
  have hu0 : u = 0 := by
    rw [← Category.comp_id u, ← summandIncl_proj_self hA 0, ← Category.assoc, ← hu, hη]
  have hη0 : η[A.X] = 0 := by rw [hu, hu0, zero_comp]
  apply summandIncl_ne_zero 𝕜 hSchur hA 0
  have hid : 𝟙 A.X = 0 := by
    rw [← Iso.inv_hom_id_assoc (λ_ A.X) (𝟙 A.X), Category.comp_id, ← MonObj.one_mul A.X, hη0,
      MonoidalPreadditive.zero_whiskerRight, zero_comp, comp_zero]
  rw [← Category.comp_id (summandIncl hA 0), hid, comp_zero]

include hSchur hfusion in
/-- **`hnondeg` from separability**: for an algebra `A ≅ ⊕_{c ∈ ℤ/3} S (c, c)` with a
separability section whose unit lies in `S (0, 0) ≅ 𝟙_ C`, all pairing components
`mulComp hA d (-d)` are nonzero. -/
theorem mulComp_pairing_ne_zero_of_separable (hS : SeparabilitySection A)
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0)
    (hunitS : S (0, 0) ≅ 𝟙_ C) (d : ZMod 3) : mulComp hA d (-d) ≠ 0 := by
  by_cases hd : d = 0
  · subst hd
    exact mulComp_zero_left_ne_zero 𝕜 hSchur hfusion hA hunit _
  · intro h1
    by_cases h2 : mulComp hA (-d) d = 0
    · exact not_pairing_zero_of_separable 𝕜 hSchur hfusion hA hS hunit hunitS hd h1 h2
    · exact mulComp_pairing_swap 𝕜 hSchur hfusion hA hunit h2 h1

variable [MonoidalLinear 𝕜 C] [IsIdempotentComplete C]

include hSchur hfusion in
/-- The equivalence `freeLminus_isEquivalence` from: `hSchur`, `hfusion`, `hA`, a separability
section of `A`, `hunit`, `S (0, 0) ≅ 𝟙_ C`, `3 ≠ 0`, `hss` and idempotent completeness. -/
theorem freeLminus_isEquivalence_separable (hS : SeparabilitySection A)
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0)
    (hunitS : S (0, 0) ≅ 𝟙_ C) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    (freeLminus A S).IsEquivalence :=
  freeLminus_isEquivalence_categorical 𝕜 hSchur hfusion hA hunit
    (mulComp_pairing_ne_zero_of_separable 𝕜 hSchur hfusion hA hS hunit hunitS) h3 hss

include hSchur hfusion in
/-- **The count `9/3 = 3`** from: `hSchur`, `hfusion`, `hA`, a separability section of `A`,
`hunit`, `S (0, 0) ≅ 𝟙_ C`, `3 ≠ 0`, `hss` and idempotent completeness. -/
theorem netCount_simple_modules_separable (hS : SeparabilitySection A)
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0)
    (hunitS : S (0, 0) ≅ 𝟙_ C) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    (∀ a : ZMod 3, Simple (free A (S (a, -a)))) ∧
      (∀ a b : ZMod 3, Nonempty (free A (S (a, -a)) ≅ free A (S (b, -b))) ↔ a = b) ∧
      ∀ M : RightMod A, Simple M → ∃! a : ZMod 3, Nonempty (M ≅ free A (S (a, -a))) :=
  netCount_simple_modules_categorical 𝕜 hSchur hfusion hA hunit
    (mulComp_pairing_ne_zero_of_separable 𝕜 hSchur hfusion hA hS hunit hunitS) h3 hss

end Separable

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.sep_left_form
#print axioms HaagerupIzumi.C8.RightMod.sep_right_form
#print axioms HaagerupIzumi.C8.RightMod.eq_zero_of_whiskerLeft_eq_zero
#print axioms HaagerupIzumi.C8.RightMod.mulComp_pairing_swap
#print axioms HaagerupIzumi.C8.RightMod.not_pairing_zero_of_separable
#print axioms HaagerupIzumi.C8.RightMod.mulComp_pairing_ne_zero_of_separable
#print axioms HaagerupIzumi.C8.RightMod.freeLminus_isEquivalence_separable
#print axioms HaagerupIzumi.C8.RightMod.netCount_simple_modules_separable
