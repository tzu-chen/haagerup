module

public import HaagerupIzumi.C8.Category.LminusSplitting

@[expose] public section

/-! # `hmul` from categorical properties of `H/B`: connected unit and nondegenerate pairing

The hypothesis `hmul` of `Category/TwistedGroupAlgebraOfMul.lean` (every homogeneous component
`mulComp hA c d : S (c,c) ⊗ S (d,d) ⟶ S (c+d, c+d)` of the multiplication of `A = H/B` is
nonzero) was justified there by a VOA input (Dong–Lepowsky, through Huang–Kirillov–Lepowsky).
Here it is derived from two categorical properties of the algebra `A ≅ ⊕_{c ∈ ℤ/3} S (c, c)`:

* `hunit`: the unit of `A` factors through the degree-zero summand `S (0, 0)` (for a connected
  algebra, `A_0 = 𝟙`);
* `hnondeg`: the pairing components `mulComp hA d (-d) : S (d,d) ⊗ S (-d,-d) ⟶ S (0,0)` are
  nonzero (nondegeneracy of the multiplication pairing `A ⊗ A ⟶ A ⟶ A_0`, the Frobenius
  form of a connected separable algebra).

* `mulComp_zero_left_ne_zero`, `mulComp_zero_right_ne_zero`: from `hunit` and the unit axioms,
  `mulComp hA 0 d ≠ 0` and `mulComp hA c 0 ≠ 0`.
* `mulComp_ne_zero_of_unit_of_nondegenerate`: from these, `hnondeg` and associativity,
  `mulComp hA c d ≠ 0` for all `c, d` (if `x y = 0` then `(x y) y' = x (y y') ≠ 0` for
  `y' ∈ S (-d, -d)`).
* `netCount_simple_modules_categorical`, `freeLminus_isEquivalence_categorical`: the count
  `9/3 = 3` and the equivalence of `Category/FreeModuleEquivalence.lean` with `hmul` replaced
  by `hunit`, `hnondeg`, and `hsplit` by `IsIdempotentComplete C`
  (`Category/LminusSplitting.lean`).

`hnondeg` is derived from a separability section of `A`, `hunit` and `S (0, 0) ≅ 𝟙_ C` in
`Category/NondegFromSeparable.lean` (`mulComp_pairing_ne_zero_of_separable`), and `hunit` from
`hSchur` and `S (0, 0) ≅ 𝟙_ C` in `Category/UntwistedFromSeparable.lean` (`hunit_of_unitS`).
No certificate inputs. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits Module

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace RightMod

variable (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [MonoidalPreadditive C]
  [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]
  {A : Mon C} {S : ZMod 3 × ZMod 3 → C}
  (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
  (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
  (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c))

omit [MonoidalPreadditive C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] in
include hSchur in
/-- A summand inclusion of `A` is nonzero. -/
theorem summandIncl_ne_zero (e : ZMod 3) : summandIncl hA e ≠ 0 := by
  intro h
  apply id_ne_zero_of_finrank_eq_one 𝕜 (M := S (e, e)) (by rw [hSchur, if_pos rfl])
  rw [← summandIncl_proj_self hA e, h, zero_comp]

omit [MonoidalPreadditive C] in
include hSchur hfusion in
/-- From the unit: `mulComp hA 0 d ≠ 0`. -/
theorem mulComp_zero_left_ne_zero
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0) (d : ZMod 3) :
    mulComp hA 0 d ≠ 0 := by
  obtain ⟨u, hu⟩ := hunit
  intro h0
  have key : (λ_ (S (d, d))).hom ≫ summandIncl hA d =
      u ▷ S (d, d) ≫ mulComp hA 0 d ≫ summandIncl hA (0 + d) := by
    calc (λ_ (S (d, d))).hom ≫ summandIncl hA d
        = 𝟙_ C ◁ summandIncl hA d ≫ (λ_ A.X).hom :=
          (MonoidalCategory.leftUnitor_naturality _).symm
      _ = 𝟙_ C ◁ summandIncl hA d ≫ η[A.X] ▷ A.X ≫ μ[A.X] := by rw [MonObj.one_mul]
      _ = η[A.X] ▷ S (d, d) ≫ A.X ◁ summandIncl hA d ≫ μ[A.X] := by
          rw [MonoidalCategory.whisker_exchange_assoc]
      _ = u ▷ S (d, d) ≫ (summandIncl hA 0 ⊗ₘ summandIncl hA d) ≫ μ[A.X] := by
          rw [hu, MonoidalCategory.comp_whiskerRight_assoc, MonoidalCategory.tensorHom_def_assoc]
      _ = u ▷ S (d, d) ≫ mulComp hA 0 d ≫ summandIncl hA (0 + d) := by
          rw [mul_eq_mulComp 𝕜 hSchur hfusion hA]
  rw [h0, zero_comp, comp_zero] at key
  apply summandIncl_ne_zero 𝕜 hSchur hA d
  rw [← Iso.inv_hom_id_assoc (λ_ (S (d, d))) (summandIncl hA d), key, comp_zero]

omit [MonoidalPreadditive C] in
include hSchur hfusion in
/-- From the unit: `mulComp hA c 0 ≠ 0`. -/
theorem mulComp_zero_right_ne_zero
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0) (c : ZMod 3) :
    mulComp hA c 0 ≠ 0 := by
  obtain ⟨u, hu⟩ := hunit
  intro h0
  have key : (ρ_ (S (c, c))).hom ≫ summandIncl hA c =
      S (c, c) ◁ u ≫ mulComp hA c 0 ≫ summandIncl hA (c + 0) := by
    calc (ρ_ (S (c, c))).hom ≫ summandIncl hA c
        = summandIncl hA c ▷ 𝟙_ C ≫ (ρ_ A.X).hom :=
          (MonoidalCategory.rightUnitor_naturality _).symm
      _ = summandIncl hA c ▷ 𝟙_ C ≫ A.X ◁ η[A.X] ≫ μ[A.X] := by rw [MonObj.mul_one]
      _ = S (c, c) ◁ η[A.X] ≫ summandIncl hA c ▷ A.X ≫ μ[A.X] := by
          rw [← MonoidalCategory.whisker_exchange_assoc]
      _ = S (c, c) ◁ u ≫ (summandIncl hA c ⊗ₘ summandIncl hA 0) ≫ μ[A.X] := by
          rw [hu, MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.tensorHom_def'_assoc]
      _ = S (c, c) ◁ u ≫ mulComp hA c 0 ≫ summandIncl hA (c + 0) := by
          rw [mul_eq_mulComp 𝕜 hSchur hfusion hA]
  rw [h0, zero_comp, comp_zero] at key
  apply summandIncl_ne_zero 𝕜 hSchur hA c
  rw [← Iso.inv_hom_id_assoc (ρ_ (S (c, c))) (summandIncl hA c), key, comp_zero]

include hSchur hfusion in
/-- **`hmul` from the unit and the nondegeneracy of the pairing**: all homogeneous components
of the multiplication of `A` are nonzero. -/
theorem mulComp_ne_zero_of_unit_of_nondegenerate
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0)
    (hnondeg : ∀ d : ZMod 3, mulComp hA d (-d) ≠ 0) (c d : ZMod 3) : mulComp hA c d ≠ 0 := by
  intro h0
  have hright : ∀ e : ZMod 3, e = 0 → mulComp hA c e ≠ 0 := by
    intro e he
    subst he
    exact mulComp_zero_right_ne_zero 𝕜 hSchur hfusion hA hunit c
  have i1 : IsIso (mulComp hA d (-d)) := isIso_mulComp 𝕜 hSchur hfusion hA d (-d) (hnondeg d)
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
/-- `A` is a twisted group algebra of `L₊`, from the unit and the nondegeneracy of the
pairing. -/
noncomputable def twistedGroupAlgebraOfUnitNondeg
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0)
    (hnondeg : ∀ d : ZMod 3, mulComp hA d (-d) ≠ 0) : TwistedGroupAlgebra hA :=
  twistedGroupAlgebraOfMulNeZero 𝕜 hSchur hfusion hA
    (mulComp_ne_zero_of_unit_of_nondegenerate 𝕜 hSchur hfusion hA hunit hnondeg)

variable [MonoidalLinear 𝕜 C] [IsIdempotentComplete C]

include hSchur hfusion in
/-- The equivalence `freeLminus_isEquivalence` from categorical inputs only: `hmul` replaced by
`hunit`, `hnondeg`, and `hsplit` by `IsIdempotentComplete C`. -/
theorem freeLminus_isEquivalence_categorical
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0)
    (hnondeg : ∀ d : ZMod 3, mulComp hA d (-d) ≠ 0) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    (freeLminus A S).IsEquivalence :=
  freeLminus_isEquivalence_of_isIdempotentComplete 𝕜 hSchur hfusion hA
    (mulComp_ne_zero_of_unit_of_nondegenerate 𝕜 hSchur hfusion hA hunit hnondeg) h3 hss

include hSchur hfusion in
/-- **The count `9/3 = 3` from categorical inputs only** (`netCount_simple_modules` with
`hmul` replaced by `hunit`, `hnondeg`, and `hsplit` by `IsIdempotentComplete C`). -/
theorem netCount_simple_modules_categorical
    (hunit : ∃ u : 𝟙_ C ⟶ S (0, 0), η[A.X] = u ≫ summandIncl hA 0)
    (hnondeg : ∀ d : ZMod 3, mulComp hA d (-d) ≠ 0) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    (∀ a : ZMod 3, Simple (free A (S (a, -a)))) ∧
      (∀ a b : ZMod 3, Nonempty (free A (S (a, -a)) ≅ free A (S (b, -b))) ↔ a = b) ∧
      ∀ M : RightMod A, Simple M → ∃! a : ZMod 3, Nonempty (M ≅ free A (S (a, -a))) :=
  netCount_simple_modules_of_isIdempotentComplete 𝕜 hSchur hfusion hA
    (mulComp_ne_zero_of_unit_of_nondegenerate 𝕜 hSchur hfusion hA hunit hnondeg) h3 hss

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.mulComp_zero_left_ne_zero
#print axioms HaagerupIzumi.C8.RightMod.mulComp_zero_right_ne_zero
#print axioms HaagerupIzumi.C8.RightMod.mulComp_ne_zero_of_unit_of_nondegenerate
#print axioms HaagerupIzumi.C8.RightMod.twistedGroupAlgebraOfUnitNondeg
#print axioms HaagerupIzumi.C8.RightMod.freeLminus_isEquivalence_categorical
#print axioms HaagerupIzumi.C8.RightMod.netCount_simple_modules_categorical
