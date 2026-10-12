module

public import HaagerupIzumi.C8.Category.FreeModuleEssSurj

@[expose] public section

/-! # `H/B` is a twisted group algebra of `L₊`

Removes the hypothesis structure `TwistedGroupAlgebra` from the `L_untwisted` chain
(`Category/FreeModuleGraded.lean`, `FreeModuleTwistedSeparable.lean`, `FreeModuleEssSurj.lean`)
in favour of a more primitive statement.  Let `A ≅ ⊕_{c ∈ ℤ/3} S (c, c)` (`hA`: `H/B` as an
object of `Rep(B)` is the sum of the invertibles of `L₊`) in a `𝕜`-linear category whose
invertibles `S v` satisfy `hSchur` and `hfusion`.

* `mulComp hA c d : S (c,c) ⊗ S (d,d) ⟶ S (c+d, c+d)`: the homogeneous component of the
  multiplication of `A`.
* `mul_proj_eq_zero`: the components into `S (e,e)`, `e ≠ c + d`, vanish (Schur:
  `Hom(S v ⊗ S w, S u) ≅ Hom(S (v + w), S u) = 0`); `mul_eq_mulComp`: hence
  `μ ∘ (incl_c ⊗ incl_d) = incl_{c+d} ∘ mulComp c d`.
* `isIso_mulComp`: a nonzero `mulComp c d` is an isomorphism (`Hom(S(c,c) ⊗ S(d,d),
  S(c+d,c+d))` is one-dimensional, spanned by the isomorphism `hfusion`).
* `twistedGroupAlgebraOfMulNeZero`: if all nine components `mulComp c d` are nonzero, `A` is a
  `TwistedGroupAlgebra`; `free_essSurj_Lminus_of_mul_ne_zero`, `retractFree_Lplus_of_mul_ne_zero`:
  the main results of the chain with this hypothesis.

Hypothesis `hmul` (all homogeneous components of the multiplication of `H/B` are nonzero): for
the simple vertex operator algebra `H = ⊕_{ℓ ∈ L₊} ℓ` this is the non-vanishing of products of
nonzero homogeneous vectors in a simple VOA (`Y(u, z) v ≠ 0` for `u, v ≠ 0`; Dong–Lepowsky,
*Generalized vertex algebras and relative vertex operators*, 1993, Prop. 11.9).  Passing from
`Y(u, z) v ≠ 0` to `mulComp hA c d ≠ 0` uses the Huang–Kirillov–Lepowsky correspondence
between VOA extensions of `B` and commutative algebras in `Rep(B)` (the multiplication of the
algebra `H/B` restricted to `S (c,c) ⊗ S (d,d)` is the intertwining operator given by `Y`).
Both are external inputs here, phrased as the single hypothesis `hmul`.  No certificate
inputs. -/

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

/-- The homogeneous component `S (c,c) ⊗ S (d,d) ⟶ S (c+d, c+d)` of the multiplication. -/
noncomputable def mulComp (c d : ZMod 3) : S (c, c) ⊗ S (d, d) ⟶ S (c + d, c + d) :=
  (summandIncl hA c ⊗ₘ summandIncl hA d) ≫ μ[A.X] ≫ summandProj hA (c + d)

omit [MonoidalPreadditive C] in
include hSchur hfusion in
/-- The components of the multiplication into the wrong summands vanish (Schur). -/
theorem mul_proj_eq_zero (c d e : ZMod 3) (he : e ≠ c + d) :
    (summandIncl hA c ⊗ₘ summandIncl hA d) ≫ μ[A.X] ≫ summandProj hA e = 0 := by
  have h0 : finrank 𝕜 (S (c, c) ⊗ S (d, d) ⟶ S (e, e)) = 0 := by
    rw [(Linear.homCongr 𝕜 (hfusion (c, c) (d, d)) (Iso.refl (S (e, e)))).finrank_eq, hSchur,
      if_neg]
    intro h
    exact he (congrArg Prod.fst h).symm
  have : Subsingleton (S (c, c) ⊗ S (d, d) ⟶ S (e, e)) := Module.finrank_zero_iff.1 h0
  exact Subsingleton.elim _ _

omit [MonoidalPreadditive C] in
include hSchur hfusion in
/-- `μ ∘ (incl_c ⊗ incl_d) = incl_{c+d} ∘ mulComp c d`. -/
theorem mul_eq_mulComp (c d : ZMod 3) :
    (summandIncl hA c ⊗ₘ summandIncl hA d) ≫ μ[A.X] =
      mulComp hA c d ≫ summandIncl hA (c + d) := by
  calc (summandIncl hA c ⊗ₘ summandIncl hA d) ≫ μ[A.X]
      = (summandIncl hA c ⊗ₘ summandIncl hA d) ≫ μ[A.X] ≫
          ∑ e, summandProj hA e ≫ summandIncl hA e := by
        rw [summand_total, Category.comp_id]
    _ = ∑ e, ((summandIncl hA c ⊗ₘ summandIncl hA d) ≫ μ[A.X] ≫ summandProj hA e) ≫
          summandIncl hA e := by
        simp only [Preadditive.comp_sum, Category.assoc]
    _ = ((summandIncl hA c ⊗ₘ summandIncl hA d) ≫ μ[A.X] ≫ summandProj hA (c + d)) ≫
          summandIncl hA (c + d) := by
        refine Finset.sum_eq_single (c + d) (fun e _ he => ?_)
          (fun h => absurd (Finset.mem_univ _) h)
        rw [mul_proj_eq_zero 𝕜 hSchur hfusion hA c d e he, Limits.zero_comp]
    _ = mulComp hA c d ≫ summandIncl hA (c + d) := rfl

omit [MonoidalPreadditive C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] in
include hSchur hfusion in
/-- A nonzero homogeneous component of the multiplication is an isomorphism. -/
theorem isIso_mulComp (c d : ZMod 3) (hne : mulComp hA c d ≠ 0) : IsIso (mulComp hA c d) := by
  have φ : S (c, c) ⊗ S (d, d) ≅ S (c + d, c + d) := hfusion (c, c) (d, d)
  have h1 : finrank 𝕜 (S (c, c) ⊗ S (d, d) ⟶ S (c + d, c + d)) = 1 := by
    rw [(Linear.homCongr 𝕜 φ (Iso.refl _)).finrank_eq, hSchur, if_pos rfl]
  have hφ : φ.hom ≠ 0 := by
    intro h
    apply id_ne_zero_of_finrank_eq_one 𝕜 (M := S (c + d, c + d)) (by rw [hSchur, if_pos rfl])
    rw [← φ.inv_hom_id, h, Limits.comp_zero]
  obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' φ.hom hφ).1 h1 (mulComp hA c d)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact hne ht.symm
  refine ⟨⟨t⁻¹ • φ.inv, ?_, ?_⟩⟩
  · rw [← ht, Linear.smul_comp, Linear.comp_smul, smul_smul, mul_inv_cancel₀ ht0, one_smul,
      Iso.hom_inv_id]
  · rw [← ht, Linear.smul_comp, Linear.comp_smul, smul_smul, inv_mul_cancel₀ ht0, one_smul,
      Iso.inv_hom_id]

include hSchur hfusion in
/-- **`H/B` is a twisted group algebra of `L₊`**, given that the homogeneous components of
its multiplication are nonzero. -/
noncomputable def twistedGroupAlgebraOfMulNeZero (hmul : ∀ c d : ZMod 3, mulComp hA c d ≠ 0) :
    TwistedGroupAlgebra hA where
  m c d := @asIso _ _ _ _ (mulComp hA c d) (isIso_mulComp 𝕜 hSchur hfusion hA c d (hmul c d))
  mul_eq c d := mul_eq_mulComp 𝕜 hSchur hfusion hA c d

variable [MonoidalLinear 𝕜 C]

include hSchur hfusion in
/-- Every right `H/B`-module is a retract of a free module, with the separability section of
`Category/FreeModuleTwistedSeparable.lean`; hypothesis `hmul` instead of a
`TwistedGroupAlgebra` structure. -/
theorem retractFree_Lplus_of_mul_ne_zero (hmul : ∀ c d : ZMod 3, mulComp hA c d ≠ 0)
    (h3 : (3 : 𝕜) ≠ 0) (M : RightMod A) : Nonempty (Retract M (free A M.X)) :=
  retractFree_Lplus 𝕜 (twistedGroupAlgebraOfMulNeZero 𝕜 hSchur hfusion hA hmul) h3 M

include hSchur hfusion in
/-- **Every `H/B`-module is induced from `L₋`** (manuscript lines 3345–3348), with hypothesis
`hmul` instead of a `TwistedGroupAlgebra` structure. -/
theorem free_essSurj_Lminus_of_mul_ne_zero (hmul : ∀ c d : ZMod 3, mulComp hA c d ≠ 0)
    (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j)))
    (hsplit : ∀ (n : ℕ) (a : Fin n → ZMod 3)
      (e : (⨁ fun j => S (a j, -a j)) ⟶ (⨁ fun j => S (a j, -a j))), e ≫ e = e →
        ∃ (m : ℕ) (b : Fin m → ZMod 3)
          (R : Retract (⨁ fun k => S (b k, -b k)) (⨁ fun j => S (a j, -a j))), R.r ≫ R.i = e)
    (M : RightMod A) :
    ∃ (m : ℕ) (b : Fin m → ZMod 3), Nonempty (M ≅ free A (⨁ fun k => S (b k, -b k))) :=
  free_essSurj_Lminus 𝕜 A S hSchur hfusion (twistedGroupAlgebraOfMulNeZero 𝕜 hSchur hfusion hA hmul)
    h3 hss hsplit M

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.mul_proj_eq_zero
#print axioms HaagerupIzumi.C8.RightMod.mul_eq_mulComp
#print axioms HaagerupIzumi.C8.RightMod.isIso_mulComp
#print axioms HaagerupIzumi.C8.RightMod.twistedGroupAlgebraOfMulNeZero
#print axioms HaagerupIzumi.C8.RightMod.retractFree_Lplus_of_mul_ne_zero
#print axioms HaagerupIzumi.C8.RightMod.free_essSurj_Lminus_of_mul_ne_zero
