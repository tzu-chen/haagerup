module

public import HaagerupIzumi.C8.Category.SimpleModulesLminus
public import Mathlib.CategoryTheory.Idempotents.Basic

@[expose] public section

/-! # The splitting hypothesis `hsplit` from idempotent completeness

The hypothesis `hsplit` of `free_essSurj_Lminus` (`Category/FreeModuleEssSurj.lean`),
`freeLminus_isEquivalence` (`Category/FreeModuleEquivalence.lean`) and
`netCount_simple_modules` (`Category/SimpleModulesLminus.lean`) says that every idempotent of a
finite direct sum of the invertibles `S (a, -a)` of `L₋` splits through a sub-sum of such
invertibles.  Here it is derived from more primitive statements about `Rep(B)`:

* `hsplit_of_isIdempotentComplete`: if idempotents split in `C` (`IsIdempotentComplete C`;
  Mathlib's instance `isIdempotentComplete_of_abelian` covers every abelian category, in
  particular `Rep(B)`), every object is a finite sum of the nine invertibles `S v` (`hss`),
  and `hSchur` holds, then `hsplit` holds.  Proof: the image `Y` of the idempotent is a sum
  `⊕ₖ S v_k`; each `S v_k` is a retract of `⊕ⱼ S (a_j, -a_j)` with `𝟙 ≠ 0`, so it has a
  nonzero component into some `S (a_j, -a_j)`, which forces `v_k = (a_j, -a_j) ∈ L₋` by
  `hSchur`.
* `freeLminus_isEquivalence_of_isIdempotentComplete`,
  `netCount_simple_modules_of_isIdempotentComplete`: the equivalence and the count `9/3 = 3`
  with `IsIdempotentComplete C` in place of `hsplit`.

No external-theorem or certificate inputs beyond the named hypotheses. -/

namespace HaagerupIzumi.C8

open CategoryTheory MonoidalCategory MonObj Limits Module

universe v u

variable {C : Type u} [Category.{v} C]

namespace RightMod

section Split

variable (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)] {S : ZMod 3 × ZMod 3 → C}

/-- **`hsplit` from idempotent completeness**: every idempotent of a finite sum of
`L₋`-invertibles splits through a sub-sum of `L₋`-invertibles. -/
theorem hsplit_of_isIdempotentComplete [IsIdempotentComplete C]
    (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    ∀ (n : ℕ) (a : Fin n → ZMod 3)
      (e : (⨁ fun j => S (a j, -a j)) ⟶ (⨁ fun j => S (a j, -a j))), e ≫ e = e →
        ∃ (m : ℕ) (b : Fin m → ZMod 3)
          (R : Retract (⨁ fun k => S (b k, -b k)) (⨁ fun j => S (a j, -a j))), R.r ≫ R.i = e := by
  intro n a e he
  obtain ⟨Y, i, p, hip, hpi⟩ := IsIdempotentComplete.idempotents_split _ e he
  obtain ⟨m, v, ⟨φ⟩⟩ := hss Y
  -- Every summand of the image lies in `L₋`.
  have hL : ∀ k, (v k).2 = -(v k).1 := by
    intro k
    let ι' : S (v k) ⟶ ⨁ fun j => S (a j, -a j) := biproduct.ι (fun k => S (v k)) k ≫ φ.inv ≫ i
    let r' : (⨁ fun j => S (a j, -a j)) ⟶ S (v k) := p ≫ φ.hom ≫ biproduct.π (fun k => S (v k)) k
    have hret : ι' ≫ r' = 𝟙 _ := by
      simp only [ι', r', Category.assoc, reassoc_of% hip,
        Iso.inv_hom_id_assoc, biproduct.ι_π_self]
    have hid : (𝟙 (S (v k)) : S (v k) ⟶ S (v k)) ≠ 0 :=
      id_ne_zero_of_finrank_eq_one 𝕜 (by rw [hSchur, if_pos rfl])
    obtain ⟨j, hj⟩ : ∃ j, ι' ≫ biproduct.π (fun j => S (a j, -a j)) j ≠ 0 := by
      by_contra hall
      apply hid
      have h0 : ι' = 0 := biproduct.hom_ext _ _ fun j => by
        rw [zero_comp]
        by_contra h
        exact hall ⟨j, h⟩
      rw [← hret, h0, zero_comp]
    have hva : v k = (a j, -a j) := by
      by_contra hne
      apply hj
      have h0 : finrank 𝕜 (S (v k) ⟶ S (a j, -a j)) = 0 := by rw [hSchur, if_neg hne]
      have : Subsingleton (S (v k) ⟶ S (a j, -a j)) := Module.finrank_zero_iff.1 h0
      exact Subsingleton.elim _ _
    rw [hva]
  have hv : ∀ k, v k = ((v k).1, -(v k).1) := fun k => Prod.ext rfl (hL k)
  let ψ : (⨁ fun k => S (v k)) ≅ ⨁ fun k => S ((v k).1, -(v k).1) :=
    biproduct.mapIso fun k => eqToIso (congrArg S (hv k))
  refine ⟨m, fun k => (v k).1, ⟨ψ.inv ≫ φ.inv ≫ i, p ≫ φ.hom ≫ ψ.hom, ?_⟩, ?_⟩
  · simp only [Category.assoc, reassoc_of% hip, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id]
  · simp only [Category.assoc, Iso.hom_inv_id_assoc, hpi]

end Split

variable [MonoidalCategory C]
  (𝕜 : Type*) [Field 𝕜] [Preadditive C] [Linear 𝕜 C] [MonoidalPreadditive C]
  [MonoidalLinear 𝕜 C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]
  [IsIdempotentComplete C] {A : Mon C} {S : ZMod 3 × ZMod 3 → C}
  (hSchur : ∀ v w, finrank 𝕜 (S v ⟶ S w) = if v = w then 1 else 0)
  (hfusion : ∀ v w, S v ⊗ S w ≅ S (v + w))
  (hA : A.X ≅ ⨁ fun c : ZMod 3 => S (c, c))

include hSchur hfusion in
/-- `freeLminus_isEquivalence` with `IsIdempotentComplete C` in place of `hsplit`. -/
theorem freeLminus_isEquivalence_of_isIdempotentComplete
    (hmul : ∀ c d : ZMod 3, mulComp hA c d ≠ 0) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    (freeLminus A S).IsEquivalence :=
  freeLminus_isEquivalence 𝕜 hSchur hfusion hA hmul h3 hss
    (hsplit_of_isIdempotentComplete 𝕜 hSchur hss)

include hSchur hfusion in
/-- **The count `9/3 = 3`** (`netCount_simple_modules`) with `IsIdempotentComplete C` in place
of `hsplit`. -/
theorem netCount_simple_modules_of_isIdempotentComplete
    (hmul : ∀ c d : ZMod 3, mulComp hA c d ≠ 0) (h3 : (3 : 𝕜) ≠ 0)
    (hss : ∀ X : C, ∃ (n : ℕ) (v : Fin n → ZMod 3 × ZMod 3),
      Nonempty (X ≅ ⨁ fun j => S (v j))) :
    (∀ a : ZMod 3, Simple (free A (S (a, -a)))) ∧
      (∀ a b : ZMod 3, Nonempty (free A (S (a, -a)) ≅ free A (S (b, -b))) ↔ a = b) ∧
      ∀ M : RightMod A, Simple M → ∃! a : ZMod 3, Nonempty (M ≅ free A (S (a, -a))) :=
  netCount_simple_modules 𝕜 hSchur hfusion hA hmul h3 hss
    (hsplit_of_isIdempotentComplete 𝕜 hSchur hss)

end RightMod

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.RightMod.hsplit_of_isIdempotentComplete
#print axioms HaagerupIzumi.C8.RightMod.freeLminus_isEquivalence_of_isIdempotentComplete
#print axioms HaagerupIzumi.C8.RightMod.netCount_simple_modules_of_isIdempotentComplete
