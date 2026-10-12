module

public import HaagerupIzumi.C8.Lattice.ModelVacuum

@[expose] public section

/-!
# The Fock model is generated from the vacuum by 24 fields

Benchmark item 4 (`Lattice/Benchmark.md` §5): toward reducing `FLMInput.L0`, `FLMInput.Lm1`
to finitely many checks.  This file proves, from the definitions of the modes alone, that the
Fock model `V` (`Lattice/Model.lean`) is spanned by the vectors
`b¹_(n₁) ⋯ bᵏ_(nₖ) 𝟏` with every `bⁱ` among the 24 fields

* `hᵢ(-1)𝟏` (`hV i`, `i < 8`), whose modes are the Heisenberg modes (`modeC_hV`), and
* `e^{±αᵢ}` (`eV`, the simple roots and their negatives), whose lowest nonzero mode shifts the
  momentum: `(e^α)_(-(α,γ)-1) e^γ = ε(α,γ) e^{α+γ}` (`modeC_eV_lower`).

`GenClosed W`: `W` contains `𝟏` and is stable under all modes of the 24 fields;
`eq_top_of_genClosed`: such a `W` is all of `V`.  Every canonical monomial
`h_{k₁}(-n₁) ⋯ h_{kₘ}(-nₘ) e^β` is reached: `e^β` by induction over the coordinates of `β`
(steps `±αᵢ`), then the oscillators one at a time (codes in increasing order).

No hypotheses.
-/

namespace HaagerupIzumi.C8
namespace LatticeVOA

/-! ## The 24 generating fields -/

/-- `hᵢ(-1)𝟏` as a canonical monomial. -/
def hState (i : ℕ) : ValidState := ⟨(Mom.zero, [i]), List.pairwise_singleton _ _⟩

/-- `e^β` as a canonical monomial. -/
def eState (β : Mom) : ValidState := ⟨(β, []), List.Pairwise.nil⟩

/-- `hᵢ(-1)𝟏 ∈ V`. -/
noncomputable def hV (i : ℕ) : V := Finsupp.single (hState i) 1

/-- `e^β ∈ V`. -/
noncomputable def eV (β : Mom) : V := Finsupp.single (eState β) 1

/-- The 24 fields `hᵢ(-1)𝟏`, `e^{αᵢ}`, `e^{-αᵢ}` (`i < 8`). -/
noncomputable def GenSet : Set V :=
  {x | ∃ i < 8, x = hV i ∨ x = eV (Mom.simple i) ∨ x = eV (Mom.neg (Mom.simple i))}

/-- `W` contains the vacuum and is stable under all modes of the 24 fields. -/
def GenClosed (W : Submodule ℂ V) : Prop :=
  vacV ∈ W ∧ ∀ b ∈ GenSet, ∀ n : ℤ, ∀ w ∈ W, modeC n b w ∈ W

/-! ## Heisenberg creation -/

theorem gbinom_zero_right (a : ℤ) : gbinom a 0 = 1 := by
  simp [gbinom, descProd]

theorem Mom.norm_zero' : Mom.norm Mom.zero = 0 := Mom.form_zero_left _

/-- The terms of the recursion for `hᵢ(-1)𝟏` in which `e⁰` acts with a mode other than `-1`
vanish. -/
theorem toFock_foldr_bind_vertex_zero (c : ℕ → ℚ) (H : ℕ → Vec) (F : ℕ → ℤ)
    (hF : ∀ j, F j ≠ -1) (l : List ℕ) :
    toFock (l.foldr (fun j acc =>
      addVec (smul (c j) (bindVec (H j) (basisModeAux Mom.zero [] (F j)))) acc) []) = 0 := by
  rw [toFock_foldr_addVec]
  refine List.sum_eq_zero fun x hx => ?_
  rw [List.mem_map] at hx
  obtain ⟨j, -, rfl⟩ := hx
  rw [toFock_smul, toFock_bindVec]
  have hz : (fun s => toFock (basisModeAux Mom.zero [] (F j) s)) = fun _ => 0 := by
    funext s
    rw [show basisModeAux Mom.zero [] (F j) s = vertexOp Mom.zero (F j) s from rfl,
      toFock_vertexOp_zero, if_neg (hF j)]
  rw [hz]
  simp [Finsupp.linearCombination_apply]

/-- The only term of the recursion in which `e⁰` acts by its mode `-1`. -/
theorem toFock_foldr_vertex_single (c : ℕ → ℚ) (v : State) (F : ℕ → ℤ) (G : ℕ → State → Vec)
    (l : List ℕ) (j₀ : ℕ) (hnd : l.Nodup) (hj₀ : j₀ ∈ l) (hF : ∀ j, F j = -1 ↔ j = j₀) :
    toFock (l.foldr (fun j acc =>
      addVec (smul (c j) (bindVec (basisModeAux Mom.zero [] (F j) v) (G j))) acc) []) =
      c j₀ • toFock (G j₀ v) := by
  rw [toFock_foldr_addVec, list_sum_map_eq_single _ j₀ l hnd hj₀ ?_]
  · rw [toFock_smul, toFock_bindVec,
      show basisModeAux Mom.zero [] (F j₀) v = vertexOp Mom.zero (F j₀) v from rfl,
      toFock_vertexOp_zero, if_pos ((hF j₀).2 rfl), Finsupp.linearCombination_single, one_smul]
  · intro j _ hj
    rw [toFock_smul, toFock_bindVec,
      show basisModeAux Mom.zero [] (F j) v = vertexOp Mom.zero (F j) v from rfl,
      toFock_vertexOp_zero, if_neg (fun h => hj ((hF j).1 h)), map_zero, smul_zero]

/-- `(hᵢ(-1)𝟏)_(-n)` is the Heisenberg creation operator `hᵢ(-n)` (code `k = i + 8(n-1)`). -/
theorem toFock_basisModeAux_h (k : ℕ) (β : Mom) (ks : List ℕ) :
    toFock (basisModeAux Mom.zero [k % 8] (-(((k / 8 : ℕ) : ℤ) + 1)) (β, ks)) =
      toFock (heis (k % 8) (-(((k / 8 : ℕ) : ℤ) + 1)) (β, ks)) := by
  have h1 : k % 8 % 8 = k % 8 := Nat.mod_mod k 8
  have h2 : k % 8 / 8 = 0 := Nat.div_eq_of_lt (Nat.mod_lt k (by norm_num))
  have hn0 := Mom.norm_zero'
  rw [basisModeAux.eq_2]
  simp only [h1, h2]
  rw [toFock_addVec, toFock_foldr_vertex_single _ _ _ _ _ (k / 8) List.nodup_range ?_ ?_,
    toFock_foldr_bind_vertex_zero _ _ _ ?_, add_zero]
  · simp [gbinom_zero_right]
  · intro j h
    omega
  · rw [List.mem_range]
    simp only [oscGrade, h2]
    omega
  · intro j
    constructor <;> intro h <;> omega

/-- **Heisenberg creation in `V`**: `(h_{k%8}(-1)𝟏)_(-(k/8+1))` prepends the code `k` to a
monomial whose codes are all `≥ k`. -/
theorem modeC_hV (k : ℕ) (β : Mom) (ks : List ℕ) (hks : ∀ x ∈ ks, k ≤ x) (hv : Valid (β, ks))
    (hv' : Valid (β, k :: ks)) :
    modeC (-(((k / 8 : ℕ) : ℤ) + 1)) (hV (k % 8)) (Finsupp.single ⟨(β, ks), hv⟩ 1) =
      Finsupp.single ⟨(β, k :: ks), hv'⟩ 1 := by
  rw [hV, modeC_single, one_mul, one_smul]
  show push (toFock (basisModeAux Mom.zero [k % 8] (-(((k / 8 : ℕ) : ℤ) + 1)) (β, ks))) = _
  rw [toFock_basisModeAux_h, toFock_heis_create k β ks hks, push_single,
    canon_of_valid hv', Rat.cast_one]

/-! ## Momentum shifts -/

theorem schur_toNat_zero (α : Mom) {d : ℤ} (hd : d = 0) :
    schur α d.toNat = [((Mom.zero, []), 1)] := by
  rw [hd, Int.toNat_zero, schur_zero]

/-- `(e^α)_(-(α,γ)-1) e^γ = ε(α,γ) e^{α+γ}` (the lowest term of `E⁻(-α,z)`). -/
theorem toFock_vertexOp_lower (α γ : Mom) :
    toFock (vertexOp α (-Mom.form α γ - 1) (γ, [])) =
      Mom.eps α γ • Finsupp.single (Mom.add α γ, []) 1 := by
  simp only [vertexOp]
  rw [show contract α ([] : List ℕ) = [([], 1, 0)] from rfl, List.foldr_cons, List.foldr_nil,
    if_neg ?_, schur_toNat_zero α ?_]
  · simp [mergeOsc, toFock_addVec, toFock_smul]
  all_goals (try dsimp only)
  all_goals (try push_cast)
  all_goals omega

theorem modeC_eV_lower (α γ : Mom) :
    modeC (-Mom.form α γ - 1) (eV α) (eV γ) = ((Mom.eps α γ : ℚ) : ℂ) • eV (Mom.add α γ) := by
  unfold eV
  rw [modeC_single, one_mul, one_smul]
  show push (toFock (vertexOp α (-Mom.form α γ - 1) (γ, []))) = _
  rw [toFock_vertexOp_lower, push_smul, push_single,
    canon_of_valid (s := (Mom.add α γ, [])) List.Pairwise.nil, Rat.cast_one]
  rfl

theorem eps_ne_zero (α γ : Mom) : ((Mom.eps α γ : ℚ) : ℂ) ≠ 0 := by
  unfold Mom.eps
  split_ifs <;> norm_num

theorem eV_add_mem {W : Submodule ℂ V} (hW : GenClosed W) {α γ : Mom} (hα : eV α ∈ GenSet)
    (hγ : eV γ ∈ W) : eV (Mom.add α γ) ∈ W := by
  have h := hW.2 (eV α) hα (-Mom.form α γ - 1) (eV γ) hγ
  rw [modeC_eV_lower] at h
  exact (Submodule.smul_mem_iff W (eps_ne_zero α γ)).1 h

/-- Every `e^β` lies in a `GenClosed` subspace. -/
theorem eV_mem {W : Submodule ℂ V} (hW : GenClosed W) : ∀ β : Mom, eV β ∈ W := by
  have up : ∀ i < 8, ∀ γ, eV γ ∈ W → eV (Mom.add (Mom.simple i) γ) ∈ W :=
    fun i hi _ hγ => eV_add_mem hW ⟨i, hi, Or.inr (Or.inl rfl)⟩ hγ
  have dn : ∀ i < 8, ∀ γ, eV γ ∈ W → eV (Mom.add (Mom.neg (Mom.simple i)) γ) ∈ W :=
    fun i hi _ hγ => eV_add_mem hW ⟨i, hi, Or.inr (Or.inr rfl)⟩ hγ
  have L8 : eV ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ ∈ W := hW.1
  have L7 : ∀ x7 : ℤ, eV ⟨0, 0, 0, 0, 0, 0, 0, x7⟩ ∈ W := by
    intro x7
    induction x7 with
    | zero => exact L8
    | succ n ih =>
      rw [show (⟨0, 0, 0, 0, 0, 0, 0, (n : ℤ) + 1⟩ : Mom) =
          Mom.add (Mom.simple 7) ⟨0, 0, 0, 0, 0, 0, 0, (n : ℤ)⟩ by
        simp only [Mom.add, Mom.simple, Mom.mk.injEq, zero_add, add_zero, true_and, and_true]; omega]
      exact up 7 (by norm_num) _ ih
    | pred n ih =>
      rw [show (⟨0, 0, 0, 0, 0, 0, 0, -(n : ℤ) - 1⟩ : Mom) =
          Mom.add (Mom.neg (Mom.simple 7)) ⟨0, 0, 0, 0, 0, 0, 0, -(n : ℤ)⟩ by
        simp only [Mom.add, Mom.neg, Mom.simple, Mom.mk.injEq, zero_add, add_zero, neg_zero, true_and,
          and_true]; omega]
      exact dn 7 (by norm_num) _ ih
  have L6 : ∀ x6 x7 : ℤ, eV ⟨0, 0, 0, 0, 0, 0, x6, x7⟩ ∈ W := by
    intro x6 x7
    induction x6 with
    | zero => exact L7 x7
    | succ n ih =>
      rw [show (⟨0, 0, 0, 0, 0, 0, (n : ℤ) + 1, x7⟩ : Mom) =
          Mom.add (Mom.simple 6) ⟨0, 0, 0, 0, 0, 0, (n : ℤ), x7⟩ by
        simp only [Mom.add, Mom.simple, Mom.mk.injEq, zero_add, add_zero, true_and, and_true]; omega]
      exact up 6 (by norm_num) _ ih
    | pred n ih =>
      rw [show (⟨0, 0, 0, 0, 0, 0, -(n : ℤ) - 1, x7⟩ : Mom) =
          Mom.add (Mom.neg (Mom.simple 6)) ⟨0, 0, 0, 0, 0, 0, -(n : ℤ), x7⟩ by
        simp only [Mom.add, Mom.neg, Mom.simple, Mom.mk.injEq, zero_add, add_zero, neg_zero, true_and,
          and_true]; omega]
      exact dn 6 (by norm_num) _ ih
  have L5 : ∀ x5 x6 x7 : ℤ, eV ⟨0, 0, 0, 0, 0, x5, x6, x7⟩ ∈ W := by
    intro x5 x6 x7
    induction x5 with
    | zero => exact L6 x6 x7
    | succ n ih =>
      rw [show (⟨0, 0, 0, 0, 0, (n : ℤ) + 1, x6, x7⟩ : Mom) =
          Mom.add (Mom.simple 5) ⟨0, 0, 0, 0, 0, (n : ℤ), x6, x7⟩ by
        simp only [Mom.add, Mom.simple, Mom.mk.injEq, zero_add, add_zero, true_and, and_true]; omega]
      exact up 5 (by norm_num) _ ih
    | pred n ih =>
      rw [show (⟨0, 0, 0, 0, 0, -(n : ℤ) - 1, x6, x7⟩ : Mom) =
          Mom.add (Mom.neg (Mom.simple 5)) ⟨0, 0, 0, 0, 0, -(n : ℤ), x6, x7⟩ by
        simp only [Mom.add, Mom.neg, Mom.simple, Mom.mk.injEq, zero_add, add_zero, neg_zero, true_and,
          and_true]; omega]
      exact dn 5 (by norm_num) _ ih
  have L4 : ∀ x4 x5 x6 x7 : ℤ, eV ⟨0, 0, 0, 0, x4, x5, x6, x7⟩ ∈ W := by
    intro x4 x5 x6 x7
    induction x4 with
    | zero => exact L5 x5 x6 x7
    | succ n ih =>
      rw [show (⟨0, 0, 0, 0, (n : ℤ) + 1, x5, x6, x7⟩ : Mom) =
          Mom.add (Mom.simple 4) ⟨0, 0, 0, 0, (n : ℤ), x5, x6, x7⟩ by
        simp only [Mom.add, Mom.simple, Mom.mk.injEq, zero_add, add_zero, true_and, and_true]; omega]
      exact up 4 (by norm_num) _ ih
    | pred n ih =>
      rw [show (⟨0, 0, 0, 0, -(n : ℤ) - 1, x5, x6, x7⟩ : Mom) =
          Mom.add (Mom.neg (Mom.simple 4)) ⟨0, 0, 0, 0, -(n : ℤ), x5, x6, x7⟩ by
        simp only [Mom.add, Mom.neg, Mom.simple, Mom.mk.injEq, zero_add, add_zero, neg_zero, true_and,
          and_true]; omega]
      exact dn 4 (by norm_num) _ ih
  have L3 : ∀ x3 x4 x5 x6 x7 : ℤ, eV ⟨0, 0, 0, x3, x4, x5, x6, x7⟩ ∈ W := by
    intro x3 x4 x5 x6 x7
    induction x3 with
    | zero => exact L4 x4 x5 x6 x7
    | succ n ih =>
      rw [show (⟨0, 0, 0, (n : ℤ) + 1, x4, x5, x6, x7⟩ : Mom) =
          Mom.add (Mom.simple 3) ⟨0, 0, 0, (n : ℤ), x4, x5, x6, x7⟩ by
        simp only [Mom.add, Mom.simple, Mom.mk.injEq, zero_add, add_zero, true_and, and_true]; omega]
      exact up 3 (by norm_num) _ ih
    | pred n ih =>
      rw [show (⟨0, 0, 0, -(n : ℤ) - 1, x4, x5, x6, x7⟩ : Mom) =
          Mom.add (Mom.neg (Mom.simple 3)) ⟨0, 0, 0, -(n : ℤ), x4, x5, x6, x7⟩ by
        simp only [Mom.add, Mom.neg, Mom.simple, Mom.mk.injEq, zero_add, add_zero, neg_zero, true_and,
          and_true]; omega]
      exact dn 3 (by norm_num) _ ih
  have L2 : ∀ x2 x3 x4 x5 x6 x7 : ℤ, eV ⟨0, 0, x2, x3, x4, x5, x6, x7⟩ ∈ W := by
    intro x2 x3 x4 x5 x6 x7
    induction x2 with
    | zero => exact L3 x3 x4 x5 x6 x7
    | succ n ih =>
      rw [show (⟨0, 0, (n : ℤ) + 1, x3, x4, x5, x6, x7⟩ : Mom) =
          Mom.add (Mom.simple 2) ⟨0, 0, (n : ℤ), x3, x4, x5, x6, x7⟩ by
        simp only [Mom.add, Mom.simple, Mom.mk.injEq, zero_add, add_zero, true_and, and_true]; omega]
      exact up 2 (by norm_num) _ ih
    | pred n ih =>
      rw [show (⟨0, 0, -(n : ℤ) - 1, x3, x4, x5, x6, x7⟩ : Mom) =
          Mom.add (Mom.neg (Mom.simple 2)) ⟨0, 0, -(n : ℤ), x3, x4, x5, x6, x7⟩ by
        simp only [Mom.add, Mom.neg, Mom.simple, Mom.mk.injEq, zero_add, add_zero, neg_zero, true_and,
          and_true]; omega]
      exact dn 2 (by norm_num) _ ih
  have L1 : ∀ x1 x2 x3 x4 x5 x6 x7 : ℤ, eV ⟨0, x1, x2, x3, x4, x5, x6, x7⟩ ∈ W := by
    intro x1 x2 x3 x4 x5 x6 x7
    induction x1 with
    | zero => exact L2 x2 x3 x4 x5 x6 x7
    | succ n ih =>
      rw [show (⟨0, (n : ℤ) + 1, x2, x3, x4, x5, x6, x7⟩ : Mom) =
          Mom.add (Mom.simple 1) ⟨0, (n : ℤ), x2, x3, x4, x5, x6, x7⟩ by
        simp only [Mom.add, Mom.simple, Mom.mk.injEq, zero_add, add_zero, true_and, and_true]; omega]
      exact up 1 (by norm_num) _ ih
    | pred n ih =>
      rw [show (⟨0, -(n : ℤ) - 1, x2, x3, x4, x5, x6, x7⟩ : Mom) =
          Mom.add (Mom.neg (Mom.simple 1)) ⟨0, -(n : ℤ), x2, x3, x4, x5, x6, x7⟩ by
        simp only [Mom.add, Mom.neg, Mom.simple, Mom.mk.injEq, zero_add, add_zero, neg_zero, true_and,
          and_true]; omega]
      exact dn 1 (by norm_num) _ ih
  have L0 : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : ℤ, eV ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ ∈ W := by
    intro x0 x1 x2 x3 x4 x5 x6 x7
    induction x0 with
    | zero => exact L1 x1 x2 x3 x4 x5 x6 x7
    | succ n ih =>
      rw [show (⟨(n : ℤ) + 1, x1, x2, x3, x4, x5, x6, x7⟩ : Mom) =
          Mom.add (Mom.simple 0) ⟨(n : ℤ), x1, x2, x3, x4, x5, x6, x7⟩ by
        simp only [Mom.add, Mom.simple, Mom.mk.injEq, zero_add, add_zero, true_and, and_true]; omega]
      exact up 0 (by norm_num) _ ih
    | pred n ih =>
      rw [show (⟨-(n : ℤ) - 1, x1, x2, x3, x4, x5, x6, x7⟩ : Mom) =
          Mom.add (Mom.neg (Mom.simple 0)) ⟨-(n : ℤ), x1, x2, x3, x4, x5, x6, x7⟩ by
        simp only [Mom.add, Mom.neg, Mom.simple, Mom.mk.injEq, zero_add, add_zero, neg_zero, true_and,
          and_true]; omega]
      exact dn 0 (by norm_num) _ ih
  rintro ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  exact L0 x0 x1 x2 x3 x4 x5 x6 x7

/-! ## Oscillators and the conclusion -/

theorem single_mem_of_genClosed {W : Submodule ℂ V} (hW : GenClosed W) :
    ∀ (osc : List ℕ) (β : Mom) (hv : Valid (β, osc)),
      Finsupp.single (⟨(β, osc), hv⟩ : ValidState) (1 : ℂ) ∈ W
  | [], β, _ => eV_mem hW β
  | k :: ks, β, hv => by
    have hv' : Valid (β, ks) := (List.pairwise_cons.1 hv).2
    have hks : ∀ x ∈ ks, k ≤ x := (List.pairwise_cons.1 hv).1
    rw [← modeC_hV k β ks hks hv' hv]
    exact hW.2 _ ⟨k % 8, Nat.mod_lt k (by norm_num), Or.inl rfl⟩ _ _
      (single_mem_of_genClosed hW ks β hv')

/-- **Generation**: a subspace containing `𝟏` and stable under the modes of the 24 fields
`hᵢ(-1)𝟏`, `e^{±αᵢ}` is all of `V`. -/
theorem eq_top_of_genClosed {W : Submodule ℂ V} (hW : GenClosed W) : W = ⊤ := by
  rw [eq_top_iff]
  rintro f -
  induction f using Finsupp.induction_linear with
  | zero => exact W.zero_mem
  | add f g hf hg => exact W.add_mem hf hg
  | single s c =>
    obtain ⟨⟨β, osc⟩, hv⟩ := s
    have h := single_mem_of_genClosed hW osc β hv
    have e : Finsupp.single (⟨(β, osc), hv⟩ : ValidState) c =
        c • Finsupp.single (⟨(β, osc), hv⟩ : ValidState) (1 : ℂ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e]
    exact W.smul_mem c h

#print axioms modeC_hV
#print axioms modeC_eV_lower
#print axioms eq_top_of_genClosed

end LatticeVOA
end HaagerupIzumi.C8
