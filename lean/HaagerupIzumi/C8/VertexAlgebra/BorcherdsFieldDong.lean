module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsFieldPair
public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsDongNeg

@[expose] public section

/-!
# Dong's lemma for fields

W3, item (1), route A groundwork (`Lattice/W3_PLAN.md`, section 2).  For fields `A, B, C`
(`OpField`) that are pairwise local of order `r` and any `n ∈ ℤ`, the field product `A_(n) B`
is local with `C` (**`OpField.dong`**, order `(2r - n)⁺ + r`).  This is `dong_general`
(`VertexAlgebra/BorcherdsDongNeg.lean`) applied to the families
`Φ⁺(u, w, q) = A_u B_w C_q v - C_q A_u B_w v` and `Φ⁻(u, w, q) = B_w A_u C_q v - C_q B_w A_u v`;
the truncation of the fields replaces the grading used in `ModeAlgebra.dong_of_good`.

Also `assoc_of_local` (weak associativity on `V` for a local pair of fields, from
`borcherds_of_local`) and `eq_zero_of_dz_of_trunc`: multiplication by `(z₁ - z₂)^R` is injective on families
truncated in the second variable (the cancellation step of Li's weak-associativity argument).

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

variable {k : Type*} [Field k] in
/-- **Cancellation of `(z₁ - z₂)^R`** on families truncated in the second variable: if
`F(p, q) = 0` for `q ≥ Q` (all `p`) and `(z₁ - z₂)^R F = 0`, then `F = 0`.  (The mode form of
the cancellation step in Li's proof of weak associativity for the vertex operators on local
fields.) -/
theorem eq_zero_of_dz_of_trunc {W : Type*} [AddCommGroup W] [Module k W] (Q : ℤ) :
    ∀ (R : ℕ) (F : ℤ → ℤ → W), (∀ p q, Q ≤ q → F p q = 0) → (∀ p q, dz k R F p q = 0) →
      ∀ p q, F p q = 0 := by
  -- the case `R = 1`
  have base : ∀ G : ℤ → ℤ → W, (∀ p q, Q ≤ q → G p q = 0) →
      (∀ p q, G (p + 1) q = G p (q + 1)) → ∀ p q, G p q = 0 := by
    intro G hG hs
    have hm : ∀ m : ℕ, ∀ p, G p (Q - m) = 0 := by
      intro m
      induction m with
      | zero => intro p; exact hG p _ (by simp)
      | succ m ih =>
        intro p
        have := hs (p - 1) (Q - ((m + 1 : ℕ) : ℤ))
        rw [sub_add_cancel, show Q - ((m + 1 : ℕ) : ℤ) + 1 = Q - m by push_cast; ring,
          ih] at this
        exact this
    intro p q
    by_cases h : Q ≤ q
    · exact hG p q h
    · have := hm (Q - q).toNat p
      rwa [show Q - ((Q - q).toNat : ℤ) = q by omega] at this
  intro R
  induction R with
  | zero => intro F _ hd p q; rw [← dz_zero k F p q]; exact hd p q
  | succ R ih =>
    intro F hF hd
    refine ih F hF (base (dz k R F) (fun p q hq => ?_) (fun p q => ?_))
    · exact Finset.sum_eq_zero fun t _ => by rw [hF _ _ (by omega), smul_zero]
    · have h := hd p q
      rw [dz_succ] at h
      exact sub_eq_zero.1 h

namespace OpField

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Locality of order `R`: `(z₁ - z₂)^R [A(z₁), B(z₂)] = 0`. -/
def IsLocal (A B : OpField k V) (R : ℕ) : Prop := ∀ p q, dz k R (opComm A.mode B.mode) p q = 0

/-- `Φ⁺(u, w, q) = A_u B_w C_q v - C_q A_u B_w v`. -/
def dP (A B C : OpField k V) (v : V) : ℤ → ℤ → ℤ → V := fun u w q =>
  A.mode u (B.mode w (C.mode q v)) - C.mode q (A.mode u (B.mode w v))

/-- `Φ⁻(u, w, q) = B_w A_u C_q v - C_q B_w A_u v`. -/
def dM (A B C : OpField k V) (v : V) : ℤ → ℤ → ℤ → V := fun u w q =>
  B.mode w (A.mode u (C.mode q v)) - C.mode q (B.mode w (A.mode u v))

theorem dP_mem (A B C : OpField k V) (v : V) : dP A B C v ∈ T2 k V := by
  refine mem_T2.2 fun q => ?_
  obtain ⟨N₁, h₁⟩ := B.trunc (C.mode q v)
  obtain ⟨N₂, h₂⟩ := B.trunc v
  refine ⟨max N₁ N₂, fun u w hw => ?_⟩
  show A.mode u (B.mode w (C.mode q v)) - C.mode q (A.mode u (B.mode w v)) = 0
  rw [h₁ w (le_of_max_le_left hw), h₂ w (le_of_max_le_right hw)]
  simp

theorem dM_mem (A B C : OpField k V) (v : V) : dM A B C v ∈ T1 k V := by
  refine mem_T1.2 fun q => ?_
  obtain ⟨N₁, h₁⟩ := A.trunc (C.mode q v)
  obtain ⟨N₂, h₂⟩ := A.trunc v
  refine ⟨max N₁ N₂, fun u w hu => ?_⟩
  show B.mode w (A.mode u (C.mode q v)) - C.mode q (B.mode w (A.mode u v)) = 0
  rw [h₁ u (le_of_max_le_left hu), h₂ u (le_of_max_le_right hu)]
  simp

/-- `dz` of an operator family applied to a vector. -/
theorem dz_apply_fam (R : ℕ) (F : ℤ → ℤ → Module.End k V) (x : V) (p q : ℤ) :
    dz k R (fun u w => F u w x) p q = dz k R F p q x :=
  (dz_linearMap_apply k R F p q x).symm

theorem dong_h12 (A B C : OpField k V) (v : V) {r : ℕ} (hAB : IsLocal A B r) :
    ((d12 k V) ^ r) (dP A B C v - dM A B C v) = 0 := by
  funext u w q
  rw [d12_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
  have e : (fun p' q' => (dP A B C v - dM A B C v) p' q' q) = fun p' q' =>
      (opComm A.mode B.mode p' q' * C.mode q - C.mode q * opComm A.mode B.mode p' q') v := by
    funext p' q'
    simp only [Pi.sub_apply, dP, dM, opComm, LinearMap.sub_apply, Module.End.mul_apply,
      map_sub]
    abel
  rw [e, dz_apply_fam, dz_sub_fun, dz_mul_right, dz_mul_left, hAB u w, zero_mul, mul_zero,
    sub_zero, LinearMap.zero_apply]

theorem dong_h3p (A B C : OpField k V) (v : V) {r : ℕ} (hAC : IsLocal A C r)
    (hBC : IsLocal B C r) : ((d13 k V) ^ r) (((d23 k V) ^ r) (dP A B C v)) = 0 := by
  let Θ1 : ℤ → ℤ → ℤ → V := fun u w q => (A.mode u * opComm B.mode C.mode w q) v
  let Θ2 : ℤ → ℤ → ℤ → V := fun u w q => (opComm A.mode C.mode u q * B.mode w) v
  have hsplit : dP A B C v = Θ1 + Θ2 := by
    funext u w q
    simp only [Θ1, Θ2, dP, opComm, Pi.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
      map_sub]
    abel
  have h1 : ((d23 k V) ^ r) Θ1 = 0 := by
    funext u w q
    rw [d23_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    show dz k r (fun p' q' => (A.mode u * opComm B.mode C.mode p' q') v) w q = 0
    rw [dz_apply_fam, dz_mul_left, hBC w q, mul_zero, LinearMap.zero_apply]
  have h2 : ((d13 k V) ^ r) Θ2 = 0 := by
    funext u w q
    rw [d13_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    show dz k r (fun p' q' => (opComm A.mode C.mode p' q' * B.mode w) v) u q = 0
    rw [dz_apply_fam, dz_mul_right, hAC u q, zero_mul, LinearMap.zero_apply]
  rw [hsplit, map_add, map_add, h1, map_zero, zero_add,
    comm_apply ((commute_d13_d23 (k := k) (W := V)).pow_pow r r), h2, map_zero]

theorem dong_h3m (A B C : OpField k V) (v : V) {r : ℕ} (hAC : IsLocal A C r)
    (hBC : IsLocal B C r) : ((d13 k V) ^ r) (((d23 k V) ^ r) (dM A B C v)) = 0 := by
  let Θ3 : ℤ → ℤ → ℤ → V := fun u w q => (B.mode w * opComm A.mode C.mode u q) v
  let Θ4 : ℤ → ℤ → ℤ → V := fun u w q => (opComm B.mode C.mode w q * A.mode u) v
  have hsplit : dM A B C v = Θ3 + Θ4 := by
    funext u w q
    simp only [Θ3, Θ4, dM, opComm, Pi.add_apply, LinearMap.sub_apply, Module.End.mul_apply,
      map_sub]
    abel
  have h3 : ((d13 k V) ^ r) Θ3 = 0 := by
    funext u w q
    rw [d13_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    show dz k r (fun p' q' => (B.mode w * opComm A.mode C.mode p' q') v) u q = 0
    rw [dz_apply_fam, dz_mul_left, hAC u q, mul_zero, LinearMap.zero_apply]
  have h4 : ((d23 k V) ^ r) Θ4 = 0 := by
    funext u w q
    rw [d23_pow_apply, Pi.zero_apply, Pi.zero_apply, Pi.zero_apply]
    show dz k r (fun p' q' => (opComm B.mode C.mode p' q' * A.mode u) v) w q = 0
    rw [dz_apply_fam, dz_mul_right, hBC w q, zero_mul, LinearMap.zero_apply]
  rw [hsplit, map_add, map_add, h4, map_zero, add_zero,
    comm_apply ((commute_d13_d23 (k := k) (W := V)).pow_pow r r), h3, map_zero]

/-- `[(A_(n) B)_s, C_q] v = ePlus n Φ⁺ (s, q) - eMinus n Φ⁻ (s, q)`. -/
theorem comm_prod_eq (A B C : OpField k V) (v : V) (n s q : ℤ) :
    opComm (prod n A B).mode C.mode s q v =
      ePlus k n (dP A B C v) s q - eMinus k n (dM A B C v) s q := by
  obtain ⟨M₁, h₁⟩ := prodMode_eq_sum A B n s (C.mode q v)
  obtain ⟨M₂, h₂⟩ := prodMode_eq_sum A B n s v
  obtain ⟨M₃, h₃⟩ := ePlus_eq_sum (dP_mem A B C v) n s q
  obtain ⟨M₄, h₄⟩ := eMinus_eq_sum (dM_mem A B C v) n s q
  obtain ⟨M, hM1, hM2, hM3, hM4⟩ : ∃ M : ℕ, M₁ ≤ M ∧ M₂ ≤ M ∧ M₃ ≤ M ∧ M₄ ≤ M :=
    ⟨M₁ + M₂ + M₃ + M₄, by omega, by omega, by omega, by omega⟩
  show (prod n A B).mode s (C.mode q v) - C.mode q ((prod n A B).mode s v) = _
  rw [prod_mode, h₁ M hM1, h₂ M hM2, h₃ M hM3, h₄ M hM4, map_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [prodTerm, dP, dM, map_smul, map_sub]
  rw [show n + s - (t : ℤ) = n + s - t from rfl]
  module

/-- **Dong's lemma for fields**: if `A, B, C` are pairwise local of order `r`, then `A_(n) B` is
local with `C` of order `(2r - n)⁺ + r`, for every `n ∈ ℤ`. -/
theorem dong (A B C : OpField k V) {r : ℕ} (hAB : IsLocal A B r) (hAC : IsLocal A C r)
    (hBC : IsLocal B C r) (n : ℤ) :
    IsLocal (prod n A B) C ((2 * (r : ℤ) - n).toNat + r) := by
  intro p q
  refine LinearMap.ext fun v => ?_
  rw [← dz_apply_fam, LinearMap.zero_apply]
  have e : (fun u w => opComm (prod n A B).mode C.mode u w v) =
      fun u w => ePlus k n (dP A B C v) u w - eMinus k n (dM A B C v) u w :=
    funext fun u => funext fun w => comm_prod_eq A B C v n u w
  rw [e]
  exact dong_general r (2 * (r : ℤ) - n).toNat n (by omega) _ _ (dP_mem A B C v)
    (dM_mem A B C v) (dong_h12 A B C v hAB) (dong_h3p A B C v hAC hBC)
    (dong_h3m A B C v hAC hBC) p q

/-- **Weak associativity for a local pair of fields** on `v`: for `p ≥ P₀(A, v)` the `B A`
terms drop out of `borcherds_of_local`:
`∑_t (p choose t) (A_(r+t) B)_{p+q-t} v = ∑_t (-1)^t (r choose t) A_{p+r-t} B_{q+t} v`
(the mode form of `(z₀ + z₂)^p Y_E(A, z₀) B (z₂) v = (z₀ + z₂)^p A(z₀ + z₂) B(z₂) v`). -/
theorem assoc_of_local (A B : OpField k V) (N : ℕ) (hloc : IsLocal A B N) (v : V) :
    ∃ P₀ : ℤ, ∀ p, P₀ ≤ p → ∀ q r : ℤ, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M →
      lsum k (bX A B v) p q r M = ysum k (bY A B v) p q r M := by
  obtain ⟨NA, hA⟩ := A.trunc v
  refine ⟨NA, fun p hp q r => ?_⟩
  obtain ⟨M₀, hM₀⟩ := borcherds_of_local A B N hloc v p q r
  refine ⟨M₀, fun M hM => ?_⟩
  have hZ : ysum k (bZ A B v) q p r M = 0 :=
    Finset.sum_eq_zero fun t _ => by
      show _ • B.mode _ (A.mode (p + t) v) = 0
      rw [hA (p + t) (by omega), map_zero, smul_zero]
  rw [hM₀ M hM, hZ, smul_zero, sub_zero]

end OpField

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.OpField.comm_prod_eq
#print axioms HaagerupIzumi.C8.OpField.dong
#print axioms HaagerupIzumi.C8.eq_zero_of_dz_of_trunc
#print axioms HaagerupIzumi.C8.OpField.assoc_of_local
