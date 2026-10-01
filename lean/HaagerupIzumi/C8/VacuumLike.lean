module

public import HaagerupIzumi.C8.VertexAlgebra.Basic
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Vacuum-like vectors (Lemma `lem:vacuum-like`)

Lemma `lem:vacuum-like` (lines 2916–2929 of the expanded draft): *Let `M` be a weak module
over a VOA `V`.  If `v ∈ M` satisfies `L_M(-1) v = 0`, then `a_n v = 0` for all `a ∈ V` and
`n ≥ 0`, and `a ↦ a_(-1) v` is a `V`-module homomorphism `V → M` sending `1` to `v`.*

The proof uses translation covariance `[L_M(-1), a_(n)] = (T a)_(n) = -n a_(n-1)`, lower
truncation, and the module iterate formula.  This file records exactly those properties of a
weak module (`WeakModule`) and proves the lemma:

* `mode_vacuumLike_nonneg` — `a_(n) v = 0` for `n ≥ 0` (downward induction from truncation);
* `vacuumLike_hom` — `b_(m) (a_(-1) v) = (b_(m) a)_(-1) v` for all `m`;
* `vacuumLike_vac` — `1_(-1) v = v`.

The lemma is used in Lemma `lem:vacuum-projective` (a weight-zero top on which every partial
energy vanishes gives a nonzero module map out of the vacuum module).
-/

namespace HaagerupIzumi.C8.VacuumLike

open HaagerupIzumi.C8

variable {k : Type*} [Field k] [CharZero k]
variable {V : Type*} [AddCommGroup V] [Module k V]
variable {M : Type*} [AddCommGroup M] [Module k M]

/-- The properties of a weak module over `A` used by Lemma `lem:vacuum-like`: lower
truncation, the vacuum axiom, translation covariance, and the module iterate formula
(each a standard consequence of the module Jacobi identity). -/
structure WeakModule (A : VertexAlgebra k V) (M : Type*) [AddCommGroup M] [Module k M] where
  /-- `act n a w = a_(n) w`. -/
  act : ℤ → V →ₗ[k] M →ₗ[k] M
  /-- `L_M(-1)`. -/
  TM : M →ₗ[k] M
  /-- Lower truncation. -/
  trunc : ∀ (a : V) (w : M), ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → act n a w = 0
  /-- `Y_M(1, z) = id`. -/
  vac_act : ∀ (n : ℤ) (w : M), act n A.vac w = if n = -1 then w else 0
  /-- Translation covariance: `[L_M(-1), a_(n)] = (T a)_(n) = -n a_(n-1)`. -/
  TM_act : ∀ (n : ℤ) (a : V) (w : M), TM (act n a w) - act n a (TM w) = -((n : k) • act (n - 1) a w)
  /-- Module iterate formula `(a_(m) b)_(n) w = ∑_{t ≥ 0} (-1)^t (m choose t)
  (a_(m-t) b_(n+t) w - (-1)^m b_(m+n-t) a_(t) w)`, for any bound `N` beyond which
  `b_(n+t) w` and `a_(t) w` vanish. -/
  iterate : ∀ (a b : V) (w : M) (m n : ℤ) (N : ℕ),
    (∀ t : ℕ, N ≤ t → act (n + t) b w = 0) → (∀ t : ℕ, N ≤ t → act t a w = 0) →
    act n (A.mode m a b) w =
      ∑ t ∈ Finset.range N, ((-1 : k) ^ t * zbinom k m t) •
        (act (m - t) a (act (n + t) b w) - (-1 : k) ^ m • act (m + n - t) b (act t a w))

variable {A : VertexAlgebra k V} (W : WeakModule A M)

/-- **Vacuum-like vectors are annihilated by all nonnegative modes.** -/
theorem mode_vacuumLike_nonneg {v : M} (hv : W.TM v = 0) (a : V) :
    ∀ n : ℤ, 0 ≤ n → W.act n a v = 0 := by
  obtain ⟨N, hN⟩ := W.trunc a v
  -- downward induction: `a_(N - j) v = 0` for all `j ≤ N`
  have step : ∀ n : ℤ, 0 ≤ n → W.act (n + 1) a v = 0 → W.act n a v = 0 := by
    intro n hn h
    have h1 := W.TM_act (n + 1) a v
    rw [h, hv, map_zero, map_zero, sub_zero, add_sub_cancel_right] at h1
    have hne : ((n + 1 : ℤ) : k) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    have h2 : ((n + 1 : ℤ) : k) • W.act n a v = 0 := by
      rw [← neg_eq_zero]; exact h1.symm
    calc W.act n a v = (((n + 1 : ℤ) : k))⁻¹ • (((n + 1 : ℤ) : k) • W.act n a v) := by
          rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = 0 := by rw [h2, smul_zero]
  have key : ∀ j : ℕ, W.act ((N : ℤ) - j) a v = 0 ∨ (N : ℤ) - j < 0 := by
    intro j
    induction j with
    | zero => left; simpa using hN N le_rfl
    | succ j ih =>
      rcases ih with h | h
      · by_cases hneg : (N : ℤ) - (j + 1 : ℕ) < 0
        · right; exact hneg
        · left
          apply step _ (by push_cast at hneg ⊢; omega)
          have : (N : ℤ) - ((j + 1 : ℕ) : ℤ) + 1 = (N : ℤ) - j := by push_cast; ring
          rw [this]; exact h
      · right; push_cast at h ⊢; omega
  intro n hn
  by_cases hle : n ≤ N
  · have := key (N - n).toNat
    have hc : (N : ℤ) - ((N - n).toNat : ℕ) = n := by
      rw [Int.toNat_of_nonneg (by omega)]; ring
    rw [hc] at this
    rcases this with h | h
    · exact h
    · omega
  · exact hN n (by omega)

/-- **The map `a ↦ a_(-1) v` intertwines the modes**: `b_(m) (a_(-1) v) = (b_(m) a)_(-1) v`. -/
theorem vacuumLike_hom {v : M} (hv : W.TM v = 0) (a b : V) (m : ℤ) :
    W.act (-1) (A.mode m b a) v = W.act m b (W.act (-1) a v) := by
  have ha := mode_vacuumLike_nonneg W hv a
  have hb := mode_vacuumLike_nonneg W hv b
  rw [W.iterate b a v m (-1) 1 (fun t ht => ha _ (by omega)) (fun t ht => hb _ (by omega))]
  simp only [Finset.sum_range_one, pow_zero, one_mul, Nat.cast_zero, sub_zero, add_zero]
  rw [hb 0 le_rfl, map_zero, smul_zero, sub_zero]
  simp [zbinom]

/-- `1_(-1) v = v`. -/
theorem vacuumLike_vac (v : M) : W.act (-1) A.vac v = v := by
  simp [W.vac_act]

/-- **Lemma `lem:vacuum-like`**: for a vacuum-like `v`, the linear map `a ↦ a_(-1) v`
sends `1` to `v` and intertwines every mode. -/
theorem vacuumLike_module_map {v : M} (hv : W.TM v = 0) :
    ∃ φ : V →ₗ[k] M, φ A.vac = v ∧ ∀ (m : ℤ) (b a : V), φ (A.mode m b a) = W.act m b (φ a) :=
  ⟨(W.act (-1)).flip v, vacuumLike_vac W v, fun m b a => vacuumLike_hom W hv a b m⟩

/-- **The section in `lem:vacuum-projective`** (lines 2972–2978).  If `π : M → V` is a module map
and `v ∈ M` is vacuum-like with `π v = 𝟏`, then `s(a) = a_(-1) v` is a module map with
`π ∘ s = id`, so `π` splits.  (Finding such a `v ∈ N_[0]` uses `L_V(-1) N_[0] = 0`, from the
trace and vacuum-top steps, and the surjectivity of `π` on generalized weight zero.) -/
theorem vacuumLike_section {v : M} (hv : W.TM v = 0) (π : M →ₗ[k] V)
    (hπ : ∀ (n : ℤ) (a : V) (w : M), π (W.act n a w) = A.mode n a (π w)) (hπv : π v = A.vac) :
    ∃ s : V →ₗ[k] M, (∀ (m : ℤ) (b a : V), s (A.mode m b a) = W.act m b (s a)) ∧
      ∀ a, π (s a) = a :=
  ⟨(W.act (-1)).flip v, fun m b a => vacuumLike_hom W hv a b m, fun a => by
    show π (W.act (-1) a v) = a
    rw [hπ, hπv, A.mode_vac_neg_one]⟩

#print axioms vacuumLike_module_map
#print axioms vacuumLike_section

end HaagerupIzumi.C8.VacuumLike
