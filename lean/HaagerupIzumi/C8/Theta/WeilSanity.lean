module

public import HaagerupIzumi.C8.Theta.M6ReverseSym
public import HaagerupIzumi.C8.Theta.EvenBlockDataG7m

@[expose] public section

/-!
# Consistency checks for the even-block `S`- and `T`-matrices

Audit item (non-vacuity) for W6 (`Theta/W6_PLAN.md`).  The capstones `m*_hcancel_of_voa` and
the obstruction theorems `m*_obstruction_of_voa` assume a homomorphism
`σ : SL(2, ℤ) → GL(E, ℂ)` with `σ(S) = SθE*`, `σ(T) = TθE*`.  Such a `σ` can only exist if the
explicit matrices satisfy the relations of `SL(2, ℤ)` (`S⁴ = 1`, `(ST)³ = S²`, `S²` central).
Proved here:

* `TθE*^N = 1` for every block (`N = 21` for `L₇ ⊕ A₂`, `G₇⁻`; `N = 12` for `A₁ ⊕ A₁ ⊕ A₂` and
  the swap-symmetric `G₆⁻` block), so `σ(T)` has finite order;
* `SθE * SθE = 1` for every block (`SθEL7A2_sq`, `SθEG7m_sq`, `SθEA1A1A2_sq`, `SθE6G6m_sq`):
  for `m = 6` from the integer matrix `C₂₂ ⊗ C₃` (`K6 * K6 = 12`, kernel-checked); for `m = 3`
  from `C₇² = 7` and `C₃² = 3`, where `C₇²` is computed in `ℤ[ζ₇]`, `ζ₇ = e(1/7)`, using
  `ζ₇⁷ = 1` and `1 + ζ₇ + … + ζ₇⁶ = 0`.

So `σ(S)² = 1` is consistent with `S² = -1` acting trivially on weight-zero functions.  The
relation `(SθE TθE)³ = SθE²` is **not** proved here (it needs the quadratic Gauss sums
`∑ e(q(γ))` of the discriminant forms with their signs); it is listed in `W6_PLAN.md` as the
remaining consistency check.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex Matrix
open scoped Real

namespace HaagerupIzumi.C8
namespace Theta

/-! ## `T` has finite order -/

theorem eChar_pow (x : ℝ) (n : ℕ) : eChar x ^ n = eChar (n * x) := by
  rw [eChar, eChar, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem eChar_pow_eq_one {x : ℝ} {y : ℚ} (hxy : x = y) (N : ℕ) (h : ((N : ℚ) * y).den = 1) :
    eChar x ^ N = 1 := by
  rw [eChar_pow, hxy]
  have h2 : ((((N : ℚ) * y).num : ℤ) : ℚ) = (N : ℚ) * y := Rat.coe_int_num_of_den_eq_one h
  have h3 : (N : ℝ) * (y : ℝ) = ((((N : ℚ) * y).num : ℤ) : ℝ) := by
    have := congrArg (Rat.cast : ℚ → ℝ) h2
    push_cast at this
    linarith
  rw [h3, eChar_intCast]

theorem diagonal_eChar_pow_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ)
    (y : ι → ℚ) (hxy : ∀ i, x i = y i) (N : ℕ) (h : ∀ i, ((N : ℚ) * y i).den = 1) :
    (Matrix.diagonal fun i => eChar (x i)) ^ N = 1 := by
  rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [Pi.pow_apply]
  exact eChar_pow_eq_one (hxy i) N (h i)

theorem TθEL7A2_pow : TθEL7A2 ^ 21 = 1 :=
  diagonal_eChar_pow_eq_one _ (fun e => eQL7A2 (ιL7A2 e) - 1 / 3) (fun e => eL7A2_sub _) 21
    (by decide +kernel)

theorem TθEG7m_pow : TθEG7m ^ 21 = 1 :=
  diagonal_eChar_pow_eq_one _ (fun e => eQG7m (ιG7m e) - 1 / 3) (fun e => eG7m_sub _) 21
    (by decide +kernel)

theorem TθEA1A1A2_pow : TθEA1A1A2 ^ 12 = 1 :=
  diagonal_eChar_pow_eq_one _ (fun e => eQA1A1A2 (ιA1A1A2 e) - 1 / 3) (fun e => eA1A1A2_sub _)
    12 (by decide +kernel)

theorem TθE6G6m_pow : TθE6G6m ^ 12 = 1 :=
  diagonal_eChar_pow_eq_one _ (fun e => eQG6m (ιA1A1A2 e) - 1 / 3) (fun e => eG6m_sub _) 12
    (by decide +kernel)

/-! ## `C₃` as an integer matrix -/

def c3int : Fin 2 → Fin 2 → ℤ := ![![1, 2], ![1, -1]]

theorem cos_four_pi_div_three : Real.cos (4 * π / 3) = -1 / 2 := by
  rw [show 4 * π / 3 = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]
  norm_num

theorem c3_eq_int (s s' : Fin 2) : c3 s s' = ((c3int s s' : ℤ) : ℝ) := by
  fin_cases s <;> fin_cases s' <;> simp [c3, c3int, cos_four_pi_div_three] <;> norm_num

theorem c3int_sq : ∀ s s'' : Fin 2,
    ∑ s' : Fin 2, c3int s s' * c3int s' s'' = if s = s'' then 3 else 0 := by
  decide +kernel

theorem c3_sq (s s'' : Fin 2) :
    ∑ s' : Fin 2, ((c3 s s' : ℝ) : ℂ) * ((c3 s' s'' : ℝ) : ℂ) = if s = s'' then 3 else 0 := by
  have h := congrArg (Int.cast : ℤ → ℂ) (c3int_sq s s'')
  push_cast at h
  rw [← h]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [c3_eq_int, c3_eq_int]
  push_cast
  ring

theorem sqrt_inv_sq {n : ℝ} (hn : 0 < n) :
    ((Real.sqrt n : ℂ))⁻¹ * ((Real.sqrt n : ℂ))⁻¹ * (n : ℂ) = 1 := by
  have h : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ * n = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hn.le, inv_mul_cancel₀ hn.ne']
  have h' := congrArg (fun x : ℝ => (x : ℂ)) h
  push_cast at h'
  exact h'

/-! ## `S² = 1`, `m = 6` blocks -/

/-- The integer matrix `C₂₂ ⊗ C₃` on `Fin 3 × Fin 2`. -/
def K6 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℤ := fun e e' => c22 e.1 e'.1 * c3int e.2 e'.2

theorem K6_sq : K6 * K6 = Matrix.diagonal fun _ => 12 := by
  decide +kernel

theorem SθEA1A1A2_eq_K6 :
    SθEA1A1A2 = (-(((Real.sqrt 12)⁻¹ : ℝ) : ℂ)) • K6.map (Int.castRingHom ℂ) := by
  ext e e'
  rw [SθEA1A1A2_eq, Matrix.smul_apply, Matrix.map_apply, c3_eq_int, smul_eq_mul, eq_intCast]
  simp only [K6]
  push_cast
  ring

/-- **`SθE² = 1` for `A₁ ⊕ A₁ ⊕ A₂`.** -/
theorem SθEA1A1A2_sq : SθEA1A1A2 * SθEA1A1A2 = 1 := by
  rw [SθEA1A1A2_eq_K6, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.map_mul, K6_sq,
    Matrix.diagonal_map (map_zero _)]
  ext i j
  rw [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [eq_intCast]
    have hs := sqrt_inv_sq (n := 12) (by norm_num)
    push_cast at hs ⊢
    linear_combination hs
  · simp

/-- **`SθE² = 1` for the swap-symmetric `G₆⁻` block.** -/
theorem SθE6G6m_sq : SθE6G6m * SθE6G6m = 1 := by
  rw [SθE6G6m_eq_SθEA1A1A2, SθEA1A1A2_sq]

/-! ## `S² = 1`, `m = 3` blocks: `C₇² = 7` in `ℤ[ζ₇]` -/

/-- `ζ₇ = e(1/7)`. -/
def z7 : ℂ := eChar (1 / 7)

theorem z7_pow_seven : z7 ^ 7 = 1 := by
  rw [z7, eChar_pow, show ((7 : ℕ) : ℝ) * (1 / 7) = ((1 : ℤ) : ℝ) by norm_num, eChar_intCast]

theorem z7_geom : 1 + z7 + z7 ^ 2 + z7 ^ 3 + z7 ^ 4 + z7 ^ 5 + z7 ^ 6 = 0 := by
  have hne : z7 ≠ 1 := eChar_ne_one_of_den (y := 1 / 7) (by norm_num) (by decide +kernel)
  have h : (z7 - 1) * (1 + z7 + z7 ^ 2 + z7 ^ 3 + z7 ^ 4 + z7 ^ 5 + z7 ^ 6) = 0 := by
    linear_combination z7_pow_seven
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h

theorem z7_pow_mod (n : ℕ) : z7 ^ n = z7 ^ (n % 7) := by
  conv_lhs => rw [← Nat.div_add_mod n 7, pow_add, pow_mul, z7_pow_seven, one_pow, one_mul]

theorem z7_pow_high : z7 ^ 7 = 1 ∧ z7 ^ 8 = z7 ∧ z7 ^ 9 = z7 ^ 2 ∧ z7 ^ 10 = z7 ^ 3 ∧
    z7 ^ 11 = z7 ^ 4 ∧ z7 ^ 12 = z7 ^ 5 := by
  refine ⟨z7_pow_seven, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [z7_pow_mod] <;> norm_num

/-- `C₇(r, r') = ∑_{x ∈ ±r'} ζ₇^{5rx}`. -/
def C7z (r r' : Fin 4) : ℂ := ∑ x ∈ R7 r', z7 ^ ((5 * (r : ℕ) * (x : ℕ)) % 7)

theorem c7_eq_z (r r' : Fin 4) : ((c7 r r' : ℝ) : ℂ) = C7z r r' := by
  rw [← sum_R7 r r']
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← z7_pow_mod, z7, eChar_pow]
  refine eChar_eq_of_sub_eq_int (-(((r : ℕ) : ℤ) * ((x : ℕ) : ℤ))) ?_
  push_cast
  ring

/-- **`C₇² = 7`** (computed in `ℤ[ζ₇]`). -/
theorem C7z_sq (r r'' : Fin 4) :
    ∑ r' : Fin 4, C7z r r' * C7z r' r'' = if r = r'' then 7 else 0 := by
  obtain ⟨h7, h8, h9, h10, h11, h12⟩ := z7_pow_high
  fin_cases r <;> fin_cases r'' <;>
    simp [C7z, R7, Fin.sum_univ_four, Finset.sum_insert, Finset.sum_singleton] <;> ring_nf <;>
    (try simp only [h7, h8, h9, h10, h11, h12]) <;>
    first
    | linear_combination (0 : ℂ) * z7_geom
    | linear_combination (1 : ℂ) * z7_geom
    | linear_combination (2 : ℂ) * z7_geom

theorem c7_sq (r r'' : Fin 4) :
    ∑ r' : Fin 4, ((c7 r r' : ℝ) : ℂ) * ((c7 r' r'' : ℝ) : ℂ) = if r = r'' then 7 else 0 := by
  simp only [c7_eq_z]
  exact C7z_sq r r''

/-- **`SθE² = 1` for `L₇ ⊕ A₂`.** -/
theorem SθEL7A2_sq : SθEL7A2 * SθEL7A2 = 1 := by
  ext e e''
  rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]
  simp only [SθEL7A2_eq]
  set c : ℂ := -(((Real.sqrt 21)⁻¹ : ℝ) : ℂ) with hc
  have hsplit : ∑ r' : Fin 4, ∑ s' : Fin 2,
      c * (((c7 e.1 r' : ℝ) : ℂ) * ((c3 e.2 s' : ℝ) : ℂ)) *
        (c * (((c7 r' e''.1 : ℝ) : ℂ) * ((c3 s' e''.2 : ℝ) : ℂ))) =
      c * c * ((∑ r' : Fin 4, ((c7 e.1 r' : ℝ) : ℂ) * ((c7 r' e''.1 : ℝ) : ℂ)) *
        (∑ s' : Fin 2, ((c3 e.2 s' : ℝ) : ℂ) * ((c3 s' e''.2 : ℝ) : ℂ))) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  rw [hsplit, c7_sq, c3_sq]
  have hs := sqrt_inv_sq (n := 21) (by norm_num)
  obtain ⟨r, s⟩ := e
  obtain ⟨r'', s''⟩ := e''
  simp only [Prod.mk.injEq]
  by_cases h1 : r = r'' <;> by_cases h2 : s = s'' <;> simp [h1, h2]
  rw [hc]
  push_cast at hs ⊢
  linear_combination hs

/-- **`SθE² = 1` for `G₇⁻`** (`SθEG7m = SθEL7A2`). -/
theorem SθEG7m_sq : SθEG7m * SθEG7m = 1 := by
  rw [SθEG7m_eq_SθEL7A2, SθEL7A2_sq]

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.TθEL7A2_pow
#print axioms HaagerupIzumi.C8.Theta.TθEG7m_pow
#print axioms HaagerupIzumi.C8.Theta.TθEA1A1A2_pow
#print axioms HaagerupIzumi.C8.Theta.TθE6G6m_pow
#print axioms HaagerupIzumi.C8.Theta.SθEA1A1A2_sq
#print axioms HaagerupIzumi.C8.Theta.SθE6G6m_sq
#print axioms HaagerupIzumi.C8.Theta.C7z_sq
#print axioms HaagerupIzumi.C8.Theta.SθEL7A2_sq
#print axioms HaagerupIzumi.C8.Theta.SθEG7m_sq
