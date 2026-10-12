module

public import HaagerupIzumi.C8.Theta.WeilSanity

@[expose] public section

/-!
# `(S T)³ = S²` for the `m = 6` even blocks

Continuation of `Theta/WeilSanity` (non-vacuity of the hypotheses `σ(S) = SθE*`,
`σ(T) = TθE*`).  For the two `m = 6` blocks (`A₁ ⊕ A₁ ⊕ A₂` and the swap-symmetric `G₆⁻`
block, both on `Fin 3 × Fin 2`) we prove `(SθE · TθE)³ = 1 = SθE²`
(`STcube_A1A1A2`, `STcube_G6m`).  The proof factors both matrices as Kronecker products,
`SθE = -(1/√12) C₂₂ ⊗ C₃`, `TθE = e(-1/3) D₂₂ ⊗ D₃`, computes `(C₂₂D₂₂)³ = 8j` and
`(C₃D₃)³ = 3 + 6w` in `ℤ[j]`, `ℤ[w]` (`j² = -1`, `w² + w + 1 = 0`), and evaluates the signs
with the explicit values `e(1/4) = i`, `e(3/4) = -i`, `e(1/3) = -1/2 + (√3/2) i`,
`e(2/3) = -1/2 - (√3/2) i`: the product `j (1 + 2w)` equals `-√3` in both cases, which is
exactly what makes the cube `+1` (a sign slip would give `-1`).

Together with `SθE² = 1` and `TθE¹² = 1` this shows that the assignment `S ↦ SθE`, `T ↦ TθE`
satisfies the defining relations of `SL(2, ℤ) = ⟨S, T | S⁴ = 1, (ST)³ = S²⟩` (with `S²`
central), i.e. a homomorphism `σ` as hypothesized in `m6_first_obstruction_of_voa`,
`m6_reverse_obstruction_of_voa` exists, with finite image.  (The existence of `σ` itself is not
constructed here; Mathlib has no presentation of `SL(2, ℤ)`.)

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex Matrix
open scoped Real Kronecker

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Explicit values -/

theorem eChar_cos_sin (x : ℝ) :
    eChar x = (Real.cos (2 * π * x) : ℂ) + (Real.sin (2 * π * x) : ℂ) * I := by
  rw [eChar, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem eChar_quarter : eChar (1 / 4) = I := by
  rw [eChar_cos_sin, show 2 * π * (1 / 4) = π / 2 by ring, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

theorem eChar_three_quarters : eChar (3 / 4) = -I := by
  rw [eChar_cos_sin, show 2 * π * (3 / 4) = π / 2 + π by ring, Real.cos_add_pi,
    Real.sin_add_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem eChar_third : eChar (1 / 3) = -1 / 2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * I := by
  rw [eChar_cos_sin, show 2 * π * (1 / 3) = π - π / 3 by ring, Real.cos_pi_sub,
    Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

theorem eChar_two_thirds : eChar (2 / 3) = -1 / 2 - ((Real.sqrt 3 : ℝ) : ℂ) / 2 * I := by
  rw [eChar_cos_sin, show 2 * π * (2 / 3) = π / 3 + π by ring, Real.cos_add_pi,
    Real.sin_add_pi, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

theorem eChar_half : eChar (1 / 2) = -1 := by
  rw [eChar_cos_sin, show 2 * π * (1 / 2) = π by ring, Real.cos_pi, Real.sin_pi]
  simp

theorem eChar_five_halves : eChar (5 / 2) = -1 := by
  rw [eChar_eq_of_sub_eq_int 2 (show (5 / 2 : ℝ) = 1 / 2 + ((2 : ℤ) : ℝ) by norm_num),
    eChar_half]

theorem sqrt3_sq : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h' := congrArg (fun x : ℝ => (x : ℂ)) h
  push_cast at h'
  exact h'

theorem sqrt12_eq : ((Real.sqrt 12 : ℝ) : ℂ) = 2 * ((Real.sqrt 3 : ℝ) : ℂ) := by
  have h : Real.sqrt 12 = 2 * Real.sqrt 3 := by
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [h]
  push_cast
  ring

/-! ## Cubes of the small factors -/

def C22c : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun a b => ((c22 a b : ℤ) : ℂ)

def C3c : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun s t => ((c3int s t : ℤ) : ℂ)

theorem cube_C3 (w : ℂ) (hw2 : w ^ 2 = -1 - w) (hw3 : w ^ 3 = 1) :
    C3c * Matrix.diagonal ![1, w] * (C3c * Matrix.diagonal ![1, w]) *
        (C3c * Matrix.diagonal ![1, w]) = (3 + 6 * w) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, C3c, c3int, Matrix.diagonal_apply] <;> ring_nf <;>
    (try simp only [hw2, hw3]) <;> ring_nf

theorem cube_C22 (j : ℂ) :
    C22c * Matrix.diagonal ![1, j, -1] * (C22c * Matrix.diagonal ![1, j, -1]) *
        (C22c * Matrix.diagonal ![1, j, -1]) = (8 * j) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, C22c, c22, Matrix.diagonal_apply] <;> ring_nf

/-! ## The Kronecker factorizations -/

theorem SθEA1A1A2_kron :
    SθEA1A1A2 = (-(((Real.sqrt 12)⁻¹ : ℝ) : ℂ)) • (C22c ⊗ₖ C3c) := by
  ext ⟨a, s⟩ ⟨a', s'⟩
  rw [SθEA1A1A2_eq, Matrix.smul_apply, Matrix.kronecker_apply, c3_eq_int, smul_eq_mul]
  simp only [C22c, C3c, Matrix.of_apply]
  push_cast
  ring

/-- The general step: if `S = c (A ⊗ B)` and `T = u (D ⊗ E)` with `D`, `E` diagonal, then
`(ST)³ = (cu)³ (AD)³ ⊗ (BE)³`. -/
theorem kron_cube {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (c u : ℂ) (A D : Matrix m m ℂ) (B E : Matrix n n ℂ) :
    (c • (A ⊗ₖ B)) * (u • (D ⊗ₖ E)) * ((c • (A ⊗ₖ B)) * (u • (D ⊗ₖ E))) *
        ((c • (A ⊗ₖ B)) * (u • (D ⊗ₖ E))) =
      ((c * u) * (c * u) * (c * u)) • ((A * D * (A * D) * (A * D)) ⊗ₖ (B * E * (B * E) * (B * E))) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_kronecker_mul]
  congr 1
  ring

/-- `T` of `A₁ ⊕ A₁ ⊕ A₂` as `e(-1/3) · diag(1, e(1/4), e(1/2)) ⊗ diag(1, e(1/3))`. -/
theorem TθEA1A1A2_kron :
    TθEA1A1A2 = eChar (-(1 / 3)) • (Matrix.diagonal ![1, I, -1] ⊗ₖ
      Matrix.diagonal ![1, eChar (1 / 3)]) := by
  rw [Matrix.diagonal_kronecker_diagonal]
  ext e e'
  rw [TθEA1A1A2, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rcases e with ⟨ab, s⟩
    rw [smul_eq_mul, ← eChar_quarter, ← eChar_half]
    fin_cases ab <;> fin_cases s <;>
      simp [ιA1A1A2, eA1A1A2, ← eChar_add, eChar_zero] <;> norm_num
  · simp

theorem vecG6_22 (ab : Fin 3) :
    (![1, -I, -1] : Fin 3 → ℂ) ab = eChar ((![0, 3 / 4, 5 / 2] : Fin 3 → ℝ) ab) := by
  fin_cases ab <;> simp [eChar_zero, eChar_three_quarters, eChar_five_halves]

theorem vecG6_3 (s : Fin 2) :
    (![1, eChar (2 / 3)] : Fin 2 → ℂ) s = eChar ((![0, 2 / 3] : Fin 2 → ℝ) s) := by
  fin_cases s <;> simp [eChar_zero]

/-- The exponents of `TθE6G6m` up to integers (explicit shifts). -/
theorem eG6m_sym_shift (ab : Fin 3) (s : Fin 2) : ∃ k : ℤ,
    eG6m (ιA1A1A2 (ab, s)) - 1 / 3 =
      -(1 / 3) + ((![0, 3 / 4, 5 / 2] : Fin 3 → ℝ) ab + (![0, 2 / 3] : Fin 2 → ℝ) s) + k := by
  fin_cases ab <;> fin_cases s
  · exact ⟨0, by norm_num [ιA1A1A2, eG6m]⟩
  · exact ⟨0, by norm_num [ιA1A1A2, eG6m]⟩
  · exact ⟨0, by norm_num [ιA1A1A2, eG6m]⟩
  · exact ⟨-1, by norm_num [ιA1A1A2, eG6m]⟩
  · exact ⟨0, by norm_num [ιA1A1A2, eG6m]⟩
  · exact ⟨-2, by norm_num [ιA1A1A2, eG6m]⟩

/-- `T` of the swap-symmetric `G₆⁻` block as `e(-1/3) · diag(1, e(3/4), e(5/2)) ⊗ diag(1, e(2/3))`
(up to integer shifts of the exponents). -/
theorem TθE6G6m_kron :
    TθE6G6m = eChar (-(1 / 3)) • (Matrix.diagonal ![1, -I, -1] ⊗ₖ
      Matrix.diagonal ![1, eChar (2 / 3)]) := by
  rw [Matrix.diagonal_kronecker_diagonal]
  ext e e'
  rw [TθE6G6m, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rcases e with ⟨ab, s⟩
    obtain ⟨k, hk⟩ := eG6m_sym_shift ab s
    dsimp only
    rw [smul_eq_mul, vecG6_22, vecG6_3, eChar_eq_of_sub_eq_int k hk, eChar_add, eChar_add]
  · simp

/-! ## `(ST)³ = 1` -/

theorem eChar_third_rels : eChar (1 / 3) ^ 2 = -1 - eChar (1 / 3) ∧ eChar (1 / 3) ^ 3 = 1 := by
  rw [eChar_third]
  constructor <;> ring_nf <;> simp only [I_sq, sqrt3_sq] <;> ring_nf <;>
    (try simp only [I_sq, sqrt3_sq, show I ^ 3 = -I by rw [pow_succ, I_sq]; ring,
      show ((Real.sqrt 3 : ℝ) : ℂ) ^ 3 = 3 * ((Real.sqrt 3 : ℝ) : ℂ) by
        rw [pow_succ, sqrt3_sq]]) <;> ring_nf

theorem eChar_two_thirds_rels :
    eChar (2 / 3) ^ 2 = -1 - eChar (2 / 3) ∧ eChar (2 / 3) ^ 3 = 1 := by
  rw [eChar_two_thirds]
  constructor <;> ring_nf <;> simp only [I_sq, sqrt3_sq] <;> ring_nf <;>
    (try simp only [I_sq, sqrt3_sq, show I ^ 3 = -I by rw [pow_succ, I_sq]; ring,
      show ((Real.sqrt 3 : ℝ) : ℂ) ^ 3 = 3 * ((Real.sqrt 3 : ℝ) : ℂ) by
        rw [pow_succ, sqrt3_sq]]) <;> ring_nf

theorem eChar_neg_third_cube : eChar (-(1 / 3)) ^ 3 = 1 := by
  rw [eChar_pow, show ((3 : ℕ) : ℝ) * -(1 / 3) = ((-1 : ℤ) : ℝ) by norm_num, eChar_intCast]

/-- The scalar: `(c u)³ · 8j · (3 + 6w) = 1` when `j (1 + 2w) = -√3`, `c = -1/√12`, `u³ = 1`. -/
theorem scalar_cube {j w : ℂ} (hjw : j * (1 + 2 * w) = -((Real.sqrt 3 : ℝ) : ℂ)) :
    ((-(((Real.sqrt 12)⁻¹ : ℝ) : ℂ)) * eChar (-(1 / 3))) *
        ((-(((Real.sqrt 12)⁻¹ : ℝ) : ℂ)) * eChar (-(1 / 3))) *
        ((-(((Real.sqrt 12)⁻¹ : ℝ) : ℂ)) * eChar (-(1 / 3))) * ((8 * j) * (3 + 6 * w)) = 1 := by
  have hu := eChar_neg_third_cube
  have hr := sqrt3_sq
  have hr0 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  have h12 : (((Real.sqrt 12)⁻¹ : ℝ) : ℂ) = (2 * ((Real.sqrt 3 : ℝ) : ℂ))⁻¹ := by
    push_cast
    rw [sqrt12_eq]
  rw [h12]
  have key : (8 * j) * (3 + 6 * w) = -24 * ((Real.sqrt 3 : ℝ) : ℂ) := by
    linear_combination 24 * hjw
  rw [key]
  have e1 : (-(2 * ((Real.sqrt 3 : ℝ) : ℂ))⁻¹ * eChar (-(1 / 3))) *
      (-(2 * ((Real.sqrt 3 : ℝ) : ℂ))⁻¹ * eChar (-(1 / 3))) *
      (-(2 * ((Real.sqrt 3 : ℝ) : ℂ))⁻¹ * eChar (-(1 / 3))) =
        -((2 * ((Real.sqrt 3 : ℝ) : ℂ))⁻¹) ^ 3 * eChar (-(1 / 3)) ^ 3 := by ring
  rw [e1, hu]
  field_simp
  linear_combination (-8 : ℂ) * hr

/-- **`(SθE TθE)³ = 1` for `A₁ ⊕ A₁ ⊕ A₂`.** -/
theorem STcube_A1A1A2 :
    SθEA1A1A2 * TθEA1A1A2 * (SθEA1A1A2 * TθEA1A1A2) * (SθEA1A1A2 * TθEA1A1A2) = 1 := by
  obtain ⟨hw2, hw3⟩ := eChar_third_rels
  rw [SθEA1A1A2_kron, TθEA1A1A2_kron, kron_cube, cube_C22, cube_C3 _ hw2 hw3,
    Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul, smul_smul]
  have hjw : I * (1 + 2 * eChar (1 / 3)) = -((Real.sqrt 3 : ℝ) : ℂ) := by
    rw [eChar_third]
    ring_nf
    rw [I_sq]
    ring
  have hs := scalar_cube hjw
  refine (congrArg (· • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)) ?_).trans (one_smul ℂ _)
  linear_combination hs

/-- **`(SθE TθE)³ = 1` for the swap-symmetric `G₆⁻` block.** -/
theorem STcube_G6m :
    SθE6G6m * TθE6G6m * (SθE6G6m * TθE6G6m) * (SθE6G6m * TθE6G6m) = 1 := by
  obtain ⟨hw2, hw3⟩ := eChar_two_thirds_rels
  rw [SθE6G6m_eq_SθEA1A1A2, SθEA1A1A2_kron, TθE6G6m_kron, kron_cube, cube_C22,
    cube_C3 _ hw2 hw3, Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one,
    smul_smul, smul_smul]
  have hjw : -I * (1 + 2 * eChar (2 / 3)) = -((Real.sqrt 3 : ℝ) : ℂ) := by
    rw [eChar_two_thirds]
    ring_nf
    rw [I_sq]
    ring
  have hs := scalar_cube hjw
  refine (congrArg (· • (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)) ?_).trans (one_smul ℂ _)
  linear_combination hs

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.STcube_A1A1A2
#print axioms HaagerupIzumi.C8.Theta.STcube_G6m
