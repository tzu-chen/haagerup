module

public import HaagerupIzumi.C8.Theta.WeilSanityST

@[expose] public section

/-!
# `(S T)³ = S²` for the `m = 3` even blocks

Continuation of `Theta/WeilSanityST` for `L₇ ⊕ A₂` and `G₇⁻` (both on `Fin 4 × Fin 2`, with
the same `S`-block, `SθEG7m_eq_SθEL7A2`).  We prove `(SθE · TθE)³ = 1 = SθE²`
(`STcube_L7A2`, `STcube_G7m`):

* Kronecker factorizations `SθE = -(1/√21) C₇ ⊗ C₃`, `TθE = e(-1/3) D₇ ⊗ D₃` with
  `D₇ = diag(ζ₇^{±r²})`, `D₃ = diag(1, e(±1/3))`;
* `(C₇ D₇)³ = 7 G₇` and `(C₇ D̄₇)³ = 7 Ḡ₇` in `ℤ[ζ₇]` (`cube_C7`, `cube_C7bar`), where
  `G₇ = ∑_x ζ₇^{x²} = 1 + 2(ζ + ζ² + ζ⁴)` is the quadratic Gauss sum;
* **the sign of the Gauss sum**: `G₇ = i √7` (`gauss7_eq`): `G₇² = -7` algebraically and
  `Im G₇ = 2(sin(2π/7) + sin(4π/7) - sin(π/7)) > 0`; and `Ḡ₇ = -G₇`;
* with `1 + 2e(1/3) = i√3` this gives the scalar `(-1/√21)³ · 7(i√7) · 3(i√3) = 1`, i.e. the
  cube is `+1` (the wrong sign of either Gauss sum would give `-1`).

Together with `SθE² = 1` and `TθE²¹ = 1` (`Theta/WeilSanity`), the assignment
`S ↦ SθE`, `T ↦ TθE` satisfies the defining relations of `SL(2, ℤ)` on all four even blocks.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex Matrix
open scoped Real Kronecker

namespace HaagerupIzumi.C8
namespace Theta

/-! ## The Gauss sum `G₇` -/

/-- `G₇ = ∑_{x mod 7} ζ₇^{x²} = 1 + 2(ζ + ζ² + ζ⁴)`. -/
def gauss7 : ℂ := 1 + 2 * (z7 + z7 ^ 2 + z7 ^ 4)

/-- `Ḡ₇ = 1 + 2(ζ³ + ζ⁵ + ζ⁶)`. -/
def gauss7bar : ℂ := 1 + 2 * (z7 ^ 3 + z7 ^ 5 + z7 ^ 6)

theorem gauss7_sq : gauss7 ^ 2 = -7 := by
  rw [gauss7]
  ring_nf
  simp only [z7_pow_mod 7, z7_pow_mod 8]
  linear_combination (8 : ℂ) * z7_geom

theorem gauss7bar_eq : gauss7bar = -gauss7 := by
  rw [gauss7bar, gauss7]
  linear_combination (2 : ℂ) * z7_geom

theorem z7_pow_eq (k : ℕ) : z7 ^ k = eChar (k / 7) := by
  rw [z7, eChar_pow]
  congr 1
  ring

theorem im_z7_pow (k : ℕ) : (z7 ^ k).im = Real.sin (2 * π * (k / 7)) := by
  rw [z7_pow_eq, eChar_cos_sin]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]
  ring

theorem gauss7_im_pos : 0 < gauss7.im := by
  have h1 := im_z7_pow 1
  have h2 := im_z7_pow 2
  have h4 := im_z7_pow 4
  have hre : gauss7.im = 2 * ((z7 ^ 1).im + (z7 ^ 2).im + (z7 ^ 4).im) := by
    simp [gauss7, Complex.add_im, Complex.mul_im]
  rw [hre, h1, h2, h4]
  have hpi := Real.pi_pos
  have e8 : Real.sin (2 * π * ((4 : ℕ) / 7)) = -Real.sin (π / 7) := by
    rw [show 2 * π * ((4 : ℕ) / 7 : ℝ) = π / 7 + π by push_cast; ring, Real.sin_add_pi]
  have e2 : Real.sin (2 * π * ((1 : ℕ) / 7)) = Real.sin (2 * π / 7) := by
    congr 1
    push_cast
    ring
  have e4 : Real.sin (2 * π * ((2 : ℕ) / 7)) = Real.sin (4 * π / 7) := by
    congr 1
    push_cast
    ring
  rw [e8, e2, e4]
  have hlt : Real.sin (π / 7) < Real.sin (2 * π / 7) :=
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have hpos : 0 < Real.sin (4 * π / 7) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by linarith)
  linarith

/-- **The sign of the quadratic Gauss sum**: `G₇ = i √7`. -/
theorem gauss7_eq : gauss7 = I * ((Real.sqrt 7 : ℝ) : ℂ) := by
  have hsq := gauss7_sq
  have him := gauss7_im_pos
  have hre2 := congrArg Complex.re hsq
  have him2 := congrArg Complex.im hsq
  simp only [sq, Complex.mul_re, Complex.mul_im] at hre2 him2
  have e1 : (-7 : ℂ).re = -7 := by norm_num
  have e2 : (-7 : ℂ).im = 0 := by norm_num
  rw [e1] at hre2
  rw [e2] at him2
  have hx : gauss7.re = 0 := by
    have h0 : gauss7.re * gauss7.im = 0 := by linarith
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · linarith
  have hy : gauss7.im = Real.sqrt 7 := by
    rw [hx] at hre2
    have hy2 : gauss7.im ^ 2 = 7 := by nlinarith
    rw [← hy2, Real.sqrt_sq him.le]
  apply Complex.ext <;> simp [hx, hy]

/-! ## Cubes in `ℤ[ζ₇]` -/

def C7m : Matrix (Fin 4) (Fin 4) ℂ := Matrix.of fun r r' => C7z r r'

def D7m : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal fun r => z7 ^ (((r : ℕ) ^ 2) % 7)

def D7mbar : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal fun r => z7 ^ ((6 * (r : ℕ) ^ 2) % 7)

theorem cube_C7 : C7m * D7m * (C7m * D7m) * (C7m * D7m) = (7 * gauss7) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, C7m, D7m, C7z, R7, Finset.sum_insert,
      Matrix.diagonal_apply, gauss7] <;> ring_nf <;>
    (try simp only [z7_pow_mod 7, z7_pow_mod 8, z7_pow_mod 9, z7_pow_mod 10, z7_pow_mod 11,
      z7_pow_mod 12, z7_pow_mod 13, z7_pow_mod 14, z7_pow_mod 15, z7_pow_mod 16, z7_pow_mod 17,
      z7_pow_mod 18, z7_pow_mod 19, z7_pow_mod 20, z7_pow_mod 21, z7_pow_mod 22, z7_pow_mod 23,
      z7_pow_mod 24, z7_pow_mod 25, z7_pow_mod 26, z7_pow_mod 27, z7_pow_mod 28, z7_pow_mod 29,
      z7_pow_mod 30, z7_pow_mod 31, z7_pow_mod 32, z7_pow_mod 33, z7_pow_mod 34, z7_pow_mod 35,
      z7_pow_mod 36, z7_pow_mod 37, z7_pow_mod 38, z7_pow_mod 39, z7_pow_mod 40,
      z7_pow_mod 41]) <;>
    first
    | linear_combination (0 : ℂ) * z7_geom
    | linear_combination (7 : ℂ) * z7_geom
    | linear_combination (14 : ℂ) * z7_geom
    | linear_combination (-7 : ℂ) * z7_geom
    | linear_combination (-14 : ℂ) * z7_geom

theorem cube_C7bar :
    C7m * D7mbar * (C7m * D7mbar) * (C7m * D7mbar) = (7 * gauss7bar) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, C7m, D7mbar, C7z, R7, Finset.sum_insert,
      Matrix.diagonal_apply, gauss7bar] <;> ring_nf <;>
    (try simp only [z7_pow_mod 7, z7_pow_mod 8, z7_pow_mod 9, z7_pow_mod 10, z7_pow_mod 11,
      z7_pow_mod 12, z7_pow_mod 13, z7_pow_mod 14, z7_pow_mod 15, z7_pow_mod 16, z7_pow_mod 17,
      z7_pow_mod 18, z7_pow_mod 19, z7_pow_mod 20, z7_pow_mod 21, z7_pow_mod 22, z7_pow_mod 23,
      z7_pow_mod 24, z7_pow_mod 25, z7_pow_mod 26, z7_pow_mod 27, z7_pow_mod 28, z7_pow_mod 29,
      z7_pow_mod 30, z7_pow_mod 31, z7_pow_mod 32, z7_pow_mod 33, z7_pow_mod 34, z7_pow_mod 35,
      z7_pow_mod 36, z7_pow_mod 37, z7_pow_mod 38, z7_pow_mod 39, z7_pow_mod 40,
      z7_pow_mod 41]) <;>
    first
    | linear_combination (0 : ℂ) * z7_geom
    | linear_combination (7 : ℂ) * z7_geom
    | linear_combination (14 : ℂ) * z7_geom
    | linear_combination (-7 : ℂ) * z7_geom
    | linear_combination (-14 : ℂ) * z7_geom

/-! ## Kronecker factorizations -/

theorem SθEL7A2_kron :
    SθEL7A2 = (-(((Real.sqrt 21)⁻¹ : ℝ) : ℂ)) • (C7m ⊗ₖ C3c) := by
  ext ⟨r, s⟩ ⟨r', s'⟩
  rw [SθEL7A2_eq, Matrix.smul_apply, Matrix.kronecker_apply, c3_eq_int, c7_eq_z, smul_eq_mul]
  simp only [C7m, C3c, Matrix.of_apply]
  push_cast
  ring

theorem z7_pow_sq_mod (n : ℕ) : z7 ^ (n % 7) = eChar ((n : ℝ) / 7) := by
  rw [← z7_pow_mod, z7_pow_eq]

theorem vec3_third (s : Fin 2) :
    (![1, eChar (1 / 3)] : Fin 2 → ℂ) s = eChar (((s : ℕ) : ℝ) ^ 2 / 3) := by
  fin_cases s <;> simp [eChar_zero]

theorem vec3_two_thirds (s : Fin 2) :
    (![1, eChar (2 / 3)] : Fin 2 → ℂ) s = eChar (2 * ((s : ℕ) : ℝ) ^ 2 / 3) := by
  fin_cases s <;> simp [eChar_zero]

theorem TθEL7A2_kron :
    TθEL7A2 = eChar (-(1 / 3)) • (D7m ⊗ₖ Matrix.diagonal ![1, eChar (1 / 3)]) := by
  rw [D7m, Matrix.diagonal_kronecker_diagonal]
  ext e e'
  rw [TθEL7A2, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rcases e with ⟨r, s⟩
    dsimp only
    have h1 : (((ιL7A2 (r, s)).1 : Fin 7) : ℕ) = (r : ℕ) := rfl
    have h2 : (((ιL7A2 (r, s)).2 : Fin 3) : ℕ) = (s : ℕ) := rfl
    rw [smul_eq_mul, vec3_third, z7_pow_sq_mod, eL7A2, h1, h2, ← eChar_add, ← eChar_add]
    congr 1
    push_cast
    ring
  · simp

theorem TθEG7m_kron :
    TθEG7m = eChar (-(1 / 3)) • (D7mbar ⊗ₖ Matrix.diagonal ![1, eChar (2 / 3)]) := by
  rw [D7mbar, Matrix.diagonal_kronecker_diagonal]
  ext e e'
  by_cases h : e = e'
  · subst h
    rcases e with ⟨r, s⟩
    rw [TθEG7m_eq, Matrix.smul_apply, Matrix.diagonal_apply_eq]
    dsimp only
    rw [smul_eq_mul, vec3_two_thirds, z7_pow_sq_mod, ← eChar_add, ← eChar_add]
    congr 1
    push_cast
    ring
  · rw [TθEG7m, Matrix.smul_apply, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h,
      smul_zero]

/-! ## The scalar and `(ST)³ = 1` -/

theorem sqrt21_eq : ((Real.sqrt 21 : ℝ) : ℂ) = ((Real.sqrt 7 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ) := by
  rw [show (21 : ℝ) = 7 * 3 by norm_num, Real.sqrt_mul (by norm_num)]
  push_cast
  ring

theorem sqrt7_sq : ((Real.sqrt 7 : ℝ) : ℂ) ^ 2 = 7 := by
  have h : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h' := congrArg (fun x : ℝ => (x : ℂ)) h
  push_cast at h'
  exact h'

theorem scalar_cube7 {g w : ℂ}
    (hgw : g * (1 + 2 * w) = -(((Real.sqrt 7 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ))) :
    ((-(((Real.sqrt 21)⁻¹ : ℝ) : ℂ)) * eChar (-(1 / 3))) *
        ((-(((Real.sqrt 21)⁻¹ : ℝ) : ℂ)) * eChar (-(1 / 3))) *
        ((-(((Real.sqrt 21)⁻¹ : ℝ) : ℂ)) * eChar (-(1 / 3))) * ((7 * g) * (3 + 6 * w)) = 1 := by
  have hu := eChar_neg_third_cube
  have h7 := sqrt7_sq
  have h3 := sqrt3_sq
  have h70 : ((Real.sqrt 7 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  have h30 : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    positivity
  have h21 : (((Real.sqrt 21)⁻¹ : ℝ) : ℂ) =
      (((Real.sqrt 7 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ))⁻¹ := by
    push_cast
    rw [sqrt21_eq]
  rw [h21]
  have key : (7 * g) * (3 + 6 * w) =
      -21 * (((Real.sqrt 7 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ)) := by
    linear_combination 21 * hgw
  rw [key]
  have e1 : (-(((Real.sqrt 7 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ))⁻¹ * eChar (-(1 / 3))) *
      (-(((Real.sqrt 7 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ))⁻¹ * eChar (-(1 / 3))) *
      (-(((Real.sqrt 7 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ))⁻¹ * eChar (-(1 / 3))) =
        -(((Real.sqrt 7 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ))⁻¹ ^ 3 * eChar (-(1 / 3)) ^ 3 := by
    ring
  rw [e1, hu]
  field_simp
  linear_combination (-((Real.sqrt 3 : ℝ) : ℂ) ^ 2) * h7 + (-7 : ℂ) * h3

/-- **`(SθE TθE)³ = 1` for `L₇ ⊕ A₂`.** -/
theorem STcube_L7A2 :
    SθEL7A2 * TθEL7A2 * (SθEL7A2 * TθEL7A2) * (SθEL7A2 * TθEL7A2) = 1 := by
  obtain ⟨hw2, hw3⟩ := eChar_third_rels
  rw [SθEL7A2_kron, TθEL7A2_kron, kron_cube, cube_C7, cube_C3 _ hw2 hw3,
    Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul, smul_smul]
  have hgw : gauss7 * (1 + 2 * eChar (1 / 3)) =
      -(((Real.sqrt 7 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ)) := by
    rw [gauss7_eq, eChar_third]
    ring_nf
    rw [I_sq]
    ring
  have hs := scalar_cube7 hgw
  refine (congrArg (· • (1 : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ)) ?_).trans (one_smul ℂ _)
  linear_combination hs

/-- **`(SθE TθE)³ = 1` for `G₇⁻`.** -/
theorem STcube_G7m :
    SθEG7m * TθEG7m * (SθEG7m * TθEG7m) * (SθEG7m * TθEG7m) = 1 := by
  obtain ⟨hw2, hw3⟩ := eChar_two_thirds_rels
  rw [SθEG7m_eq_SθEL7A2, SθEL7A2_kron, TθEG7m_kron, kron_cube, cube_C7bar, cube_C3 _ hw2 hw3,
    Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul, smul_smul]
  have hgbar : gauss7bar = -(I * ((Real.sqrt 7 : ℝ) : ℂ)) := by rw [gauss7bar_eq, gauss7_eq]
  have hgw : gauss7bar * (1 + 2 * eChar (2 / 3)) =
      -(((Real.sqrt 7 : ℝ) : ℂ) * ((Real.sqrt 3 : ℝ) : ℂ)) := by
    rw [hgbar, eChar_two_thirds]
    ring_nf
    rw [I_sq]
    ring
  have hs := scalar_cube7 hgw
  refine (congrArg (· • (1 : Matrix (Fin 4 × Fin 2) (Fin 4 × Fin 2) ℂ)) ?_).trans (one_smul ℂ _)
  linear_combination hs

/-! ## The manuscript's `m = 6` projection (`lem:m6-projection`, eq. `eq:m6-projection`) -/

/-- `S_v = -½ [[1, 2, 1], [1, 0, -1], [1, -2, 1]]` (manuscript line 3557). -/
def Sv : Matrix (Fin 3) (Fin 3) ℂ := (-(1 / 2) : ℂ) • C22c

/-- `T_v = diag(1, -i, -1)` (manuscript line 3557). -/
def Tv : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![1, -I, -1]

/-- **The `m = 6` even `S`-block is `S_v ⊗ (1/√3) C₃`**, the manuscript's projection tensored
with the even `A₂` (pointed) factor; the same matrix serves `A₁ ⊕ A₁ ⊕ A₂` and `G₆⁻`
(`SθE6G6m_eq_SθEA1A1A2`). -/
theorem SθEA1A1A2_eq_Sv :
    SθEA1A1A2 = Sv ⊗ₖ ((((Real.sqrt 3 : ℝ) : ℂ))⁻¹ • C3c) := by
  rw [SθEA1A1A2_kron, Sv, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
  congr 1
  push_cast
  rw [sqrt12_eq, mul_inv]
  ring

/-- **The `G₆⁻` even `T`-block is `e(-1/3) · T_v ⊗ diag(1, e(2/3))`**; for `A₁ ⊕ A₁ ⊕ A₂` it is
the conjugate `T̄_v = diag(1, i, -1)` (`TθEA1A1A2_kron`), as the manuscript allows ("or the
conjugate matrices"). -/
theorem TθE6G6m_eq_Tv :
    TθE6G6m = eChar (-(1 / 3)) • (Tv ⊗ₖ Matrix.diagonal ![1, eChar (2 / 3)]) :=
  TθE6G6m_kron

/-! ## The `SL(2, ℤ)` relations on the four even blocks -/

/-- `S² = 1`, `(ST)³ = 1 = S²`, `T²¹ = 1` for `L₇ ⊕ A₂` (Table 1 block). -/
theorem sl2_relations_L7A2 : SθEL7A2 * SθEL7A2 = 1 ∧
    SθEL7A2 * TθEL7A2 * (SθEL7A2 * TθEL7A2) * (SθEL7A2 * TθEL7A2) = 1 ∧ TθEL7A2 ^ 21 = 1 :=
  ⟨SθEL7A2_sq, STcube_L7A2, TθEL7A2_pow⟩

/-- `S² = 1`, `(ST)³ = 1 = S²`, `T²¹ = 1` for `G₇⁻` (Table 2 block). -/
theorem sl2_relations_G7m : SθEG7m * SθEG7m = 1 ∧
    SθEG7m * TθEG7m * (SθEG7m * TθEG7m) * (SθEG7m * TθEG7m) = 1 ∧ TθEG7m ^ 21 = 1 :=
  ⟨SθEG7m_sq, STcube_G7m, TθEG7m_pow⟩

/-- `S² = 1`, `(ST)³ = 1 = S²`, `T¹² = 1` for `A₁ ⊕ A₁ ⊕ A₂` (Table 3 block). -/
theorem sl2_relations_A1A1A2 : SθEA1A1A2 * SθEA1A1A2 = 1 ∧
    SθEA1A1A2 * TθEA1A1A2 * (SθEA1A1A2 * TθEA1A1A2) * (SθEA1A1A2 * TθEA1A1A2) = 1 ∧
    TθEA1A1A2 ^ 12 = 1 :=
  ⟨SθEA1A1A2_sq, STcube_A1A1A2, TθEA1A1A2_pow⟩

/-- `S² = 1`, `(ST)³ = 1 = S²`, `T¹² = 1` for the swap-symmetric `G₆⁻` block (Table 4). -/
theorem sl2_relations_G6m : SθE6G6m * SθE6G6m = 1 ∧
    SθE6G6m * TθE6G6m * (SθE6G6m * TθE6G6m) * (SθE6G6m * TθE6G6m) = 1 ∧ TθE6G6m ^ 12 = 1 :=
  ⟨SθE6G6m_sq, STcube_G6m, TθE6G6m_pow⟩

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.gauss7_eq
#print axioms HaagerupIzumi.C8.Theta.cube_C7
#print axioms HaagerupIzumi.C8.Theta.STcube_L7A2
#print axioms HaagerupIzumi.C8.Theta.STcube_G7m
#print axioms HaagerupIzumi.C8.Theta.sl2_relations_L7A2
#print axioms HaagerupIzumi.C8.Theta.sl2_relations_G7m
#print axioms HaagerupIzumi.C8.Theta.sl2_relations_A1A1A2
#print axioms HaagerupIzumi.C8.Theta.sl2_relations_G6m
#print axioms HaagerupIzumi.C8.Theta.SθEA1A1A2_eq_Sv
