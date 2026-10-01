module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Twist steps of the near-group exclusion

Appendix G of `c8_expanded_20260929/haagerup_c8_expanded.tex`.

* `m6_projection_twists` — Lemma `lem:m6-projection` (lines 3550–3597),
  root-of-unity step.  Finitely many unit complex numbers `z_j` with positive
  weights `w_j` (in the application `w_j = n_j²`), `∑ w_j = 6`,
  `∑ w_j z_j = -2 - 4i`, `∑ w_j z_j² = -2 + 4i(1-ε)`, `ε = ±1`, force `ε = 1`
  and `z_j ∈ {-1, -i}` for every `j`.  The two moment identities are the Gauss
  sum and the second Frobenius–Schur indicator in the modular centralizer
  (external categorical input, supplied as hypotheses `h1`, `h2`).
* `m3_twists` — Proposition `prop:m3-modular` (lines 3451–3514), twist step.
  Three unit complex numbers with `∑ z = α = (-1 - i√7)/2` and
  `∑ z² = -1/2 - i(ε - 1/2)√7` force `ε = 1` and the elementary symmetric
  functions `e₂ = ᾱ`, `e₃ = 1`; hence they are the roots of
  `t³ - α t² + ᾱ t - 1` (`m3_twist_cubic`).  The two moment identities come from
  Lemma `lem:near-group-induction` (external input).
-/

namespace HaagerupIzumi.C8.Fusion

open Complex

theorem re_sq_add_im_sq_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z.re ^ 2 + z.im ^ 2 = 1 := by
  have h := Complex.sq_norm z
  rw [hz, Complex.normSq_apply] at h
  linear_combination -h

/-- On the unit circle `Im(z²) = 2 Re z Im z ≤ 1`. -/
theorem re_mul_im_add_le_one {z : ℂ} (hz : ‖z‖ = 1) : z.re * z.im + z.im * z.re ≤ 1 := by
  have := re_sq_add_im_sq_of_norm_eq_one hz
  nlinarith [sq_nonneg (z.re - z.im)]

/-- Lemma `lem:m6-projection`, root-of-unity step (lines 3567–3575). -/
theorem m6_projection_twists {J : Type*} [Fintype J] (w : J → ℝ) (z : J → ℂ) (ε : ℝ)
    (hw : ∀ j, 0 < w j) (hz : ∀ j, ‖z j‖ = 1) (hε : ε = 1 ∨ ε = -1)
    (h0 : ∑ j, w j = 6)
    (h1 : ∑ j, (w j : ℂ) * z j = -2 - 4 * I)
    (h2 : ∑ j, (w j : ℂ) * z j ^ 2 = -2 + 4 * I * (1 - ε)) :
    ε = 1 ∧ ∀ j, z j = -1 ∨ z j = -I := by
  have hxy : ∀ j, (z j).re ^ 2 + (z j).im ^ 2 = 1 := fun j =>
    re_sq_add_im_sq_of_norm_eq_one (hz j)
  have hre : ∀ j, ((w j : ℂ) * z j).re = w j * (z j).re := fun j => by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have him : ∀ j, ((w j : ℂ) * z j).im = w j * (z j).im := fun j => by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have him2 : ∀ j, ((w j : ℂ) * z j ^ 2).im = w j * (2 * (z j).re * (z j).im) := fun j => by
    rw [pow_two, Complex.mul_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have s1 : ∑ j, w j * (z j).re = -2 := by
    have := congrArg Complex.re h1
    rw [Complex.re_sum] at this
    simp only [hre] at this
    rw [this]
    simp
  have s2 : ∑ j, w j * (z j).im = -4 := by
    have := congrArg Complex.im h1
    rw [Complex.im_sum] at this
    simp only [him] at this
    rw [this]
    simp
  have s3 : ∑ j, w j * (2 * (z j).re * (z j).im) = 4 * (1 - ε) := by
    have := congrArg Complex.im h2
    rw [Complex.im_sum] at this
    simp only [him2] at this
    rw [this]
    simp
  have hb : ∀ j, w j * (2 * (z j).re * (z j).im) ≤ w j := fun j => by
    have h' : 2 * (z j).re * (z j).im ≤ 1 := by
      nlinarith [sq_nonneg ((z j).re - (z j).im), hxy j]
    have := mul_le_mul_of_nonneg_left h' (hw j).le
    linarith
  have hsum_le : ∑ j, w j * (2 * (z j).re * (z j).im) ≤ ∑ j, w j :=
    Finset.sum_le_sum (fun j _ => hb j)
  have hε1 : ε = 1 := by
    rcases hε with h | h
    · exact h
    · exfalso
      rw [s3, h0, h] at hsum_le
      norm_num at hsum_le
  refine ⟨hε1, fun j => ?_⟩
  rw [hε1] at s3
  have hsq : ∑ j, w j * (1 + (z j).re + (z j).im) ^ 2 = 0 := by
    have e : ∀ j, w j * (1 + (z j).re + (z j).im) ^ 2 =
        2 * w j + 2 * (w j * (z j).re) + 2 * (w j * (z j).im) +
          w j * (2 * (z j).re * (z j).im) := fun j => by
      linear_combination (w j) * hxy j
    rw [Finset.sum_congr rfl (fun j _ => e j)]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    linarith [h0, s1, s2, s3]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (hw j).le (sq_nonneg (1 + (z j).re + (z j).im)))).mp hsq j
    (Finset.mem_univ j)
  have hsq0 : (1 + (z j).re + (z j).im) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (hw j).ne'
  have hl : 1 + (z j).re + (z j).im = 0 := pow_eq_zero_iff two_ne_zero |>.mp hsq0
  have hx : (z j).re * ((z j).re + 1) = 0 := by
    linear_combination (1 / 2 : ℝ) * hxy j - (1 / 2 : ℝ) * ((z j).im - 1 - (z j).re) * hl
  rcases mul_eq_zero.mp hx with h | h
  · right
    apply Complex.ext
    · simp [h]
    · simp only [Complex.neg_im, Complex.I_im]
      linarith
  · left
    apply Complex.ext
    · simp only [Complex.neg_re, Complex.one_re]
      linarith
    · simp only [Complex.neg_im, Complex.one_im]
      linarith

theorem sqrt7_sq : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)

theorem two_lt_sqrt7 : (2 : ℝ) < Real.sqrt 7 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)

/-- `ᾱ` for `α = (-1 - i√7)/2`. -/
theorem conj_alpha7 :
    (starRingEnd ℂ) ((-1 - (Real.sqrt 7 : ℂ) * I) / 2) = (-1 + (Real.sqrt 7 : ℂ) * I) / 2 := by
  simp only [map_div₀, map_sub, map_neg, map_one, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  ring

/-- Proposition `prop:m3-modular`, twist step (lines 3469–3480). -/
theorem m3_twists (z₁ z₂ z₃ : ℂ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (h1 : ‖z₁‖ = 1) (h2 : ‖z₂‖ = 1) (h3 : ‖z₃‖ = 1)
    (hsum : z₁ + z₂ + z₃ = (-1 - (Real.sqrt 7 : ℂ) * I) / 2)
    (hsq : z₁ ^ 2 + z₂ ^ 2 + z₃ ^ 2 = -1 / 2 - I * ((ε : ℂ) - 1 / 2) * (Real.sqrt 7 : ℂ)) :
    ε = 1 ∧ z₁ * z₂ + z₁ * z₃ + z₂ * z₃ = (-1 + (Real.sqrt 7 : ℂ) * I) / 2 ∧
      z₁ * z₂ * z₃ = 1 := by
  have him : (z₁ ^ 2 + z₂ ^ 2 + z₃ ^ 2).im = (z₁.re * z₁.im + z₁.im * z₁.re) +
      (z₂.re * z₂.im + z₂.im * z₂.re) + (z₃.re * z₃.im + z₃.im * z₃.re) := by
    simp only [Complex.add_im, pow_two, Complex.mul_im]
  have hε1 : ε = 1 := by
    rcases hε with hε | hε
    · exact hε
    · exfalso
      have himeq := congrArg Complex.im hsq
      rw [him, hε] at himeq
      simp at himeq
      linarith [re_mul_im_add_le_one h1, re_mul_im_add_le_one h2, re_mul_im_add_le_one h3,
        two_lt_sqrt7]
  refine ⟨hε1, ?_⟩
  rw [hε1] at hsq
  push_cast at hsq
  have hI : I ^ 2 = -1 := Complex.I_sq
  have hs7c : ((Real.sqrt 7 : ℝ) : ℂ) ^ 2 = 7 := by exact_mod_cast sqrt7_sq
  have he2 : z₁ * z₂ + z₁ * z₃ + z₂ * z₃ = (-1 + (Real.sqrt 7 : ℂ) * I) / 2 := by
    linear_combination (1 / 2 : ℂ) * (z₁ + z₂ + z₃ + (-1 - (Real.sqrt 7 : ℂ) * I) / 2) * hsum -
      (1 / 2 : ℂ) * hsq + ((Real.sqrt 7 : ℂ) ^ 2 / 8) * hI - (1 / 8 : ℂ) * hs7c
  refine ⟨he2, ?_⟩
  have hc : ∀ z : ℂ, ‖z‖ = 1 → z * (starRingEnd ℂ) z = 1 := fun z hz => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hconj : (starRingEnd ℂ) z₁ + (starRingEnd ℂ) z₂ + (starRingEnd ℂ) z₃ =
      (-1 + (Real.sqrt 7 : ℂ) * I) / 2 := by
    have := congrArg (starRingEnd ℂ) hsum
    rw [map_add, map_add, conj_alpha7] at this
    exact this
  have he3 : z₁ * z₂ * z₃ * ((-1 + (Real.sqrt 7 : ℂ) * I) / 2) =
      1 * ((-1 + (Real.sqrt 7 : ℂ) * I) / 2) := by
    linear_combination (-(z₁ * z₂ * z₃)) * hconj + (z₂ * z₃) * hc z₁ h1 +
      (z₁ * z₃) * hc z₂ h2 + (z₁ * z₂) * hc z₃ h3 + he2
  have hγ : ((-1 + (Real.sqrt 7 : ℂ) * I) / 2 : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  exact mul_right_cancel₀ hγ he3

/-- The twists are the roots of `t³ - α t² + ᾱ t - 1`. -/
theorem m3_twist_cubic (z₁ z₂ z₃ α β : ℂ) (h1 : z₁ + z₂ + z₃ = α)
    (h2 : z₁ * z₂ + z₁ * z₃ + z₂ * z₃ = β) (h3 : z₁ * z₂ * z₃ = 1) (t : ℂ) :
    (t - z₁) * (t - z₂) * (t - z₃) = t ^ 3 - α * t ^ 2 + β * t - 1 := by
  linear_combination (-t ^ 2) * h1 + t * h2 - h3

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.m6_projection_twists
#print axioms HaagerupIzumi.C8.Fusion.m3_twists
#print axioms HaagerupIzumi.C8.Fusion.m3_twist_cubic
