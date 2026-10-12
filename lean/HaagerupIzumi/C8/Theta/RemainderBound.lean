module

public import HaagerupIzumi.C8.Theta.PolarParts
public import HaagerupIzumi.C8.Theta.CoeffExtraction

@[expose] public section

/-!
# A `q`-series without polar terms, divided by `η⁸`, is bounded at `i∞`

W6 plan item 3 (`Theta/W6_PLAN.md`), analytic input, for the proof of Proposition
`prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`): after the polar coefficients of
`η⁸ δv - λ Θ_{H₁} - μ Θ_{H₂}` are matched, the remainder divided by `η⁸` has no pole.

* `isBoundedAtImInfty_tsum_div_eta8`: if `∑ c_x q^x` has `c_x = 0` for `x < 1/3` and converges
  absolutely at some height `y₀`, then `(∑ c_x q^x)/η⁸` is bounded at `i∞`.  The proof
  uses `|∑ c_x q^x| ≤ K e^{-2πy/3}` and `|1/η⁸| ≤ (1 + 228/48) e^{2πy/3}` for `Im τ ≥ 1`
  (`norm_inv_eta8_sub_le`, `norm_qParam_one_le_of_one_le_im`).
* `tsum_sub_lincomb`: `∑ a q^x - (l ∑ b q^x + m ∑ b' q^x) = ∑ (a - l b - m b') q^x`.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex
open scoped Real UpperHalfPlane

namespace HaagerupIzumi.C8
namespace Theta

/-- `‖1/η⁸(τ)‖ ≤ (1 + 228/48) e^{2π Im τ/3}` for `Im τ ≥ 1`. -/
theorem norm_inv_eta8_le {τ : ℂ} (hτ : 1 ≤ τ.im) :
    ‖(eta8 τ)⁻¹‖ ≤ (1 + 228 / 48) * Real.exp (2 * π * τ.im / 3) := by
  have hq := norm_qParam_one_le_of_one_le_im hτ
  have h := norm_inv_eta8_sub_le hq
  have hq3 : ‖Function.Periodic.qParam (-3) τ‖ = Real.exp (2 * π * τ.im / 3) := by
    rw [Function.Periodic.norm_qParam]
    congr 1
    ring
  rw [hq3] at h
  have hE := Real.exp_pos (2 * π * τ.im / 3)
  calc ‖(eta8 τ)⁻¹‖ = ‖((eta8 τ)⁻¹ - Function.Periodic.qParam (-3) τ) +
        Function.Periodic.qParam (-3) τ‖ := by rw [sub_add_cancel]
    _ ≤ ‖(eta8 τ)⁻¹ - Function.Periodic.qParam (-3) τ‖ +
        ‖Function.Periodic.qParam (-3) τ‖ := norm_add_le _ _
    _ ≤ 228 * ‖Function.Periodic.qParam 1 τ‖ * Real.exp (2 * π * τ.im / 3) +
        Real.exp (2 * π * τ.im / 3) := by rw [hq3] at *; linarith
    _ ≤ 228 * (1 / 48) * Real.exp (2 * π * τ.im / 3) + Real.exp (2 * π * τ.im / 3) := by
        gcongr
    _ = (1 + 228 / 48) * Real.exp (2 * π * τ.im / 3) := by ring

/-- **The remainder is bounded at `i∞`.**  A `q`-series `∑ c_x q^x` with no exponent below
`1/3`, absolutely convergent at some height `y₀`, divided by `η⁸`. -/
theorem isBoundedAtImInfty_tsum_div_eta8 (c : ℚ → ℂ) (hsupp : ∀ x, c x ≠ 0 → 1 / 3 ≤ x)
    {y₀ : ℝ}
    (hsum : Summable fun x : ℚ => ‖c x‖ * Real.exp (-2 * π * (x : ℝ) * y₀)) :
    UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : ℍ => (∑' x : ℚ, c x * cexp (2 * π * I * (x : ℂ) * τ)) / eta8 τ) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  set K := ∑' x : ℚ, ‖c x‖ * Real.exp (-2 * π * ((x : ℝ) - 1 / 3) * y₀) with hK
  have hsK : Summable fun x : ℚ => ‖c x‖ * Real.exp (-2 * π * ((x : ℝ) - 1 / 3) * y₀) := by
    refine (hsum.mul_left (Real.exp (2 * π * y₀ / 3))).congr fun x => ?_
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  refine ⟨K * (1 + 228 / 48), max 1 y₀, fun τ hτ => ?_⟩
  have hy1 : 1 ≤ τ.im := le_trans (le_max_left _ _) hτ
  have hyy : y₀ ≤ τ.im := le_trans (le_max_right _ _) hτ
  have hle : ∀ x : ℚ, ‖c x * cexp (2 * π * I * (x : ℂ) * τ)‖ ≤
      Real.exp (-2 * π * τ.im / 3) *
        (‖c x‖ * Real.exp (-2 * π * ((x : ℝ) - 1 / 3) * y₀)) := by
    intro x
    rw [norm_qterm_rat]
    by_cases hc : c x = 0
    · simp [hc]
    · have hx' : ((1 / 3 : ℚ) : ℝ) ≤ ((x : ℚ) : ℝ) := Rat.cast_le.2 (hsupp x hc)
      have hx : (1 / 3 : ℝ) ≤ (x : ℝ) := by push_cast at hx'; exact hx'
      rw [mul_left_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have hpi := Real.pi_pos
      nlinarith [mul_nonneg (mul_nonneg hpi.le (sub_nonneg.2 hx)) (sub_nonneg.2 hyy)]
  have hsR := hsK.mul_left (Real.exp (-2 * π * τ.im / 3))
  have hsN : Summable fun x : ℚ => ‖c x * cexp (2 * π * I * (x : ℂ) * τ)‖ :=
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) hle hsR
  have hnum : ‖∑' x : ℚ, c x * cexp (2 * π * I * (x : ℂ) * τ)‖ ≤
      Real.exp (-2 * π * τ.im / 3) * K := by
    calc ‖∑' x : ℚ, c x * cexp (2 * π * I * (x : ℂ) * τ)‖
        ≤ ∑' x : ℚ, ‖c x * cexp (2 * π * I * (x : ℂ) * τ)‖ := norm_tsum_le_tsum_norm hsN
      _ ≤ ∑' x : ℚ, Real.exp (-2 * π * τ.im / 3) *
          (‖c x‖ * Real.exp (-2 * π * ((x : ℝ) - 1 / 3) * y₀)) := hsN.tsum_le_tsum hle hsR
      _ = Real.exp (-2 * π * τ.im / 3) * K := tsum_mul_left
  have heta := norm_inv_eta8_le (τ := (τ : ℂ)) hy1
  have hK0 : 0 ≤ K := tsum_nonneg fun x => by positivity
  have hexp : Real.exp (-2 * π * τ.im / 3) * Real.exp (2 * π * τ.im / 3) = 1 := by
    rw [← Real.exp_add, show -2 * π * τ.im / 3 + 2 * π * τ.im / 3 = 0 by ring, Real.exp_zero]
  calc ‖(∑' x : ℚ, c x * cexp (2 * π * I * (x : ℂ) * τ)) / eta8 τ‖
      = ‖∑' x : ℚ, c x * cexp (2 * π * I * (x : ℂ) * τ)‖ * ‖(eta8 τ)⁻¹‖ := by
        rw [div_eq_mul_inv, norm_mul]
    _ ≤ (Real.exp (-2 * π * τ.im / 3) * K) *
        ((1 + 228 / 48) * Real.exp (2 * π * τ.im / 3)) :=
        mul_le_mul hnum heta (norm_nonneg _) (by positivity)
    _ = K * (1 + 228 / 48) * (Real.exp (-2 * π * τ.im / 3) * Real.exp (2 * π * τ.im / 3)) := by
        ring
    _ = K * (1 + 228 / 48) := by rw [hexp, mul_one]

/-- Linear combinations of absolutely convergent `q`-series. -/
theorem tsum_sub_lincomb (a b b' : ℚ → ℂ) (l m : ℂ)
    (ha : ∀ y : ℝ, 0 < y → Summable fun e : ℚ => ‖a e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hb : ∀ y : ℝ, 0 < y → Summable fun e : ℚ => ‖b e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hb' : ∀ y : ℝ, 0 < y → Summable fun e : ℚ => ‖b' e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (τ : ℍ) :
    ∑' e : ℚ, a e * cexp (2 * π * I * (e : ℂ) * τ) -
        (l * ∑' e : ℚ, b e * cexp (2 * π * I * (e : ℂ) * τ) +
          m * ∑' e : ℚ, b' e * cexp (2 * π * I * (e : ℂ) * τ)) =
      ∑' e : ℚ, (a e - l * b e - m * b' e) * cexp (2 * π * I * (e : ℂ) * τ) := by
  have s0 := summable_qseries_rat ha τ
  have s1 := (summable_qseries_rat hb τ).mul_left l
  have s2 := (summable_qseries_rat hb' τ).mul_left m
  rw [← tsum_mul_left, ← tsum_mul_left, ← s1.tsum_add s2, ← s0.tsum_sub (s1.add s2)]
  refine tsum_congr fun e => ?_
  ring

/-- Absolute convergence of a linear combination. -/
theorem summable_lincomb (a b b' : ℚ → ℂ) (l m : ℂ) {y : ℝ}
    (ha : Summable fun e : ℚ => ‖a e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hb : Summable fun e : ℚ => ‖b e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hb' : Summable fun e : ℚ => ‖b' e‖ * Real.exp (-2 * π * (e : ℝ) * y)) :
    Summable fun e : ℚ => ‖a e - l * b e - m * b' e‖ * Real.exp (-2 * π * (e : ℝ) * y) := by
  refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_)
    ((ha.add (hb.mul_left ‖l‖)).add (hb'.mul_left ‖m‖))
  have hn : ‖a e - l * b e - m * b' e‖ ≤ ‖a e‖ + ‖l‖ * ‖b e‖ + ‖m‖ * ‖b' e‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
  have hE := (Real.exp_pos (-2 * π * (e : ℝ) * y)).le
  calc ‖a e - l * b e - m * b' e‖ * Real.exp (-2 * π * (e : ℝ) * y)
      ≤ (‖a e‖ + ‖l‖ * ‖b e‖ + ‖m‖ * ‖b' e‖) * Real.exp (-2 * π * (e : ℝ) * y) :=
        mul_le_mul_of_nonneg_right hn hE
    _ = _ := by ring

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.norm_inv_eta8_le
#print axioms HaagerupIzumi.C8.Theta.isBoundedAtImInfty_tsum_div_eta8
#print axioms HaagerupIzumi.C8.Theta.tsum_sub_lincomb
#print axioms HaagerupIzumi.C8.Theta.summable_lincomb
