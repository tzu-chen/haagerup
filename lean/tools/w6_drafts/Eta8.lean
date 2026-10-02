module

public import HaagerupIzumi.C8.Theta.PoissonPi
public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# The weight-four factor `η⁸`

W6 phase 2, plan item 3 (`Theta/W6_PLAN.md`).  In the proof of Proposition
`prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) the weight-four theta vectors are divided by
`η⁸` to obtain weight-zero vector-valued functions for `lem:pole-cancellation`.  From Mathlib's
Dedekind eta `ModularForm.eta`, `η(τ) = q^{1/24} ∏_{n ≥ 1} (1 - qⁿ)`, we prove:

* `eta8_S`: `η⁸(-1/τ) = τ⁴ η⁸(τ)` for `Im τ > 0` (from Mathlib's
  `ModularForm.eta_comp_eq_csqrt_I_inv`, `η(-1/τ) = (√i)⁻¹ √τ η(τ)`; `(√i)⁸ = i⁴ = 1`);
* `eta8_T`: `η⁸(τ+1) = e(1/3) η⁸(τ)` (for all `τ`; `η(τ+1) = e(1/24) η(τ)`);
* `eta8_ne_zero`, `differentiableOn_eta8`;
* the leading `q`-expansion data for the polar part of `1/η⁸`:
  `η⁸ = q^{1/3} P⁸` with `P = ∏_{n ≥ 1} (1 - qⁿ)` (`eta8_eq`), `‖P - 1‖ ≤ 6‖q‖` for
  `‖q‖ ≤ 1/2` (`norm_etaProd_sub_one_le`), and `‖η⁸(τ)⁻¹ - q^{-1/3}‖ ≤ 228 ‖q‖ ‖q^{-1/3}‖` for
  `‖q‖ ≤ 1/48` (`norm_inv_eta8_sub_le`), which holds once `Im τ ≥ 1`
  (`norm_qParam_one_le_of_one_le_im`).  Here `q = e(τ)` is `Function.Periodic.qParam 1 τ`,
  `q^{1/3} = Function.Periodic.qParam 3 τ` and `q^{-1/3} = Function.Periodic.qParam (-3) τ`.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex
open scoped Real

namespace HaagerupIzumi.C8
namespace Theta

/-- `η⁸`. -/
def eta8 (τ : ℂ) : ℂ := ModularForm.eta τ ^ 8

/-! ## `S`, `T`, non-vanishing, holomorphy -/

theorem csqrt_pow_eight {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 8 = z ^ 4 := by
  rw [sqrt_eq_exp hz, ← Complex.exp_nat_mul,
    show ((8 : ℕ) : ℂ) * (log z / 2) = ((4 : ℕ) : ℂ) * log z by push_cast; ring,
    Complex.exp_nat_mul, Complex.exp_log hz]

theorem csqrt_I_pow_eight : Complex.sqrt I ^ 8 = 1 := by
  rw [csqrt_pow_eight I_ne_zero, Complex.I_pow_four]

/-- **`S`-law of `η⁸`**: `η⁸(-1/τ) = τ⁴ η⁸(τ)`. -/
theorem eta8_S {τ : ℂ} (hτ : 0 < τ.im) : eta8 (-1 / τ) = τ ^ 4 * eta8 τ := by
  have h := ModularForm.eta_comp_eq_csqrt_I_inv (show τ ∈ UpperHalfPlane.upperHalfPlaneSet from hτ)
  simp only [Function.comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at h
  have hτ0 : τ ≠ 0 := fun h0 => by simp [h0] at hτ
  unfold eta8
  rw [h, mul_pow, mul_pow, inv_pow, csqrt_I_pow_eight, csqrt_pow_eight hτ0, inv_one, one_mul]

/-- `η(τ+1) = e(1/24) η(τ)`. -/
theorem eta_add_one (τ : ℂ) : ModularForm.eta (τ + 1) = eChar (1 / 24) * ModularForm.eta τ := by
  have hq : Function.Periodic.qParam 1 (τ + 1) = Function.Periodic.qParam 1 τ := by
    unfold Function.Periodic.qParam
    rw [Complex.exp_eq_exp_iff_exists_int]
    exact ⟨1, by push_cast; ring⟩
  have h24 : Function.Periodic.qParam 24 (τ + 1) =
      eChar (1 / 24) * Function.Periodic.qParam 24 τ := by
    simp only [Function.Periodic.qParam, eChar]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold ModularForm.eta
  simp only [ModularForm.eta_q, hq, h24]
  ring

/-- **`T`-law of `η⁸`**: `η⁸(τ+1) = e(1/3) η⁸(τ)`. -/
theorem eta8_T (τ : ℂ) : eta8 (τ + 1) = eChar (1 / 3) * eta8 τ := by
  have h : eChar (1 / 24) ^ 8 = eChar (1 / 3) := by
    simp only [eChar]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  unfold eta8
  rw [eta_add_one, mul_pow, h]

theorem eta8_ne_zero {τ : ℂ} (hτ : 0 < τ.im) : eta8 τ ≠ 0 :=
  pow_ne_zero 8 (ModularForm.eta_ne_zero hτ)

theorem differentiableOn_eta8 : DifferentiableOn ℂ eta8 {τ : ℂ | 0 < τ.im} := fun τ hτ =>
  ((ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet hτ).pow 8).differentiableWithinAt

/-! ## The product `P = ∏ (1 - qⁿ)` and the polar part of `1/η⁸` -/

/-- `P(τ) = ∏_{n ≥ 0} (1 - q^{n+1})`, `q = e(τ)`. -/
def etaProd (τ : ℂ) : ℂ := ∏' n : ℕ, (1 - Function.Periodic.qParam 1 τ ^ (n + 1))

theorem eta_eq_qParam_mul_etaProd (τ : ℂ) :
    ModularForm.eta τ = Function.Periodic.qParam 24 τ * etaProd τ := rfl

/-- `η⁸ = q^{1/3} P⁸`. -/
theorem eta8_eq (τ : ℂ) : eta8 τ = Function.Periodic.qParam 3 τ * etaProd τ ^ 8 := by
  unfold eta8
  rw [eta_eq_qParam_mul_etaProd, mul_pow]
  congr 1
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `1/η⁸ = q^{-1/3} P⁻⁸`. -/
theorem inv_eta8_eq (τ : ℂ) :
    (eta8 τ)⁻¹ = Function.Periodic.qParam (-3) τ * (etaProd τ ^ 8)⁻¹ := by
  rw [eta8_eq, mul_inv]
  congr 1
  simp only [Function.Periodic.qParam]
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem norm_tprod_one_sub_pow_sub_one_le {q : ℂ} (hq : ‖q‖ < 1) :
    ‖∏' n : ℕ, (1 - q ^ (n + 1)) - 1‖ ≤ Real.exp (‖q‖ / (1 - ‖q‖)) - 1 := by
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hsum : Summable fun i : ℕ => ‖q‖ ^ (i + 1) :=
    ((summable_geometric_of_lt_one hr0 hq).mul_left ‖q‖).congr fun i => by ring
  have htsum : ∑' i : ℕ, ‖q‖ ^ (i + 1) = ‖q‖ / (1 - ‖q‖) := by
    rw [show (fun i : ℕ => ‖q‖ ^ (i + 1)) = fun i => ‖q‖ * ‖q‖ ^ i from
      funext fun i => pow_succ' _ _, tsum_mul_left, tsum_geometric_of_lt_one hr0 hq,
      div_eq_mul_inv]
  have ht := ((ModularForm.multipliable_one_sub_pow hq).hasProd.tendsto_prod_nat.sub_const
    1).norm
  refine le_of_tendsto ht (Filter.Eventually.of_forall fun N => ?_)
  have h1 := Finset.norm_prod_one_add_sub_one_le (Finset.range N) (fun i => -q ^ (i + 1))
  simp only [← sub_eq_add_neg, norm_neg, norm_pow] at h1
  refine h1.trans (sub_le_sub_right (Real.exp_le_exp.2 ?_) 1)
  rw [← htsum]
  exact hsum.sum_le_tsum _ fun i _ => by positivity

theorem exp_div_one_sub_sub_one_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (x / (1 - x)) - 1 ≤ 6 * x := by
  have h1 : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpos := Real.exp_pos (2 * x)
  have h2 : Real.exp (2 * x) - 1 ≤ 2 * x * Real.exp (2 * x) := by
    have ha := Real.add_one_le_exp (-(2 * x))
    have hm : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by
      rw [← Real.exp_add]
      simp
    nlinarith [mul_le_mul_of_nonneg_right ha hpos.le]
  have h3 : Real.exp (2 * x) ≤ 3 := by
    have he := Real.exp_one_lt_d9
    have : Real.exp (2 * x) ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    norm_num at he
    linarith
  calc Real.exp (x / (1 - x)) - 1 ≤ Real.exp (2 * x) - 1 :=
        sub_le_sub_right (Real.exp_le_exp.2 h1) 1
    _ ≤ 2 * x * Real.exp (2 * x) := h2
    _ ≤ 2 * x * 3 := mul_le_mul_of_nonneg_left h3 (by linarith)
    _ = 6 * x := by ring

/-- `‖P(τ) - 1‖ ≤ 6 ‖q‖` for `‖q‖ ≤ 1/2`. -/
theorem norm_etaProd_sub_one_le {τ : ℂ} (h : ‖Function.Periodic.qParam 1 τ‖ ≤ 1 / 2) :
    ‖etaProd τ - 1‖ ≤ 6 * ‖Function.Periodic.qParam 1 τ‖ :=
  (norm_tprod_one_sub_pow_sub_one_le (by linarith)).trans
    (exp_div_one_sub_sub_one_le (norm_nonneg _) h)

theorem norm_pow_sub_one_le {w : ℂ} {ε : ℝ} (hε : ε ≤ 1 / 8) (hw : ‖w - 1‖ ≤ ε) (n : ℕ) :
    ‖w ^ n - 1‖ ≤ 8 * ε * ((9 / 8 : ℝ) ^ n - 1) := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hw
  have hwn : ‖w‖ ≤ 9 / 8 := by
    calc ‖w‖ = ‖1 + (w - 1)‖ := by
          congr 1
          ring
      _ ≤ ‖(1 : ℂ)‖ + ‖w - 1‖ := norm_add_le _ _
      _ ≤ 9 / 8 := by rw [norm_one]; linarith
  induction n with
  | zero => simp
  | succ n ih =>
    calc ‖w ^ (n + 1) - 1‖ = ‖w * (w ^ n - 1) + (w - 1)‖ := by
          congr 1
          ring
      _ ≤ ‖w‖ * ‖w ^ n - 1‖ + ‖w - 1‖ := (norm_add_le _ _).trans (by rw [norm_mul])
      _ ≤ 9 / 8 * (8 * ε * ((9 / 8 : ℝ) ^ n - 1)) + ε := by gcongr
      _ = 8 * ε * ((9 / 8 : ℝ) ^ (n + 1) - 1) := by ring

theorem norm_inv_pow_eight_sub_one_le {w : ℂ} {ε : ℝ} (hε : ε ≤ 1 / 8) (hw : ‖w - 1‖ ≤ ε) :
    ‖(w ^ 8)⁻¹ - 1‖ ≤ 38 * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hw
  have hw7 : 7 / 8 ≤ ‖w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) w
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw7
    norm_num at hw7
  have h8 := norm_pow_sub_one_le hε hw 8
  have heq : (w ^ 8)⁻¹ - 1 = (1 - w ^ 8) * (w ^ 8)⁻¹ := by
    field_simp
  rw [heq, norm_mul, norm_inv, norm_pow, norm_sub_rev]
  have hpow : (7 / 8 : ℝ) ^ 8 ≤ ‖w‖ ^ 8 := pow_le_pow_left₀ (by norm_num) hw7 8
  have hinv : (‖w‖ ^ 8)⁻¹ ≤ ((7 / 8 : ℝ) ^ 8)⁻¹ := inv_anti₀ (by positivity) hpow
  have hc : 8 * ((9 / 8 : ℝ) ^ 8 - 1) * ((7 / 8 : ℝ) ^ 8)⁻¹ ≤ 38 := by norm_num
  calc ‖w ^ 8 - 1‖ * (‖w‖ ^ 8)⁻¹
      ≤ (8 * ε * ((9 / 8 : ℝ) ^ 8 - 1)) * ((7 / 8 : ℝ) ^ 8)⁻¹ :=
        mul_le_mul h8 hinv (by positivity) (by positivity)
    _ = (8 * ((9 / 8 : ℝ) ^ 8 - 1) * ((7 / 8 : ℝ) ^ 8)⁻¹) * ε := by ring
    _ ≤ 38 * ε := mul_le_mul_of_nonneg_right hc hε0

/-- `‖P⁻⁸ - 1‖ ≤ 228 ‖q‖` for `‖q‖ ≤ 1/48`. -/
theorem norm_inv_etaProd_pow_sub_one_le {τ : ℂ}
    (h : ‖Function.Periodic.qParam 1 τ‖ ≤ 1 / 48) :
    ‖(etaProd τ ^ 8)⁻¹ - 1‖ ≤ 228 * ‖Function.Periodic.qParam 1 τ‖ := by
  have h1 := norm_etaProd_sub_one_le (τ := τ) (by linarith)
  have h2 := norm_inv_pow_eight_sub_one_le (by linarith) h1
  linarith

/-- **Polar part of `1/η⁸`**: `‖η⁸(τ)⁻¹ - q^{-1/3}‖ ≤ 228 ‖q‖ ‖q^{-1/3}‖` for `‖q‖ ≤ 1/48`. -/
theorem norm_inv_eta8_sub_le {τ : ℂ} (h : ‖Function.Periodic.qParam 1 τ‖ ≤ 1 / 48) :
    ‖(eta8 τ)⁻¹ - Function.Periodic.qParam (-3) τ‖ ≤
      228 * ‖Function.Periodic.qParam 1 τ‖ * ‖Function.Periodic.qParam (-3) τ‖ := by
  rw [inv_eta8_eq, show Function.Periodic.qParam (-3) τ * (etaProd τ ^ 8)⁻¹ -
      Function.Periodic.qParam (-3) τ =
      Function.Periodic.qParam (-3) τ * ((etaProd τ ^ 8)⁻¹ - 1) by ring, norm_mul]
  calc ‖Function.Periodic.qParam (-3) τ‖ * ‖(etaProd τ ^ 8)⁻¹ - 1‖
      ≤ ‖Function.Periodic.qParam (-3) τ‖ * (228 * ‖Function.Periodic.qParam 1 τ‖) :=
        mul_le_mul_of_nonneg_left (norm_inv_etaProd_pow_sub_one_le h) (norm_nonneg _)
    _ = 228 * ‖Function.Periodic.qParam 1 τ‖ * ‖Function.Periodic.qParam (-3) τ‖ := by ring

/-- `‖q‖ ≤ 1/48` once `Im τ ≥ 1`. -/
theorem norm_qParam_one_le_of_one_le_im {τ : ℂ} (h : 1 ≤ τ.im) :
    ‖Function.Periodic.qParam 1 τ‖ ≤ 1 / 48 := by
  rw [Function.Periodic.norm_qParam]
  have hpi := Real.pi_gt_three
  have h2 : Real.exp 2 ≥ 5 := by
    have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at this
    linarith
  have h6 : (48 : ℝ) ≤ Real.exp 6 := by
    have : Real.exp 6 = Real.exp 2 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [this]
    have h125 : (5 : ℝ) ^ 3 ≤ Real.exp 2 ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
    linarith
  have hle : Real.exp (-2 * π * τ.im / 1) ≤ Real.exp (-6) := Real.exp_le_exp.2 (by
    rw [div_one]
    nlinarith [mul_le_mul_of_nonneg_right hpi.le (by linarith : (0 : ℝ) ≤ τ.im)])
  have hinv : Real.exp (-6) = (Real.exp 6)⁻¹ := by rw [Real.exp_neg]
  calc Real.exp (-2 * π * τ.im / 1) ≤ Real.exp (-6) := hle
    _ = (Real.exp 6)⁻¹ := hinv
    _ ≤ (48 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h6
    _ = 1 / 48 := by norm_num

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.eta8_S
#print axioms HaagerupIzumi.C8.Theta.eta8_T
#print axioms HaagerupIzumi.C8.Theta.eta8_ne_zero
#print axioms HaagerupIzumi.C8.Theta.differentiableOn_eta8
#print axioms HaagerupIzumi.C8.Theta.eta8_eq
#print axioms HaagerupIzumi.C8.Theta.norm_inv_eta8_sub_le
#print axioms HaagerupIzumi.C8.Theta.norm_qParam_one_le_of_one_le_im
