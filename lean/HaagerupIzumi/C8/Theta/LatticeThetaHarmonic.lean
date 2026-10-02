module

public import HaagerupIzumi.C8.Theta.LatticeTheta
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Theta series with harmonic quadratic weights

Stretch goal of the first phase of work item W6 (`C8/ROADMAP.md`).  The proof of Proposition
`prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) uses the theta series
`Θ_{H,γ}(τ) = ∑_{x ∈ γ + L} H(x) q^{(x,x)/2}` of quadratic polynomials `H` that are harmonic
for the form of `L` ("Poisson summation gives vector-valued theta series of weight four",
line 3656).  Here `H = Q_M`, `Q_M(x) = x·Mx` (`qf M`), and harmonicity is
`∑ᵢⱼ (G⁻¹)ᵢⱼ Mᵢⱼ = 0` (the condition checked in `Theta/Harmonic.lean` as `pairTrace`).

## Method

Hecke's identity `𝓕[H e^{-π a Q}] = (const) a^{-2} H(G⁻¹ξ) 𝓕[e^{-π a Q}]` for harmonic `H` is
obtained by differentiating under the integral sign along modulations: for a weight `p`,
`t ↦ 𝓕[p(x) e(t w·x)](ξ) = 𝓕p(ξ - t w)` (`fourierPi_mul_eChar`) has derivative
`2πi 𝓕[(w·x) p](ξ)` at `t = 0` (`hasDerivAt_fourierPi_mul_eChar`).  Applied to the Gaussian
(whose transform is explicit) this gives `𝓕[(w·x) g]` (`fourierPi_dot_mul_gaussCM`), and
applied once more `𝓕[(u·x)(w·x) g]` (`fourierPi_dot_dot_mul_gaussCM`).  The required
decay bounds are reduced to the Gaussian with half the parameter
(`exists_poly_gauss_bound`).

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Real Complex Matrix MeasureTheory Filter Topology

namespace HaagerupIzumi.C8
namespace Theta

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Elementary properties of `fourierPi` -/

omit [DecidableEq d] in
/-- Modulation is translation of the Fourier transform: `𝓕[p · e(t w·x)](ξ) = 𝓕p(ξ - t w)`. -/
theorem fourierPi_mul_eChar (p : (d → ℝ) → ℂ) (w : d → ℝ) (t : ℝ) (ξ : d → ℝ) :
    fourierPi (fun x => p x * eChar (t * (w ⬝ᵥ x))) ξ = fourierPi p (ξ - t • w) := by
  unfold fourierPi
  congr 1
  funext x
  have h : -(x ⬝ᵥ (ξ - t • w)) = -(x ⬝ᵥ ξ) + t * (w ⬝ᵥ x) := by
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm x w]
    ring
  rw [h, eChar_add]
  ring

omit [DecidableEq d] in
theorem fourierPi_const_mul (c : ℂ) (p : (d → ℝ) → ℂ) (ξ : d → ℝ) :
    fourierPi (fun x => c * p x) ξ = c * fourierPi p ξ := by
  unfold fourierPi
  rw [← integral_const_mul]
  congr 1
  funext x
  ring

omit [DecidableEq d] in
theorem fourierPi_finset_sum {ι : Type*} (s : Finset ι) (p : ι → (d → ℝ) → ℂ)
    (hp : ∀ i ∈ s, Integrable (p i)) (ξ : d → ℝ) :
    fourierPi (fun x => ∑ i ∈ s, p i x) ξ = ∑ i ∈ s, fourierPi (p i) ξ := by
  unfold fourierPi
  simp_rw [Finset.mul_sum]
  refine integral_finsetSum s fun i hi => ?_
  refine (hp i hi).norm.mono' ((continuous_eChar_neg_dot ξ).aestronglyMeasurable.mul
    (hp i hi).1) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_eChar, one_mul]

/-! ## Differentiation under the integral sign along modulations -/

theorem hasDerivAt_eChar_mul (r t : ℝ) :
    HasDerivAt (fun s : ℝ => eChar (s * r)) (2 * π * I * r * eChar (t * r)) t := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * π * (s * r)) (2 * π * (1 * r)) t :=
    ((hasDerivAt_id' t).mul_const r).const_mul (2 * π)
  have h2 := (h1.ofReal_comp.mul_const I).cexp
  unfold eChar
  convert h2 using 1
  push_cast
  ring

omit [DecidableEq d] in
/-- `t ↦ 𝓕[p · e(t w·x)](ξ)` has derivative `2πi 𝓕[(w·x) p](ξ)` at `0`. -/
theorem hasDerivAt_fourierPi_mul_eChar {p : (d → ℝ) → ℂ} (hp : Continuous p)
    (hpi : Integrable p) (w : d → ℝ) (hwp : Integrable fun x => ((w ⬝ᵥ x : ℝ) : ℂ) * p x)
    (ξ : d → ℝ) :
    HasDerivAt (fun t : ℝ => fourierPi (fun x => p x * eChar (t * (w ⬝ᵥ x))) ξ)
      (2 * π * I * fourierPi (fun x => ((w ⬝ᵥ x : ℝ) : ℂ) * p x) ξ) 0 := by
  have hdot : Continuous fun x : d → ℝ => w ⬝ᵥ x := continuous_const.dotProduct continuous_id
  have hcont : ∀ t : ℝ, Continuous fun x : d → ℝ =>
      eChar (-(x ⬝ᵥ ξ)) * (p x * eChar (t * (w ⬝ᵥ x))) := fun t =>
    (continuous_eChar_neg_dot ξ).mul (hp.mul (continuous_eChar.comp (continuous_const.mul hdot)))
  have hcont' : ∀ t : ℝ, Continuous fun x : d → ℝ =>
      eChar (-(x ⬝ᵥ ξ)) * (p x * (2 * π * I * ((w ⬝ᵥ x : ℝ) : ℂ) * eChar (t * (w ⬝ᵥ x)))) :=
    fun t => (continuous_eChar_neg_dot ξ).mul (hp.mul ((continuous_const.mul
      (Complex.continuous_ofReal.comp hdot)).mul (continuous_eChar.comp (continuous_const.mul hdot))))
  have hint0 : Integrable fun x : d → ℝ =>
      eChar (-(x ⬝ᵥ ξ)) * (p x * eChar ((0 : ℝ) * (w ⬝ᵥ x))) := by
    refine hpi.norm.mono' (hcont 0).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, norm_eChar, norm_eChar, one_mul, mul_one]
  have hbound : ∀ (x : d → ℝ) (t : ℝ),
      ‖eChar (-(x ⬝ᵥ ξ)) * (p x * (2 * π * I * ((w ⬝ᵥ x : ℝ) : ℂ) * eChar (t * (w ⬝ᵥ x))))‖ ≤
        2 * π * ‖((w ⬝ᵥ x : ℝ) : ℂ) * p x‖ := by
    intro x t
    refine le_of_eq ?_
    simp only [norm_mul, norm_eChar, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_ofNat, abs_of_pos pi_pos, one_mul, mul_one]
    ring
  have hdiff : ∀ (x : d → ℝ) (t : ℝ),
      HasDerivAt (fun t : ℝ => eChar (-(x ⬝ᵥ ξ)) * (p x * eChar (t * (w ⬝ᵥ x))))
        (eChar (-(x ⬝ᵥ ξ)) * (p x * (2 * π * I * ((w ⬝ᵥ x : ℝ) : ℂ) * eChar (t * (w ⬝ᵥ x)))))
        t := fun x t =>
    ((hasDerivAt_eChar_mul (w ⬝ᵥ x) t).const_mul (p x)).const_mul _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0 : ℝ))
    (s := Set.univ)
    (F := fun (t : ℝ) (x : d → ℝ) => eChar (-(x ⬝ᵥ ξ)) * (p x * eChar (t * (w ⬝ᵥ x))))
    (F' := fun (t : ℝ) (x : d → ℝ) =>
      eChar (-(x ⬝ᵥ ξ)) * (p x * (2 * π * I * ((w ⬝ᵥ x : ℝ) : ℂ) * eChar (t * (w ⬝ᵥ x)))))
    (bound := fun x => 2 * π * ‖((w ⬝ᵥ x : ℝ) : ℂ) * p x‖)
    Filter.univ_mem (Eventually.of_forall fun t => (hcont t).aestronglyMeasurable) hint0
    (hcont' 0).aestronglyMeasurable (Eventually.of_forall fun x t _ => hbound x t)
    (hwp.norm.const_mul (2 * π)) (Eventually.of_forall fun x t _ => hdiff x t)
  refine key.2.congr_deriv ?_
  unfold fourierPi
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [zero_mul, eChar_zero]
  ring

/-! ## Explicit derivatives along lines -/

omit [DecidableEq d] in
theorem sqNorm_sub_smul (P' : Matrix d d ℝ) (ξ w : d → ℝ) (t : ℝ) :
    (P' *ᵥ (ξ - t • w)) ⬝ᵥ (P' *ᵥ (ξ - t • w)) =
      (P' *ᵥ ξ) ⬝ᵥ (P' *ᵥ ξ) - 2 * t * ((P' *ᵥ w) ⬝ᵥ (P' *ᵥ ξ)) +
        t ^ 2 * ((P' *ᵥ w) ⬝ᵥ (P' *ᵥ w)) := by
  simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (P' *ᵥ ξ) (P' *ᵥ w)]
  ring

omit [DecidableEq d] in
theorem dot_mulVec_sub_smul (P' : Matrix d d ℝ) (u ξ w : d → ℝ) (t : ℝ) :
    (P' *ᵥ u) ⬝ᵥ (P' *ᵥ (ξ - t • w)) =
      (P' *ᵥ u) ⬝ᵥ (P' *ᵥ ξ) - t * ((P' *ᵥ u) ⬝ᵥ (P' *ᵥ w)) := by
  simp only [mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, smul_eq_mul]

theorem hasDerivAt_cexp_quad_zero (b : ℂ) (Q0 B Q1 : ℝ) :
    HasDerivAt (fun s : ℝ => cexp (-π * b * ((Q0 - 2 * s * B + s ^ 2 * Q1 : ℝ) : ℂ)))
      (2 * π * b * B * cexp (-π * b * (Q0 : ℂ))) 0 := by
  have hf : HasDerivAt (fun s : ℝ => Q0 - 2 * s * B + s ^ 2 * Q1) (-2 * B) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => 2 * s * B) (2 * 1 * B) 0 :=
      ((hasDerivAt_id' 0).const_mul 2).mul_const B
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 * Q1) (((2 : ℕ) : ℝ) * (0 : ℝ) ^ (2 - 1) * Q1) 0 :=
      (hasDerivAt_pow 2 0).mul_const Q1
    exact (((hasDerivAt_const (0 : ℝ) Q0).sub h1).add h2).congr_deriv (by norm_num)
  have h := (hf.ofReal_comp.const_mul (-π * b)).cexp
  refine h.congr_deriv ?_
  rw [show (Q0 - 2 * 0 * B + 0 ^ 2 * Q1 : ℝ) = Q0 by ring]
  push_cast
  ring

theorem hasDerivAt_lin_mul_cexp_quad_zero (b : ℂ) (L0 L1 Q0 B Q1 : ℝ) :
    HasDerivAt (fun s : ℝ => ((L0 - s * L1 : ℝ) : ℂ) *
        cexp (-π * b * ((Q0 - 2 * s * B + s ^ 2 * Q1 : ℝ) : ℂ)))
      (-(L1 : ℂ) * cexp (-π * b * (Q0 : ℂ)) +
        (L0 : ℂ) * (2 * π * b * B * cexp (-π * b * (Q0 : ℂ)))) 0 := by
  have hL : HasDerivAt (fun s : ℝ => L0 - s * L1) (-(1 * L1)) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).mul_const L1).const_sub L0
  have h := hL.ofReal_comp.mul (hasDerivAt_cexp_quad_zero b Q0 B Q1)
  refine h.congr_deriv ?_
  rw [show (Q0 - 2 * 0 * B + 0 ^ 2 * Q1 : ℝ) = Q0 by ring, show (L0 - 0 * L1 : ℝ) = L0 by ring]
  push_cast
  ring

/-! ## Polynomial bounds -/

omit [DecidableEq d] in
theorem dotProduct_self_nonneg' (x : d → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

omit [DecidableEq d] in
theorem abs_coord_le (x : d → ℝ) (i : d) : |x i| ≤ 1 + x ⬝ᵥ x := by
  have h1 : x i * x i ≤ x ⬝ᵥ x :=
    Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  nlinarith [sq_nonneg (|x i| - 1), sq_abs (x i), abs_nonneg (x i)]

omit [DecidableEq d] in
theorem abs_dotProduct_le (u x : d → ℝ) : |u ⬝ᵥ x| ≤ (∑ i, |u i|) * (1 + x ⬝ᵥ x) := by
  calc |u ⬝ᵥ x| = |∑ i, u i * x i| := rfl
    _ ≤ ∑ i, |u i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |u i| * (1 + x ⬝ᵥ x) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_coord_le x i) (abs_nonneg _)
    _ = (∑ i, |u i|) * (1 + x ⬝ᵥ x) := (Finset.sum_mul ..).symm

omit [DecidableEq d] in
theorem abs_qf_le (M : Matrix d d ℝ) (x : d → ℝ) :
    |qf M x| ≤ (∑ i, ∑ j, |M i j|) * (1 + x ⬝ᵥ x) ^ 2 := by
  have hX : 0 ≤ 1 + x ⬝ᵥ x := by linarith [dotProduct_self_nonneg' x]
  calc |qf M x| = |∑ i, x i * (M *ᵥ x) i| := rfl
    _ ≤ ∑ i, |x i * (M *ᵥ x) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (1 + x ⬝ᵥ x) * ((∑ j, |M i j|) * (1 + x ⬝ᵥ x)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_coord_le x i) (abs_dotProduct_le (fun j => M i j) x)
          (abs_nonneg _) hX
    _ = (∑ i, ∑ j, |M i j|) * (1 + x ⬝ᵥ x) ^ 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by ring

/-- `(1 + y)² e^{-sy} ≤ (1 + 4/s)² e^{-sy/2}` for `s > 0`, `y ≥ 0`. -/
theorem one_add_sq_mul_exp_le {s y : ℝ} (hs : 0 < s) (hy : 0 ≤ y) :
    (1 + y) ^ 2 * rexp (-s * y) ≤ (1 + 4 / s) ^ 2 * rexp (-(s / 2) * y) := by
  have hsy : 4 / s * (s * y / 4) = y := by field_simp
  have h1 : 1 + y ≤ (1 + 4 / s) * (1 + s * y / 4) := by
    have e : (1 + 4 / s) * (1 + s * y / 4) = 1 + s * y / 4 + 4 / s + 4 / s * (s * y / 4) := by
      ring
    rw [e, hsy]
    have : 0 < 4 / s := by positivity
    nlinarith [mul_nonneg hs.le hy]
  have h2 : 1 + s * y / 4 ≤ rexp (s * y / 4) := by linarith [Real.add_one_le_exp (s * y / 4)]
  have h3 : (1 + y) ^ 2 ≤ ((1 + 4 / s) * rexp (s * y / 4)) ^ 2 :=
    pow_le_pow_left₀ (by linarith)
      (h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))) 2
  calc (1 + y) ^ 2 * rexp (-s * y)
      ≤ ((1 + 4 / s) * rexp (s * y / 4)) ^ 2 * rexp (-s * y) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = (1 + 4 / s) ^ 2 * (rexp (s * y / 4) * rexp (s * y / 4) * rexp (-s * y)) := by ring
    _ = (1 + 4 / s) ^ 2 * rexp (-(s / 2) * y) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- Polynomial weights cost half of the Gaussian decay:
`(1 + x·x)² ‖exp(-π a |Px|²)‖ ≤ K ‖exp(-π (Re a / 2) |Px|²)‖`. -/
theorem exists_poly_gauss_bound {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ} (ha : 0 < a.re) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : d → ℝ,
      (1 + x ⬝ᵥ x) ^ 2 * ‖gaussCM P a x‖ ≤ K * ‖gaussCM P ((a.re / 2 : ℝ) : ℂ) x‖ := by
  obtain ⟨c, hc, hcoer⟩ := exists_coercive hP
  have hs : 0 < π * a.re := mul_pos pi_pos ha
  refine ⟨(1 + 1 / c) ^ 2 * (1 + 4 / (π * a.re)) ^ 2, by positivity, fun x => ?_⟩
  have hY : 0 ≤ (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := dotProduct_self_nonneg' _
  have hX := dotProduct_self_nonneg' x
  have h1 : 1 + x ⬝ᵥ x ≤ (1 + 1 / c) * (1 + (P *ᵥ x) ⬝ᵥ (P *ᵥ x)) := by
    have hxY : x ⬝ᵥ x ≤ 1 / c * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc]
      linarith [hcoer x]
    have hc1 : 0 < 1 / c := by positivity
    nlinarith [mul_nonneg hc1.le hY]
  rw [gaussCM_apply, gaussCM_apply, norm_cexp_neg_pi_mul, norm_cexp_neg_pi_mul,
    Complex.ofReal_re]
  have h2 := one_add_sq_mul_exp_le hs hY
  calc (1 + x ⬝ᵥ x) ^ 2 * rexp (-(π * a.re) * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)))
      ≤ ((1 + 1 / c) * (1 + (P *ᵥ x) ⬝ᵥ (P *ᵥ x))) ^ 2 *
          rexp (-(π * a.re) * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) h1 2) (Real.exp_pos _).le
    _ = (1 + 1 / c) ^ 2 * ((1 + (P *ᵥ x) ⬝ᵥ (P *ᵥ x)) ^ 2 *
          rexp (-(π * a.re) * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)))) := by ring
    _ ≤ (1 + 1 / c) ^ 2 * ((1 + 4 / (π * a.re)) ^ 2 *
          rexp (-(π * a.re / 2) * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (1 + 1 / c) ^ 2 * (1 + 4 / (π * a.re)) ^ 2 *
          rexp (-(π * (a.re / 2)) * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x))) := by
        rw [show π * (a.re / 2) = π * a.re / 2 by ring]
        ring

theorem integrable_gaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ} (ha : 0 < a.re) :
    Integrable (gaussCM P a) :=
  integrable_of_translatesSummable (translatesSummable_gaussCM hP ha)

/-- `q · exp(-π a |Px|²)` is integrable if `‖q x‖ ≤ C (1 + x·x)²`. -/
theorem integrable_poly_mul_gaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ}
    (ha : 0 < a.re) {q : (d → ℝ) → ℂ} (hq : Continuous q) {C : ℝ} (hC : 0 ≤ C)
    (hqb : ∀ x, ‖q x‖ ≤ C * (1 + x ⬝ᵥ x) ^ 2) :
    Integrable fun x => q x * gaussCM P a x := by
  obtain ⟨K, hK0, hK⟩ := exists_poly_gauss_bound hP ha
  have hb : 0 < ((a.re / 2 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith
  refine ((integrable_gaussCM hP hb).norm.const_mul (C * K)).mono'
    (hq.mul (gaussCM P a).continuous).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  calc ‖q x‖ * ‖gaussCM P a x‖ ≤ C * (1 + x ⬝ᵥ x) ^ 2 * ‖gaussCM P a x‖ :=
        mul_le_mul_of_nonneg_right (hqb x) (norm_nonneg _)
    _ = C * ((1 + x ⬝ᵥ x) ^ 2 * ‖gaussCM P a x‖) := by ring
    _ ≤ C * (K * ‖gaussCM P ((a.re / 2 : ℝ) : ℂ) x‖) := mul_le_mul_of_nonneg_left (hK x) hC
    _ = C * K * ‖gaussCM P ((a.re / 2 : ℝ) : ℂ) x‖ := by ring

omit [DecidableEq d] in
theorem norm_dot_le (u x : d → ℝ) :
    ‖((u ⬝ᵥ x : ℝ) : ℂ)‖ ≤ (∑ i, |u i|) * (1 + x ⬝ᵥ x) ^ 2 := by
  have hX : 1 ≤ 1 + x ⬝ᵥ x := by linarith [dotProduct_self_nonneg' x]
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (abs_dotProduct_le u x).trans (mul_le_mul_of_nonneg_left ?_
    (Finset.sum_nonneg fun i _ => abs_nonneg _))
  nlinarith

omit [DecidableEq d] in
theorem norm_dot_mul_dot_le (u w x : d → ℝ) :
    ‖((w ⬝ᵥ x : ℝ) : ℂ) * ((u ⬝ᵥ x : ℝ) : ℂ)‖ ≤
      ((∑ i, |w i|) * (∑ i, |u i|)) * (1 + x ⬝ᵥ x) ^ 2 := by
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |w ⬝ᵥ x| * |u ⬝ᵥ x| ≤ ((∑ i, |w i|) * (1 + x ⬝ᵥ x)) * ((∑ i, |u i|) * (1 + x ⬝ᵥ x)) :=
        mul_le_mul (abs_dotProduct_le w x) (abs_dotProduct_le u x) (abs_nonneg _)
          (mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
            (by linarith [dotProduct_self_nonneg' x]))
    _ = ((∑ i, |w i|) * (∑ i, |u i|)) * (1 + x ⬝ᵥ x) ^ 2 := by ring

omit [DecidableEq d] in
theorem continuous_ofReal_dot (u : d → ℝ) : Continuous fun x : d → ℝ => ((u ⬝ᵥ x : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (continuous_const.dotProduct continuous_id)

/-! ## Fourier transforms of `(w·x) g` and `(w·x)(u·x) g` -/

/-- `𝓕[(w·x) e^{-π a |Px|²}](ξ) = -i a⁻¹ ⟨w, ξ⟩ 𝓕[e^{-π a |Px|²}](ξ)`, where
`⟨w, ξ⟩ = (P⁻ᵀw)·(P⁻ᵀξ) = w·G⁻¹ξ` for `G = PᵀP`. -/
theorem fourierPi_dot_mul_gaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ} (ha : 0 < a.re)
    (w ξ : d → ℝ) :
    fourierPi (fun x => ((w ⬝ᵥ x : ℝ) : ℂ) * gaussCM P a x) ξ =
      -I * a⁻¹ * ((((P⁻¹)ᵀ *ᵥ w) ⬝ᵥ ((P⁻¹)ᵀ *ᵥ ξ) : ℝ) : ℂ) * fourierPi (gaussCM P a) ξ := by
  obtain ⟨P', hP'⟩ : ∃ Q : Matrix d d ℝ, Q = (P⁻¹)ᵀ := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℂ, C = ((|P.det|⁻¹ : ℝ) : ℂ) * (1 / a) ^ (Fintype.card d / 2 : ℂ) :=
    ⟨_, rfl⟩
  have hg : ∀ η, fourierPi (gaussCM P a) η =
      C₀ * cexp (-π * a⁻¹ * (((P' *ᵥ η) ⬝ᵥ (P' *ᵥ η) : ℝ) : ℂ)) := by
    intro η
    rw [fourierPi_gaussCM hP ha, hC₀, hP']
  rw [← hP', hg]
  have hD := hasDerivAt_fourierPi_mul_eChar (gaussCM P a).continuous (integrable_gaussCM hP ha)
    w (integrable_poly_mul_gaussCM hP ha (continuous_ofReal_dot w)
      (Finset.sum_nonneg fun i _ => abs_nonneg _) (norm_dot_le w)) ξ
  have hline : (fun t : ℝ => fourierPi (fun x => gaussCM P a x * eChar (t * (w ⬝ᵥ x))) ξ) =
      fun t : ℝ => C₀ * cexp (-π * a⁻¹ * (((P' *ᵥ ξ) ⬝ᵥ (P' *ᵥ ξ) -
        2 * t * ((P' *ᵥ w) ⬝ᵥ (P' *ᵥ ξ)) + t ^ 2 * ((P' *ᵥ w) ⬝ᵥ (P' *ᵥ w)) : ℝ) : ℂ)) := by
    funext t
    rw [fourierPi_mul_eChar, hg, sqNorm_sub_smul]
  rw [hline] at hD
  have hD2 := (hasDerivAt_cexp_quad_zero a⁻¹ ((P' *ᵥ ξ) ⬝ᵥ (P' *ᵥ ξ))
    ((P' *ᵥ w) ⬝ᵥ (P' *ᵥ ξ)) ((P' *ᵥ w) ⬝ᵥ (P' *ᵥ w))).const_mul C₀
  have h := hD.unique hD2
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [pi_ne_zero, I_ne_zero]
  apply mul_left_cancel₀ h2πI
  rw [h]
  linear_combination (2 * π * a⁻¹ * (((P' *ᵥ w) ⬝ᵥ (P' *ᵥ ξ) : ℝ) : ℂ) * C₀ *
    cexp (-π * a⁻¹ * (((P' *ᵥ ξ) ⬝ᵥ (P' *ᵥ ξ) : ℝ) : ℂ))) * I_sq

/-- `𝓕[(w·x)(u·x) e^{-π a |Px|²}](ξ) =
  (a⁻¹ ⟨u, w⟩ / 2π - a⁻² ⟨u, ξ⟩⟨w, ξ⟩) 𝓕[e^{-π a |Px|²}](ξ)`. -/
theorem fourierPi_dot_dot_mul_gaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ}
    (ha : 0 < a.re) (u w ξ : d → ℝ) :
    fourierPi (fun x => ((w ⬝ᵥ x : ℝ) : ℂ) * (((u ⬝ᵥ x : ℝ) : ℂ) * gaussCM P a x)) ξ =
      (a⁻¹ / (2 * π) * ((((P⁻¹)ᵀ *ᵥ u) ⬝ᵥ ((P⁻¹)ᵀ *ᵥ w) : ℝ) : ℂ) -
        a⁻¹ ^ 2 * ((((P⁻¹)ᵀ *ᵥ u) ⬝ᵥ ((P⁻¹)ᵀ *ᵥ ξ) : ℝ) : ℂ) *
          ((((P⁻¹)ᵀ *ᵥ w) ⬝ᵥ ((P⁻¹)ᵀ *ᵥ ξ) : ℝ) : ℂ)) * fourierPi (gaussCM P a) ξ := by
  obtain ⟨P', hP'⟩ : ∃ Q : Matrix d d ℝ, Q = (P⁻¹)ᵀ := ⟨_, rfl⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℂ, C = ((|P.det|⁻¹ : ℝ) : ℂ) * (1 / a) ^ (Fintype.card d / 2 : ℂ) :=
    ⟨_, rfl⟩
  have hg : ∀ η, fourierPi (gaussCM P a) η =
      C₀ * cexp (-π * a⁻¹ * (((P' *ᵥ η) ⬝ᵥ (P' *ᵥ η) : ℝ) : ℂ)) := by
    intro η
    rw [fourierPi_gaussCM hP ha, hC₀, hP']
  have hF1 : ∀ η, fourierPi (fun x => ((u ⬝ᵥ x : ℝ) : ℂ) * gaussCM P a x) η =
      -I * a⁻¹ * (((P' *ᵥ u) ⬝ᵥ (P' *ᵥ η) : ℝ) : ℂ) * fourierPi (gaussCM P a) η := by
    intro η
    rw [fourierPi_dot_mul_gaussCM hP ha, hP']
  rw [← hP', hg]
  have hpc : Continuous fun x => ((u ⬝ᵥ x : ℝ) : ℂ) * gaussCM P a x :=
    (continuous_ofReal_dot u).mul (gaussCM P a).continuous
  have hpi : Integrable fun x => ((u ⬝ᵥ x : ℝ) : ℂ) * gaussCM P a x :=
    integrable_poly_mul_gaussCM hP ha (continuous_ofReal_dot u)
      (Finset.sum_nonneg fun i _ => abs_nonneg _) (norm_dot_le u)
  have hwpi : Integrable fun x =>
      ((w ⬝ᵥ x : ℝ) : ℂ) * (((u ⬝ᵥ x : ℝ) : ℂ) * gaussCM P a x) := by
    refine (integrable_poly_mul_gaussCM hP ha
      (q := fun x => ((w ⬝ᵥ x : ℝ) : ℂ) * ((u ⬝ᵥ x : ℝ) : ℂ))
      ((continuous_ofReal_dot w).mul (continuous_ofReal_dot u)) (mul_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)
        (Finset.sum_nonneg fun i _ => abs_nonneg _)) (norm_dot_mul_dot_le u w)).congr
      (Eventually.of_forall fun x => ?_)
    ring
  have hD := hasDerivAt_fourierPi_mul_eChar hpc hpi w hwpi ξ
  have hline : (fun t : ℝ => fourierPi
      (fun x => ((u ⬝ᵥ x : ℝ) : ℂ) * gaussCM P a x * eChar (t * (w ⬝ᵥ x))) ξ) =
      fun t : ℝ => (-I * a⁻¹ * C₀) *
        ((((P' *ᵥ u) ⬝ᵥ (P' *ᵥ ξ) - t * ((P' *ᵥ u) ⬝ᵥ (P' *ᵥ w)) : ℝ) : ℂ) *
          cexp (-π * a⁻¹ * (((P' *ᵥ ξ) ⬝ᵥ (P' *ᵥ ξ) - 2 * t * ((P' *ᵥ w) ⬝ᵥ (P' *ᵥ ξ)) +
            t ^ 2 * ((P' *ᵥ w) ⬝ᵥ (P' *ᵥ w)) : ℝ) : ℂ))) := by
    funext t
    rw [fourierPi_mul_eChar, hF1, hg, dot_mulVec_sub_smul, sqNorm_sub_smul]
    ring
  rw [hline] at hD
  have hD2 := (hasDerivAt_lin_mul_cexp_quad_zero a⁻¹ ((P' *ᵥ u) ⬝ᵥ (P' *ᵥ ξ))
    ((P' *ᵥ u) ⬝ᵥ (P' *ᵥ w)) ((P' *ᵥ ξ) ⬝ᵥ (P' *ᵥ ξ)) ((P' *ᵥ w) ⬝ᵥ (P' *ᵥ ξ))
    ((P' *ᵥ w) ⬝ᵥ (P' *ᵥ w))).const_mul (-I * a⁻¹ * C₀)
  have h := hD.unique hD2
  have h2πI : (2 * π * I : ℂ) ≠ 0 := by simp [pi_ne_zero, I_ne_zero]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 pi_ne_zero
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at ha
  apply mul_left_cancel₀ h2πI
  rw [h]
  field_simp
  ring

/-! ## The harmonic weight `Q_M` -/

omit [DecidableEq d] in
theorem continuous_qf (M : Matrix d d ℝ) : Continuous fun x : d → ℝ => qf M x :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

/-- `x ↦ Q_M(x) e^{-π a |Px|²}` as a continuous map. -/
def qgaussCM (M P : Matrix d d ℝ) (a : ℂ) : C(d → ℝ, ℂ) :=
  ⟨fun x => (qf M x : ℂ) * gaussCM P a x,
    (Complex.continuous_ofReal.comp (continuous_qf M)).mul (gaussCM P a).continuous⟩

omit [DecidableEq d] in
@[simp] theorem qgaussCM_apply (M P : Matrix d d ℝ) (a : ℂ) (x : d → ℝ) :
    qgaussCM M P a x = (qf M x : ℂ) * gaussCM P a x := rfl

/-- `Q_M(x) = ∑ⱼ (Mⱼ·x)(eⱼ·x)`, `Mⱼ` the `j`-th row of `M`. -/
theorem qf_eq_sum (M : Matrix d d ℝ) (x : d → ℝ) :
    qf M x = ∑ j, ((fun k => M j k) ⬝ᵥ x) * (Pi.single j 1 ⬝ᵥ x) := by
  simp only [single_dotProduct, one_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  rfl

omit [DecidableEq d] in
theorem dot_mulVec_mulVec (P' : Matrix d d ℝ) (u v : d → ℝ) :
    (P' *ᵥ u) ⬝ᵥ (P' *ᵥ v) = u ⬝ᵥ ((P'ᵀ * P') *ᵥ v) := by
  rw [← mulVec_mulVec, dotProduct_mulVec u P'ᵀ (P' *ᵥ v), vecMul_transpose]

theorem integrable_dot_dot_mul_gaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ}
    (ha : 0 < a.re) (u w : d → ℝ) :
    Integrable fun x => ((w ⬝ᵥ x : ℝ) : ℂ) * (((u ⬝ᵥ x : ℝ) : ℂ) * gaussCM P a x) := by
  refine (integrable_poly_mul_gaussCM hP ha
    (q := fun x => ((w ⬝ᵥ x : ℝ) : ℂ) * ((u ⬝ᵥ x : ℝ) : ℂ))
    ((continuous_ofReal_dot w).mul (continuous_ofReal_dot u)) (mul_nonneg
      (Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.sum_nonneg fun i _ => abs_nonneg _))
      (norm_dot_mul_dot_le u w)).congr (Eventually.of_forall fun x => ?_)
  ring

/-- **Hecke's identity for quadratic weights.**  With `W = P⁻¹P⁻ᵀ` (`= G⁻¹` for `G = PᵀP`),
`𝓕[Q_M e^{-π a |Px|²}](ξ) =
  (a⁻¹ (∑ᵢⱼ Wᵢⱼ Mᵢⱼ) / 2π - a⁻² Q_M(Wξ)) 𝓕[e^{-π a |Px|²}](ξ)`;
for harmonic `Q_M` (`∑ᵢⱼ Wᵢⱼ Mᵢⱼ = 0`) only the second term remains. -/
theorem fourierPi_qgaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ} (ha : 0 < a.re)
    (M : Matrix d d ℝ) (ξ : d → ℝ) :
    fourierPi (qgaussCM M P a) ξ =
      (a⁻¹ / (2 * π) * ((∑ j, ∑ k, ((P⁻¹)ᵀᵀ * (P⁻¹)ᵀ) j k * M j k : ℝ) : ℂ) -
        a⁻¹ ^ 2 * (qf M (((P⁻¹)ᵀᵀ * (P⁻¹)ᵀ) *ᵥ ξ) : ℂ)) * fourierPi (gaussCM P a) ξ := by
  have hsplit : (⇑(qgaussCM M P a)) = fun x => ∑ j,
      (((fun k => M j k) ⬝ᵥ x : ℝ) : ℂ) * (((Pi.single j 1 ⬝ᵥ x : ℝ) : ℂ) * gaussCM P a x) := by
    funext x
    rw [qgaussCM_apply, qf_eq_sum, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hTr : ∑ j, ((P⁻¹)ᵀ *ᵥ Pi.single j 1) ⬝ᵥ ((P⁻¹)ᵀ *ᵥ fun k => M j k) =
      ∑ j, ∑ k, ((P⁻¹)ᵀᵀ * (P⁻¹)ᵀ) j k * M j k := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dot_mulVec_mulVec, single_dotProduct, one_mul]
    rfl
  have hQr : ∑ j, (((P⁻¹)ᵀ *ᵥ Pi.single j 1) ⬝ᵥ ((P⁻¹)ᵀ *ᵥ ξ)) *
      (((P⁻¹)ᵀ *ᵥ fun k => M j k) ⬝ᵥ ((P⁻¹)ᵀ *ᵥ ξ)) = qf M (((P⁻¹)ᵀᵀ * (P⁻¹)ᵀ) *ᵥ ξ) := by
    simp only [dot_mulVec_mulVec, single_dotProduct, one_mul]
    rfl
  rw [hsplit, fourierPi_finset_sum _ _
    (fun j _ => integrable_dot_dot_mul_gaussCM hP ha (Pi.single j 1) (fun k => M j k))]
  simp_rw [fourierPi_dot_dot_mul_gaussCM hP ha]
  rw [← hTr, ← hQr, Complex.ofReal_sum, Complex.ofReal_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-! ## Decay of the weighted Gaussian and of its Fourier transform -/

omit [Fintype d] [DecidableEq d] in
theorem translatesSummable_of_le {f g : C(d → ℝ, ℂ)} (hg : TranslatesSummable g) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ x, ‖f x‖ ≤ C * ‖g x‖) : TranslatesSummable f := by
  intro K
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) ((hg K).mul_left C)
  refine (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg _))).2 fun y => ?_
  have h1 := ((g.comp (ContinuousMap.addRight (intVec m))).restrict
    (K : Set (d → ℝ))).norm_coe_le_norm y
  show ‖f ((y : d → ℝ) + intVec m)‖ ≤
    C * ‖(g.comp (ContinuousMap.addRight (intVec m))).restrict K‖
  exact (h _).trans (mul_le_mul_of_nonneg_left h1 hC)

theorem translatesSummable_qgaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ}
    (ha : 0 < a.re) (M : Matrix d d ℝ) : TranslatesSummable (qgaussCM M P a) := by
  obtain ⟨K, hK0, hK⟩ := exists_poly_gauss_bound hP ha
  have hb : 0 < ((a.re / 2 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    linarith
  have hMs : 0 ≤ ∑ i, ∑ j, |M i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine translatesSummable_of_le (translatesSummable_gaussCM hP hb) (mul_nonneg hMs hK0)
    fun x => ?_
  rw [qgaussCM_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |qf M x| * ‖gaussCM P a x‖
      ≤ (∑ i, ∑ j, |M i j|) * (1 + x ⬝ᵥ x) ^ 2 * ‖gaussCM P a x‖ :=
        mul_le_mul_of_nonneg_right (abs_qf_le M x) (norm_nonneg _)
    _ = (∑ i, ∑ j, |M i j|) * ((1 + x ⬝ᵥ x) ^ 2 * ‖gaussCM P a x‖) := by ring
    _ ≤ (∑ i, ∑ j, |M i j|) * (K * ‖gaussCM P ((a.re / 2 : ℝ) : ℂ) x‖) :=
        mul_le_mul_of_nonneg_left (hK x) hMs
    _ = _ := by ring

/-- Polynomially weighted Gaussians are absolutely summable over `ℤ^d`. -/
theorem summable_poly_mul_gaussCM_intVec {P : Matrix d d ℝ} (hP : P.det ≠ 0) {b : ℂ}
    (hb : 0 < b.re) {q : (d → ℝ) → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hqb : ∀ x, ‖q x‖ ≤ C * (1 + x ⬝ᵥ x) ^ 2) :
    Summable fun k : d → ℤ => ‖q (intVec k) * gaussCM P b (intVec k)‖ := by
  obtain ⟨K, hK0, hK⟩ := exists_poly_gauss_bound hP hb
  obtain ⟨u, hu, -, hbound⟩ := exists_summable_gauss_bound hP
    (mul_pos pi_pos (by linarith : 0 < b.re / 2)) 0
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hu.mul_left (C * K))
  have h1 : ‖gaussCM P ((b.re / 2 : ℝ) : ℂ) (intVec k)‖ ≤ u k := by
    have h0 := hbound k 0 (fun i => by simp)
    rw [zero_add] at h0
    rw [gaussCM_apply, norm_cexp_neg_pi_mul, Complex.ofReal_re]
    exact h0
  rw [norm_mul]
  calc ‖q (intVec k)‖ * ‖gaussCM P b (intVec k)‖
      ≤ C * (1 + intVec k ⬝ᵥ intVec k) ^ 2 * ‖gaussCM P b (intVec k)‖ :=
        mul_le_mul_of_nonneg_right (hqb _) (norm_nonneg _)
    _ = C * ((1 + intVec k ⬝ᵥ intVec k) ^ 2 * ‖gaussCM P b (intVec k)‖) := by ring
    _ ≤ C * (K * u k) :=
        mul_le_mul_of_nonneg_left ((hK _).trans (mul_le_mul_of_nonneg_left h1 hK0)) hC
    _ = C * K * u k := by ring

omit [DecidableEq d] in
/-- `|Q_M(Wξ)| ≤ C (1 + ξ·ξ)²`. -/
theorem abs_qf_mulVec_le (M W : Matrix d d ℝ) (ξ : d → ℝ) :
    |qf M (W *ᵥ ξ)| ≤ ((∑ i, ∑ j, |M i j|) * (1 + ∑ i, ∑ j, W i j ^ 2) ^ 2) *
      (1 + ξ ⬝ᵥ ξ) ^ 2 := by
  have hW : 0 ≤ ∑ i, ∑ j, W i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hX := dotProduct_self_nonneg' ξ
  have hMs : 0 ≤ ∑ i, ∑ j, |M i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have h1 : 1 + (W *ᵥ ξ) ⬝ᵥ (W *ᵥ ξ) ≤ (1 + ∑ i, ∑ j, W i j ^ 2) * (1 + ξ ⬝ᵥ ξ) := by
    have := dotProduct_mulVec_self_le W ξ
    nlinarith [mul_nonneg hW hX]
  refine (abs_qf_le M (W *ᵥ ξ)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hMs
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by linarith [dotProduct_self_nonneg' (W *ᵥ ξ)]) h1 2

theorem summable_fourierPi_qgaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ}
    (ha : 0 < a.re) (M : Matrix d d ℝ) :
    Summable fun k : d → ℤ => fourierPi (qgaussCM M P a) (intVec k) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hinv : 0 < (a⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos ha (Complex.normSq_pos.2 ha0)
  set W := (P⁻¹)ᵀᵀ * (P⁻¹)ᵀ
  set T : ℂ := a⁻¹ / (2 * π) * ((∑ j, ∑ k, W j k * M j k : ℝ) : ℂ)
  set C₀ : ℂ := ((|P.det|⁻¹ : ℝ) : ℂ) * (1 / a) ^ (Fintype.card d / 2 : ℂ)
  have hform : ∀ ξ, fourierPi (qgaussCM M P a) ξ =
      C₀ * ((T - a⁻¹ ^ 2 * (qf M (W *ᵥ ξ) : ℂ)) * gaussCM ((P⁻¹)ᵀ) a⁻¹ ξ) := by
    intro ξ
    rw [fourierPi_qgaussCM hP ha, fourierPi_gaussCM hP ha, gaussCM_apply]
    ring
  set Cq : ℝ := ‖T‖ + ‖a⁻¹ ^ 2‖ * ((∑ i, ∑ j, |M i j|) * (1 + ∑ i, ∑ j, W i j ^ 2) ^ 2)
  have hCq : 0 ≤ Cq := by
    have : 0 ≤ (∑ i, ∑ j, |M i j|) * (1 + ∑ i, ∑ j, W i j ^ 2) ^ 2 :=
      mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
        (sq_nonneg _)
    positivity
  have hqb : ∀ ξ : d → ℝ, ‖T - a⁻¹ ^ 2 * (qf M (W *ᵥ ξ) : ℂ)‖ ≤ Cq * (1 + ξ ⬝ᵥ ξ) ^ 2 := by
    intro ξ
    have hX : 1 ≤ (1 + ξ ⬝ᵥ ξ) ^ 2 := by nlinarith [dotProduct_self_nonneg' ξ]
    have h2 := abs_qf_mulVec_le M W ξ
    have e : ‖a⁻¹ ^ 2 * (qf M (W *ᵥ ξ) : ℂ)‖ = ‖a⁻¹ ^ 2‖ * |qf M (W *ᵥ ξ)| := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖T - a⁻¹ ^ 2 * (qf M (W *ᵥ ξ) : ℂ)‖ ≤ ‖T‖ + ‖a⁻¹ ^ 2 * (qf M (W *ᵥ ξ) : ℂ)‖ :=
          norm_sub_le _ _
      _ = ‖T‖ + ‖a⁻¹ ^ 2‖ * |qf M (W *ᵥ ξ)| := by rw [e]
      _ ≤ ‖T‖ * (1 + ξ ⬝ᵥ ξ) ^ 2 + ‖a⁻¹ ^ 2‖ * (((∑ i, ∑ j, |M i j|) *
            (1 + ∑ i, ∑ j, W i j ^ 2) ^ 2) * (1 + ξ ⬝ᵥ ξ) ^ 2) := by
          gcongr
          nlinarith [norm_nonneg T]
      _ = Cq * (1 + ξ ⬝ᵥ ξ) ^ 2 := by ring
  have hs := summable_poly_mul_gaussCM_intVec (det_inv_transpose_ne_zero hP) hinv hCq hqb
  refine (hs.of_norm.mul_left C₀).congr fun k => ?_
  rw [hform]

/-! ## Poisson summation with a harmonic quadratic weight -/

/-- **Weighted theta transformation.**  For `G` positive definite and `Q_M` harmonic for
`G` (`∑ᵢⱼ (G⁻¹)ᵢⱼ Mᵢⱼ = 0`), `Re a > 0` and `x ∈ ℝ^d`,
`∑_m Q_M(x+m) e^{-π a Q_G(x+m)} =
  -(det G)^{-1/2} a^{-d/2} a^{-2} ∑_k Q_M(G⁻¹k) e^{-π a⁻¹ Q_{G⁻¹}(k)} e(k·x)`. -/
theorem tsum_qf_exp_qf_poisson {G : Matrix d d ℝ} (hG : G.PosDef) (M : Matrix d d ℝ)
    (hM : ∑ i, ∑ j, G⁻¹ i j * M i j = 0) {a : ℂ} (ha : 0 < a.re) (x : d → ℝ) :
    ∑' m : d → ℤ, (qf M (x + intVec m) : ℂ) * cexp (-π * a * (qf G (x + intVec m) : ℂ)) =
      -((((Real.sqrt G.det)⁻¹ : ℝ) : ℂ) * (1 / a) ^ (Fintype.card d / 2 : ℂ) * a⁻¹ ^ 2) *
        ∑' k : d → ℤ, (qf M (G⁻¹ *ᵥ intVec k) : ℂ) *
          cexp (-π * a⁻¹ * (qf G⁻¹ (intVec k) : ℂ)) * eChar (intVec k ⬝ᵥ x) := by
  obtain ⟨P, rfl, hdet⟩ := exists_factor_of_posDef hG
  have hinv : (Pᵀ * P)⁻¹ = (P⁻¹)ᵀᵀ * (P⁻¹)ᵀ := by
    rw [Matrix.mul_inv_rev, ← transpose_nonsing_inv, transpose_transpose]
  have hsqrt : Real.sqrt (Pᵀ * P).det = |P.det| := by
    rw [det_mul, det_transpose, ← sq, Real.sqrt_sq_eq_abs]
  have h := tsum_eq_tsum_fourierPi (translatesSummable_qgaussCM hdet ha M)
    (summable_fourierPi_qgaussCM hdet ha M) x
  simp only [qgaussCM_apply, gaussCM_apply] at h
  rw [hinv] at hM
  rw [hinv, hsqrt]
  simp only [qf_transpose_mul_self]
  rw [h, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [fourierPi_qgaussCM hdet ha M, hM, fourierPi_gaussCM hdet ha]
  push_cast
  ring

/-- The theta series `Θ_{M,γ}(τ) = ∑_{m ∈ ℤ^d} Q_M(γ+m) exp(πiτ Q_G(γ+m))` of the coset
`γ + L` with the quadratic weight `Q_M`. -/
def latticeThetaQ (G M : Matrix d d ℝ) (γ : d → ℝ) (τ : ℂ) : ℂ :=
  ∑' m : d → ℤ, (qf M (γ + intVec m) : ℂ) * cexp (π * I * τ * (qf G (γ + intVec m) : ℂ))

omit [DecidableEq d] in
/-- `Θ_{M,γ}` depends only on the coset `γ + ℤ^d`. -/
theorem latticeThetaQ_add_intVec (G M : Matrix d d ℝ) (γ : d → ℝ) (n : d → ℤ) (τ : ℂ) :
    latticeThetaQ G M (γ + intVec n) τ = latticeThetaQ G M γ τ := by
  unfold latticeThetaQ
  conv_rhs => rw [← (Equiv.addLeft n).tsum_eq]
  refine tsum_congr fun m => ?_
  simp only [Equiv.coe_addLeft, intVec_add, add_assoc]

omit [DecidableEq d] in
/-- `Θ_{M,-γ} = Θ_{M,γ}`. -/
theorem latticeThetaQ_neg (G M : Matrix d d ℝ) (γ : d → ℝ) (τ : ℂ) :
    latticeThetaQ G M (-γ) τ = latticeThetaQ G M γ τ := by
  unfold latticeThetaQ
  rw [← (Equiv.neg (d → ℤ)).tsum_eq]
  refine tsum_congr fun m => ?_
  have h : -γ + intVec (Equiv.neg (d → ℤ) m) = -(γ + intVec m) := by
    rw [Equiv.neg_apply, intVec_neg, neg_add]
  rw [h, qf_neg, qf_neg]

/-- **`S`-transformation with a harmonic quadratic weight, Poisson form** (weight
`d/2 + 2`): `Θ_{M,γ}(-1/τ) = (det G)^{-1/2} (-iτ)^{d/2} τ²
  ∑_{k ∈ ℤ^d} Q_M(G⁻¹k) exp(πiτ Q_{G⁻¹}(k)) e(k·γ)`. -/
theorem latticeThetaQ_S_poisson {G : Matrix d d ℝ} (hG : G.PosDef) {M : Matrix d d ℝ}
    (hM : ∑ i, ∑ j, G⁻¹ i j * M i j = 0) (γ : d → ℝ) {τ : ℂ} (hτ : 0 < τ.im) :
    latticeThetaQ G M γ (-1 / τ) =
      (((Real.sqrt G.det)⁻¹ : ℝ) : ℂ) * (-I * τ) ^ (Fintype.card d / 2 : ℂ) * τ ^ 2 *
        ∑' k : d → ℤ, (qf M (G⁻¹ *ᵥ intVec k) : ℂ) *
          cexp (π * I * τ * (qf G⁻¹ (intVec k) : ℂ)) * eChar (intVec k ⬝ᵥ γ) := by
  have hτ0 : τ ≠ 0 := fun h => by simp [h] at hτ
  have ha : 0 < (I / τ).re := by
    rw [Complex.div_re, Complex.I_re, Complex.I_im, zero_mul, zero_div, zero_add, one_mul]
    exact div_pos hτ (Complex.normSq_pos.2 hτ0)
  have e2 : (I / τ)⁻¹ = -I * τ := by
    rw [inv_div, div_eq_mul_inv, Complex.inv_I]
    ring
  have h := tsum_qf_exp_qf_poisson hG M hM ha γ
  rw [one_div, e2] at h
  have hsq : (-I * τ) ^ 2 = -τ ^ 2 := by linear_combination τ ^ 2 * I_sq
  have hsum : ∑' k : d → ℤ, (qf M (G⁻¹ *ᵥ intVec k) : ℂ) *
      cexp (-π * (-I * τ) * (qf G⁻¹ (intVec k) : ℂ)) * eChar (intVec k ⬝ᵥ γ) =
      ∑' k : d → ℤ, (qf M (G⁻¹ *ᵥ intVec k) : ℂ) *
        cexp (π * I * τ * (qf G⁻¹ (intVec k) : ℂ)) * eChar (intVec k ⬝ᵥ γ) :=
    tsum_congr fun k => by
      congr 3
      ring
  rw [hsq, hsum] at h
  unfold latticeThetaQ
  calc ∑' m : d → ℤ, (qf M (γ + intVec m) : ℂ) *
        cexp (π * I * (-1 / τ) * (qf G (γ + intVec m) : ℂ))
      = ∑' m : d → ℤ, (qf M (γ + intVec m) : ℂ) *
          cexp (-π * (I / τ) * (qf G (γ + intVec m) : ℂ)) :=
        tsum_congr fun m => by
          congr 2
          ring
    _ = _ := h
    _ = _ := by ring

/-- The dual weighted series converges absolutely. -/
theorem summable_weighted_dual {G : Matrix d d ℝ} (hG : G.PosDef) (M : Matrix d d ℝ) {τ : ℂ}
    (hτ : 0 < τ.im) (γ : d → ℝ) :
    Summable fun k : d → ℤ => (qf M (G⁻¹ *ᵥ intVec k) : ℂ) *
      cexp (π * I * τ * (qf G⁻¹ (intVec k) : ℂ)) * eChar (intVec k ⬝ᵥ γ) := by
  obtain ⟨P'', hP''G, hdet''⟩ := exists_factor_of_posDef hG.inv
  have hb : 0 < (-I * τ).re := by rwa [re_neg_I_mul]
  have hC : 0 ≤ (∑ i, ∑ j, |M i j|) * (1 + ∑ i, ∑ j, G⁻¹ i j ^ 2) ^ 2 :=
    mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
      (sq_nonneg _)
  have hqb : ∀ ξ : d → ℝ, ‖((qf M (G⁻¹ *ᵥ ξ) : ℝ) : ℂ)‖ ≤
      ((∑ i, ∑ j, |M i j|) * (1 + ∑ i, ∑ j, G⁻¹ i j ^ 2) ^ 2) * (1 + ξ ⬝ᵥ ξ) ^ 2 := by
    intro ξ
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_qf_mulVec_le M G⁻¹ ξ
  have hgk : ∀ k : d → ℤ, gaussCM P'' (-I * τ) (intVec k) =
      cexp (π * I * τ * (qf G⁻¹ (intVec k) : ℂ)) := by
    intro k
    rw [gaussCM_apply, ← qf_transpose_mul_self, hP''G]
    congr 1
    ring
  refine (summable_poly_mul_gaussCM_intVec hdet'' hb hC hqb).of_norm_bounded fun k =>
    le_of_eq ?_
  rw [norm_mul, norm_eChar, mul_one, hgk]

/-- **`S`-transformation of the vector of weighted coset theta series** (weight `d/2 + 2`).
Hypotheses as in `latticeTheta_S`, plus harmonicity of `Q_M` for `G = gramR Gz`:
`Θ_{M,γ}(-1/τ) = (det G)^{-1/2} (-iτ)^{d/2} τ² ∑_{r ∈ R} e((γ, G⁻¹r)) Θ_{M,G⁻¹r}(τ)`. -/
theorem latticeThetaQ_S {Gz : Matrix d d ℤ} (hG : (gramR Gz).PosDef) {M : Matrix d d ℝ}
    (hM : ∑ i, ∑ j, (gramR Gz)⁻¹ i j * M i j = 0) (R : Finset (d → ℤ))
    (hR : ∀ k : d → ℤ, ∃! p : R × (d → ℤ), (p.1 : d → ℤ) + Gz *ᵥ p.2 = k)
    (s : d → ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    latticeThetaQ (gramR Gz) M ((gramR Gz)⁻¹ *ᵥ intVec s) (-1 / τ) =
      (((Real.sqrt (gramR Gz).det)⁻¹ : ℝ) : ℂ) * (-I * τ) ^ (Fintype.card d / 2 : ℂ) * τ ^ 2 *
        ∑ r ∈ R, eChar (intVec r ⬝ᵥ ((gramR Gz)⁻¹ *ᵥ intVec s)) *
          latticeThetaQ (gramR Gz) M ((gramR Gz)⁻¹ *ᵥ intVec r) τ := by
  set G := gramR Gz with hGdef
  set γ := G⁻¹ *ᵥ intVec s with hγ
  have hunit := isUnit_det_of_posDef hG
  have hGt := transpose_eq_of_posDef hG
  rw [latticeThetaQ_S_poisson hG hM γ hτ]
  congr 1
  have hFsum := summable_weighted_dual hG M hτ γ
  let e : R × (d → ℤ) ≃ (d → ℤ) :=
    Equiv.ofBijective (fun p => (p.1 : d → ℤ) + Gz *ᵥ p.2)
      ((Function.bijective_iff_existsUnique _).2 hR)
  have hFe : Summable fun p : R × (d → ℤ) => (qf M (G⁻¹ *ᵥ intVec (e p)) : ℂ) *
      cexp (π * I * τ * (qf G⁻¹ (intVec (e p)) : ℂ)) * eChar (intVec (e p) ⬝ᵥ γ) :=
    e.summable_iff.2 hFsum
  rw [← e.tsum_eq, hFe.tsum_prod, tsum_fintype, ← Finset.sum_coe_sort R]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [latticeThetaQ, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hv : intVec (e (r, m)) = intVec (r : d → ℤ) + G *ᵥ intVec m := by
    show intVec ((r : d → ℤ) + Gz *ᵥ m) = _
    rw [intVec_add, intVec_mulVec]
  have hw : G⁻¹ *ᵥ (intVec (r : d → ℤ) + G *ᵥ intVec m) = G⁻¹ *ᵥ intVec (r : d → ℤ) + intVec m := by
    rw [mulVec_add, mulVec_mulVec, nonsing_inv_mul G hunit, one_mulVec]
  rw [hv, hw, qf_inv_add_mulVec hunit, add_dotProduct, hγ, mulVec_dotProduct_inv_mulVec hGt hunit,
    intVec_dotProduct, eChar_add, eChar_intCast, mul_one]
  ring

/-- **`T`-transformation with a quadratic weight**: `Θ_{M,γ}(τ+1) = e(Q_G(γ)/2) Θ_{M,γ}(τ)`
for even integral `G` and `γ = G⁻¹ s ∈ L'`. -/
theorem latticeThetaQ_T {Gz : Matrix d d ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : d → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) (M : Matrix d d ℝ) (s : d → ℤ) (τ : ℂ) :
    latticeThetaQ (gramR Gz) M ((gramR Gz)⁻¹ *ᵥ intVec s) (τ + 1) =
      cexp (π * I * (qf (gramR Gz) ((gramR Gz)⁻¹ *ᵥ intVec s) : ℂ)) *
        latticeThetaQ (gramR Gz) M ((gramR Gz)⁻¹ *ᵥ intVec s) τ := by
  unfold latticeThetaQ
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rw [cexp_qf_add_one hG hEven s m τ]
  ring

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.hasDerivAt_fourierPi_mul_eChar
#print axioms HaagerupIzumi.C8.Theta.fourierPi_dot_mul_gaussCM
#print axioms HaagerupIzumi.C8.Theta.fourierPi_dot_dot_mul_gaussCM
#print axioms HaagerupIzumi.C8.Theta.fourierPi_qgaussCM
#print axioms HaagerupIzumi.C8.Theta.tsum_qf_exp_qf_poisson
#print axioms HaagerupIzumi.C8.Theta.latticeThetaQ_S_poisson
#print axioms HaagerupIzumi.C8.Theta.latticeThetaQ_S
#print axioms HaagerupIzumi.C8.Theta.latticeThetaQ_T
#print axioms HaagerupIzumi.C8.Theta.latticeThetaQ_add_intVec
#print axioms HaagerupIzumi.C8.Theta.latticeThetaQ_neg
