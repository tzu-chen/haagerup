module

public import HaagerupIzumi.C8.Theta.PoissonPi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# Poisson summation for Gaussians of a positive definite quadratic form

Second step of work item W6 (`C8/ROADMAP.md`; theta identities in the proof of Proposition
`prop:near-group-current-obstructions`, lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).  We apply the multi-dimensional Poisson
summation formula `tsum_eq_tsum_fourierPi` (file `PoissonPi`) to the Gaussians
`x ↦ exp(-π a Q_G(x))`, `Q_G(x) = x·Gx` (`qf`), for a real positive definite matrix `G` and a
complex parameter `a` with `Re a > 0`.

## Main results

* `fourierPi_gaussCM`: for an invertible real matrix `P`,
  `𝓕[exp(-π a |Px|²)](ξ) = |det P|⁻¹ a^{-d/2} exp(-π a⁻¹ |P⁻ᵀξ|²)`
  (linear change of variables `v = Px` and Mathlib's `GaussianFourier.integral_cexp_neg_mul_sum_add`).
* `tsum_gauss_poisson`: the resulting theta transformation for `|Px|²`.
* `tsum_exp_qf_poisson`: for `G` positive definite,
  `∑_{m ∈ ℤ^d} exp(-π a Q_G(x + m)) =
     (det G)^{-1/2} a^{-d/2} ∑_{k ∈ ℤ^d} exp(-π a⁻¹ Q_{G⁻¹}(k)) e(k·x)`.
  Here `a^{-d/2}` is `(1/a)^(d/2 : ℂ)` with the principal branch (`Re a > 0`).

The factorization `G = PᵀP` of a positive definite matrix is obtained from the continuous
functional calculus (`P = √G`, `exists_transpose_mul_self_eq_of_posDef`).  The decay estimates
use only that `P` is invertible (`exists_coercive`) and the one-dimensional Gaussian bound of
`Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable`.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Real Complex MeasureTheory Set TopologicalSpace Filter Matrix

namespace HaagerupIzumi.C8
namespace Theta

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Summability of products of one-dimensional sequences -/

omit [DecidableEq d] in
/-- If `g ≥ 0` is summable on `ℤ`, then `m ↦ ∏ᵢ g(mᵢ)` is summable on `ℤ^d`. -/
theorem summable_prod_pi {g : ℤ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) :
    Summable fun m : d → ℤ => ∏ i, g (m i) := by
  classical
  refine summable_of_sum_le (c := (∑' n, g n) ^ Fintype.card d)
    (fun m => Finset.prod_nonneg fun i _ => hg0 _) fun s => ?_
  let T : Finset ℤ := s.biUnion fun m => Finset.univ.image m
  have hsub : s ⊆ Fintype.piFinset fun _ => T := by
    intro m hm
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_biUnion.2 ⟨m, hm, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩
  calc ∑ m ∈ s, ∏ i, g (m i)
      ≤ ∑ m ∈ Fintype.piFinset (fun _ : d => T), ∏ i, g (m i) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ =>
          Finset.prod_nonneg fun i _ => hg0 _
    _ = ∏ _i : d, ∑ n ∈ T, g n := Finset.sum_prod_piFinset T fun _ n => g n
    _ ≤ ∏ _i : d, ∑' n, g n :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun n _ => hg0 n)
          fun i _ => hg.sum_le_tsum T fun n _ => hg0 n
    _ = (∑' n, g n) ^ Fintype.card d := by rw [Finset.prod_const, Finset.card_univ]

/-- `n ↦ exp(-α n²)` is summable on `ℤ` for `α > 0`. -/
theorem summable_exp_neg_mul_int_sq {α : ℝ} (hα : 0 < α) :
    Summable fun n : ℤ => rexp (-α * (n : ℝ) ^ 2) := by
  refine (summable_pow_mul_jacobiTheta₂_term_bound 0 (div_pos hα pi_pos) 0).congr fun n => ?_
  simp only [pow_zero, one_mul, mul_zero, zero_mul, sub_zero]
  congr 1
  field_simp

/-! ## Coercivity of `|Px|²` and a uniform Gaussian majorant -/

omit [DecidableEq d] in
/-- `|By|² ≤ (∑ᵢⱼ Bᵢⱼ²) |y|²` (Cauchy–Schwarz in each row). -/
theorem dotProduct_mulVec_self_le (B : Matrix d d ℝ) (y : d → ℝ) :
    (B *ᵥ y) ⬝ᵥ (B *ᵥ y) ≤ (∑ i, ∑ j, B i j ^ 2) * (y ⬝ᵥ y) := by
  have key : ∀ i, (B *ᵥ y) i * (B *ᵥ y) i ≤ (∑ j, B i j ^ 2) * (y ⬝ᵥ y) := by
    intro i
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => B i j) y
    have e1 : (B *ᵥ y) i = ∑ j, B i j * y j := rfl
    have e2 : y ⬝ᵥ y = ∑ j, y j ^ 2 := Finset.sum_congr rfl fun j _ => (sq _).symm
    rw [e1, e2, ← sq]
    exact h
  calc (B *ᵥ y) ⬝ᵥ (B *ᵥ y) = ∑ i, (B *ᵥ y) i * (B *ᵥ y) i := rfl
    _ ≤ ∑ i, (∑ j, B i j ^ 2) * (y ⬝ᵥ y) := Finset.sum_le_sum fun i _ => key i
    _ = (∑ i, ∑ j, B i j ^ 2) * (y ⬝ᵥ y) := (Finset.sum_mul ..).symm

/-- For invertible `P` there is `c > 0` with `c |x|² ≤ |Px|²`. -/
theorem exists_coercive {P : Matrix d d ℝ} (hP : P.det ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : d → ℝ, c * (x ⬝ᵥ x) ≤ (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
  set M : ℝ := ∑ i, ∑ j, P⁻¹ i j ^ 2
  have hM : 0 ≤ M := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  refine ⟨1 / (M + 1), by positivity, fun x => ?_⟩
  have hx : P⁻¹ *ᵥ (P *ᵥ x) = x := by
    rw [mulVec_mulVec, nonsing_inv_mul P (isUnit_iff_ne_zero.2 hP), one_mulVec]
  have h1 := dotProduct_mulVec_self_le P⁻¹ (P *ᵥ x)
  rw [hx] at h1
  have hyy : 0 ≤ (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

/-- `(a + b)² ≥ b²/2 - a²`. -/
theorem sq_add_ge (a b : ℝ) : b ^ 2 / 2 - a ^ 2 ≤ (a + b) ^ 2 := by
  nlinarith [sq_nonneg (b + 2 * a)]

/-- A summable majorant, uniform on bounded sets of shifts: for invertible `P`, `t > 0` and
`R`, there is a summable `u ≥ 0` on `ℤ^d` with `exp(-t |P(y + m)|²) ≤ u(m)` whenever all
`|yᵢ| ≤ R`. -/
theorem exists_summable_gauss_bound {P : Matrix d d ℝ} (hP : P.det ≠ 0) {t : ℝ} (ht : 0 < t)
    (R : ℝ) :
    ∃ u : (d → ℤ) → ℝ, Summable u ∧ (∀ m, 0 ≤ u m) ∧ ∀ (m : d → ℤ) (y : d → ℝ),
      (∀ i, |y i| ≤ R) →
        rexp (-t * ((P *ᵥ (y + intVec m)) ⬝ᵥ (P *ᵥ (y + intVec m)))) ≤ u m := by
  obtain ⟨c, hc, hcoer⟩ := exists_coercive hP
  have hs : 0 < t * c := mul_pos ht hc
  refine ⟨fun m => ∏ i, rexp (-(t * c) * ((m i : ℝ) ^ 2 / 2 - R ^ 2)), ?_,
    fun m => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le, ?_⟩
  · refine summable_prod_pi (g := fun n : ℤ => rexp (-(t * c) * ((n : ℝ) ^ 2 / 2 - R ^ 2)))
      (fun n => (Real.exp_pos _).le) ?_
    refine ((summable_exp_neg_mul_int_sq (half_pos hs)).mul_left (rexp (t * c * R ^ 2))).congr
      fun n => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  · intro m y hy
    dsimp only
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    have hQ := hcoer (y + intVec m)
    have h3 : ∑ i, ((m i : ℝ) ^ 2 / 2 - R ^ 2) ≤ (y + intVec m) ⬝ᵥ (y + intVec m) := by
      show ∑ i, ((m i : ℝ) ^ 2 / 2 - R ^ 2) ≤ ∑ i, (y + intVec m) i * (y + intVec m) i
      refine Finset.sum_le_sum fun i _ => ?_
      have hyi : y i ^ 2 ≤ R ^ 2 := sq_le_sq' (abs_le.1 (hy i)).1 (abs_le.1 (hy i)).2
      have h := sq_add_ge (y i) (m i : ℝ)
      simp only [Pi.add_apply, intVec_apply]
      nlinarith
    have h4 : ∑ i, -(t * c) * ((m i : ℝ) ^ 2 / 2 - R ^ 2) =
        -(t * c) * ∑ i, ((m i : ℝ) ^ 2 / 2 - R ^ 2) := by
      rw [Finset.mul_sum]
    rw [h4]
    nlinarith [mul_le_mul_of_nonneg_left hQ ht.le, mul_le_mul_of_nonneg_left h3 hs.le]

/-! ## The Gaussian `exp(-π a |Px|²)` -/

omit [DecidableEq d] in
theorem continuous_sqNorm (P : Matrix d d ℝ) :
    Continuous fun x : d → ℝ => (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
  have h : Continuous fun x : d → ℝ => P *ᵥ x := continuous_const.matrix_mulVec continuous_id
  exact h.dotProduct h

/-- The Gaussian `x ↦ exp(-π a |Px|²)` as a continuous map. -/
def gaussCM (P : Matrix d d ℝ) (a : ℂ) : C(d → ℝ, ℂ) :=
  ⟨fun x => cexp (-π * a * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x) : ℝ)),
    Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_sqNorm P)))⟩

omit [DecidableEq d] in
@[simp] theorem gaussCM_apply (P : Matrix d d ℝ) (a : ℂ) (x : d → ℝ) :
    gaussCM P a x = cexp (-π * a * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x) : ℝ)) := rfl

/-- `‖exp(-π a r)‖ = exp(-π (Re a) r)` for real `r`. -/
theorem norm_cexp_neg_pi_mul (a : ℂ) (r : ℝ) :
    ‖cexp (-π * a * (r : ℂ))‖ = rexp (-(π * a.re) * r) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.ofReal_im, neg_zero, zero_mul, mul_zero, sub_zero]
  ring

theorem translatesSummable_gaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ}
    (ha : 0 < a.re) : TranslatesSummable (gaussCM P a) := by
  intro K
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  obtain ⟨u, hu, hu0, hbound⟩ := exists_summable_gauss_bound hP (mul_pos pi_pos ha) R
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hu
  refine (ContinuousMap.norm_le _ (hu0 m)).2 fun y => ?_
  have hy : (y : d → ℝ) ∈ Metric.closedBall (0 : d → ℝ) R := hR y.2
  rw [mem_closedBall_zero_iff] at hy
  have hyi : ∀ i, |(y : d → ℝ) i| ≤ R := fun i =>
    (Real.norm_eq_abs ((y : d → ℝ) i) ▸ norm_le_pi_norm (y : d → ℝ) i).trans hy
  show ‖gaussCM P a ((y : d → ℝ) + intVec m)‖ ≤ u m
  rw [gaussCM_apply, norm_cexp_neg_pi_mul]
  exact hbound m y hyi

/-! ## The Fourier transform of the Gaussian -/

/-- `𝓕[exp(-π a |Px|²)](ξ) = |det P|⁻¹ a^{-d/2} exp(-π a⁻¹ |P⁻ᵀ ξ|²)`. -/
theorem fourierPi_gaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ} (ha : 0 < a.re)
    (ξ : d → ℝ) :
    fourierPi (gaussCM P a) ξ =
      ((|P.det|⁻¹ : ℝ) : ℂ) * (1 / a) ^ (Fintype.card d / 2 : ℂ) *
        cexp (-π * a⁻¹ * (((P⁻¹)ᵀ *ᵥ ξ) ⬝ᵥ ((P⁻¹)ᵀ *ᵥ ξ) : ℝ)) := by
  have hunit : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hpi0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 pi_ne_zero
  set η : d → ℝ := (P⁻¹)ᵀ *ᵥ ξ with hη
  let c : d → ℂ := fun i => -2 * π * I * (η i : ℂ)
  let h : (d → ℝ) → ℂ := fun v =>
    cexp (-(π * a) * ∑ i, (v i : ℂ) ^ 2 + ∑ i, c i * (v i : ℂ))
  have hcont_h : Continuous h := by fun_prop
  have hcomp : ∀ x : d → ℝ, eChar (-(x ⬝ᵥ ξ)) * gaussCM P a x = h (Matrix.toLin' P x) := by
    intro x
    have hdot : (P *ᵥ x) ⬝ᵥ η = x ⬝ᵥ ξ := by
      rw [hη, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, nonsing_inv_mul P hunit,
        one_mulVec]
    rw [gaussCM_apply, Matrix.toLin'_apply, eChar, ← Complex.exp_add, ← hdot]
    congr 1
    simp only [dotProduct, c]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib, mul_neg]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hL : LinearMap.det (Matrix.toLin' P) ≠ 0 := by rwa [LinearMap.det_toLin']
  have hb : 0 < ((π : ℂ) * a).re := by
    rw [Complex.re_ofReal_mul]
    exact mul_pos pi_pos ha
  have hsum : ∑ i, c i ^ 2 = -4 * (π : ℂ) ^ 2 * ((η ⬝ᵥ η : ℝ) : ℂ) := by
    simp only [dotProduct, c]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (4 * (π : ℂ) ^ 2 * (η i : ℂ) ^ 2) * I_sq
  calc fourierPi (gaussCM P a) ξ = ∫ x, h (Matrix.toLin' P x) := by
        unfold fourierPi
        exact integral_congr_ae (Eventually.of_forall hcomp)
    _ = ∫ v, h v ∂(Measure.map (Matrix.toLin' P) volume) :=
        (integral_map (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
          hcont_h.aestronglyMeasurable).symm
    _ = ((|P.det|⁻¹ : ℝ) : ℂ) * ∫ v, h v := by
        rw [Real.map_linearMap_volume_pi_eq_smul_volume_pi hL, integral_smul_measure,
          LinearMap.det_toLin', ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, Complex.real_smul]
    _ = ((|P.det|⁻¹ : ℝ) : ℂ) * ((π / (π * a)) ^ (Fintype.card d / 2 : ℂ) *
          cexp ((∑ i, c i ^ 2) / (4 * (π * a)))) := by
        rw [GaussianFourier.integral_cexp_neg_mul_sum_add hb c]
    _ = _ := by
        have e1 : (π : ℂ) / (π * a) = 1 / a := by
          rw [div_mul_eq_div_div, div_self hpi0]
        have e2 : -4 * (π : ℂ) ^ 2 * ((η ⬝ᵥ η : ℝ) : ℂ) / (4 * (π * a)) =
            -π * a⁻¹ * ((η ⬝ᵥ η : ℝ) : ℂ) := by
          field_simp
        rw [hsum, e1, e2]
        ring

theorem det_inv_transpose_ne_zero {P : Matrix d d ℝ} (hP : P.det ≠ 0) : (P⁻¹)ᵀ.det ≠ 0 := by
  rw [det_transpose]
  exact (isUnit_nonsing_inv_det P (isUnit_iff_ne_zero.2 hP)).ne_zero

theorem summable_fourierPi_gaussCM {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ}
    (ha : 0 < a.re) : Summable fun k : d → ℤ => fourierPi (gaussCM P a) (intVec k) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hinv : 0 < (a⁻¹).re := by
    rw [Complex.inv_re]
    exact div_pos ha (Complex.normSq_pos.2 ha0)
  obtain ⟨u, hu, -, hbound⟩ :=
    exists_summable_gauss_bound (det_inv_transpose_ne_zero hP) (mul_pos pi_pos hinv) 0
  simp_rw [fourierPi_gaussCM hP ha]
  refine Summable.mul_left _ (hu.of_norm_bounded fun k => ?_)
  rw [norm_cexp_neg_pi_mul]
  have := hbound k 0 (fun i => by simp)
  rwa [zero_add] at this

/-! ## Poisson summation for Gaussians -/

/-- **Theta transformation for `|Px|²`.**  For invertible `P`, `Re a > 0` and `x ∈ ℝ^d`,
`∑_{m ∈ ℤ^d} exp(-π a |P(x+m)|²) =
  |det P|⁻¹ a^{-d/2} ∑_{k ∈ ℤ^d} exp(-π a⁻¹ |P⁻ᵀk|²) e(k·x)`. -/
theorem tsum_gauss_poisson {P : Matrix d d ℝ} (hP : P.det ≠ 0) {a : ℂ} (ha : 0 < a.re)
    (x : d → ℝ) :
    ∑' m : d → ℤ, cexp (-π * a * ((P *ᵥ (x + intVec m)) ⬝ᵥ (P *ᵥ (x + intVec m)) : ℝ)) =
      ((|P.det|⁻¹ : ℝ) : ℂ) * (1 / a) ^ (Fintype.card d / 2 : ℂ) *
        ∑' k : d → ℤ, cexp (-π * a⁻¹ *
          (((P⁻¹)ᵀ *ᵥ intVec k) ⬝ᵥ ((P⁻¹)ᵀ *ᵥ intVec k) : ℝ)) * eChar (intVec k ⬝ᵥ x) := by
  have h := tsum_eq_tsum_fourierPi (translatesSummable_gaussCM hP ha)
    (summable_fourierPi_gaussCM hP ha) x
  simp only [gaussCM_apply] at h
  rw [h, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [fourierPi_gaussCM hP ha]
  ring

/-! ## The form `Q_G(x) = x·Gx` of a positive definite matrix -/

/-- The quadratic form `Q_G(x) = x·Gx`. -/
def qf (G : Matrix d d ℝ) (x : d → ℝ) : ℝ := x ⬝ᵥ (G *ᵥ x)

omit [DecidableEq d] in
theorem qf_transpose_mul_self (P : Matrix d d ℝ) (x : d → ℝ) :
    qf (Pᵀ * P) x = (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
  rw [qf, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

open scoped MatrixOrder in
/-- A positive definite real matrix is `PᵀP` (take `P = √G`). -/
theorem exists_transpose_mul_self_eq_of_posDef {G : Matrix d d ℝ} (hG : G.PosDef) :
    ∃ P : Matrix d d ℝ, Pᵀ * P = G := by
  have h0 : 0 ≤ G := hG.posSemidef.nonneg
  refine ⟨CFC.sqrt G, ?_⟩
  have hsa : IsSelfAdjoint (CFC.sqrt G) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg G)
  have ht : (CFC.sqrt G)ᵀ = CFC.sqrt G := by
    have h := hsa.star_eq
    rwa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] at h
  rw [ht, CFC.sqrt_mul_sqrt_self G h0]

/-- **Theta transformation for a positive definite form.**  For `G` positive definite,
`Re a > 0` and `x ∈ ℝ^d`,
`∑_{m ∈ ℤ^d} exp(-π a Q_G(x+m)) =
  (det G)^{-1/2} a^{-d/2} ∑_{k ∈ ℤ^d} exp(-π a⁻¹ Q_{G⁻¹}(k)) e(k·x)`. -/
theorem tsum_exp_qf_poisson {G : Matrix d d ℝ} (hG : G.PosDef) {a : ℂ} (ha : 0 < a.re)
    (x : d → ℝ) :
    ∑' m : d → ℤ, cexp (-π * a * (qf G (x + intVec m) : ℂ)) =
      (((Real.sqrt G.det)⁻¹ : ℝ) : ℂ) * (1 / a) ^ (Fintype.card d / 2 : ℂ) *
        ∑' k : d → ℤ, cexp (-π * a⁻¹ * (qf G⁻¹ (intVec k) : ℂ)) * eChar (intVec k ⬝ᵥ x) := by
  obtain ⟨P, rfl⟩ := exists_transpose_mul_self_eq_of_posDef hG
  have hpos := hG.det_pos
  rw [det_mul, det_transpose] at hpos
  have hdet : P.det ≠ 0 := fun h => by rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
  have hinv : (Pᵀ * P)⁻¹ = ((P⁻¹)ᵀ)ᵀ * (P⁻¹)ᵀ := by
    rw [Matrix.mul_inv_rev, ← transpose_nonsing_inv, transpose_transpose]
  have hsqrt : Real.sqrt (Pᵀ * P).det = |P.det| := by
    rw [det_mul, det_transpose, ← sq, Real.sqrt_sq_eq_abs]
  simp only [hinv, qf_transpose_mul_self, hsqrt]
  exact tsum_gauss_poisson hdet ha x

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.fourierPi_gaussCM
#print axioms HaagerupIzumi.C8.Theta.tsum_gauss_poisson
#print axioms HaagerupIzumi.C8.Theta.exists_transpose_mul_self_eq_of_posDef
#print axioms HaagerupIzumi.C8.Theta.tsum_exp_qf_poisson
