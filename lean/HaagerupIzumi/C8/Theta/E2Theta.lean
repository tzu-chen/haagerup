module

public import HaagerupIzumi.C8.Theta.SerreQExp
public import HaagerupIzumi.C8.Theta.PolarParts
public import HaagerupIzumi.C8.Theta.CoeffExtraction

@[expose] public section

/-!
# The `q`-expansion of `F = -6 D₂ Θ`

W6 plan item 3, the `F` orientations (`Theta/W6_PLAN.md`): the coefficients of
`F = -6 D₂ Θ_{g+L}` are `minusSixD2Coeff (thetaCount G g)` (`Theta/Basic`), the numbers used in
Tables 2 and 4 (lines 3690–3705, 3756–3761 of `c8_expanded_20260929/haagerup_c8_expanded.tex`).

* `thetaCoeff_support_fract`: the coefficients of `g + L` (`γ = G⁻¹ s ∈ L'`, `L` even) are
  supported on `frac q(γ) + ℕ`;
* `summable_norm_thetaCount`: absolute convergence of `∑ N(e) q^e` at every height;
* `hasSum_E2`: Mathlib's `E₂ = 1 - 24 ∑ σ₁(n) qⁿ` with the coefficients `e2Coeff`;
* `E2_mul_theta_hasSum`: the Cauchy product `E₂ Θ = ∑_e (∑_{0 ≤ j ≤ e} E₂[j] N(e - j)) q^e`;
* `minusSixSerre_theta_qexp`: **`-6 ∂₂Θ_{g+L} = ∑_e minusSixD2Coeff N e · q^e`**.

Nothing here is an external hypothesis; everything is proved.
-/

noncomputable section

open Complex Matrix
open UpperHalfPlane hiding I
open scoped Real

namespace HaagerupIzumi.C8
namespace Theta

/-- Support on `frac q(γ) + ℕ`. -/
theorem thetaCoeff_support_fract {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) {g : Fin 4 → ℚ} {s : Fin 4 → ℤ}
    (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) {H : (Fin 4 → ℚ) → ℚ} {e : ℚ}
    (h : thetaCoeff Gz g H e ≠ 0) : ∃ n : ℕ, e = (n : ℚ) + Int.fract (energy Gz g) := by
  obtain ⟨k, hk⟩ := thetaCoeff_support hG hEven hg h
  have he0 := nonneg_of_thetaCoeff_ne_zero hG h
  have hf1 := Int.fract_lt_one (energy Gz g)
  have hm : e - Int.fract (energy Gz g) = ((k + ⌊energy Gz g⌋ : ℤ) : ℚ) := by
    rw [hk, ← Int.self_sub_floor]
    push_cast
    ring
  have hge : (-1 : ℚ) < ((k + ⌊energy Gz g⌋ : ℤ) : ℚ) := by rw [← hm]; linarith
  have hge' : -1 < k + ⌊energy Gz g⌋ := by exact_mod_cast hge
  have hge'' : 0 ≤ k + ⌊energy Gz g⌋ := by omega
  refine ⟨(k + ⌊energy Gz g⌋).toNat, ?_⟩
  have hc : (((k + ⌊energy Gz g⌋).toNat : ℕ) : ℚ) = ((k + ⌊energy Gz g⌋ : ℤ) : ℚ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hge'']
  rw [hc]
  linarith

/-- Absolute convergence of the unweighted coefficients at every height. -/
theorem summable_norm_thetaCount {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (g : Fin 4 → ℚ) {y : ℝ} (hy : 0 < y) :
    Summable fun e : ℚ => ‖((thetaCount Gz g e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y) := by
  have hτ : 0 < ((y : ℂ) * I).im := by simpa using hy
  have hs : Summable fun m : Fin 4 → ℤ =>
      ‖cexp (2 * π * I * ((energy Gz (cosetPt g m) : ℚ) : ℂ) * ((y : ℂ) * I))‖ := by
    refine (summable_norm_latticeTheta hG (ratVec g) hτ).congr fun m => ?_
    rw [← ratVec_cosetPt, qf_gramR_ratVec_eq_energy]
    push_cast
    congr 2
    ring
  have hfib := hs.hasSum.tsum_fiberwise fun m => energy Gz (cosetPt g m)
  refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_) hfib.summable
  show _ ≤ ∑' b : shell Gz g e,
      ‖cexp (2 * π * I * ((energy Gz (cosetPt g b) : ℚ) : ℂ) * ((y : ℂ) * I))‖
  have hE : ∀ b : shell Gz g e,
      ‖cexp (2 * π * I * ((energy Gz (cosetPt g b) : ℚ) : ℂ) * ((y : ℂ) * I))‖ =
        |(((fun _ => (1 : ℚ)) b : ℚ) : ℝ)| * Real.exp (-2 * π * (e : ℝ) * y) := by
    intro b
    have hre : 2 * (π : ℂ) * I * ((e : ℚ) : ℂ) * ((y : ℂ) * I) =
        ((-2 * π * ((e : ℚ) : ℝ) * y : ℝ) : ℂ) := by
      push_cast
      linear_combination (2 * (π : ℂ) * (e : ℂ) * (y : ℂ)) * I_sq
    rw [show energy Gz (cosetPt g b) = e from b.2, hre, Complex.norm_exp_ofReal]
    simp
  rw [tsum_congr hE, tsum_mul_right]
  exact mul_le_mul_of_nonneg_right
    (norm_finsum_le_tsum_norm (shell_finite hG g e) (fun _ => (1 : ℚ))) (Real.exp_pos _).le

/-- Mathlib's `q`-expansion of `E₂` with the coefficients `e2Coeff` of `Theta/Basic`. -/
theorem hasSum_E2 (z : ℍ) :
    HasSum (fun n : ℕ => ((e2Coeff n : ℚ) : ℂ) * cexp (2 * π * I * (n : ℂ) * z))
      (EisensteinSeries.E2 z) := by
  have h := EisensteinSeries.hasSum_qExpansion_E2 z
  convert h using 1
  funext n
  rw [smul_eq_mul, ← Complex.exp_nat_mul]
  congr 1
  · by_cases hn : n = 0
    · simp [e2Coeff, hn]
    · simp [e2Coeff, hn, ArithmeticFunction.sigma_apply]
  · ring_nf

theorem norm_e2Coeff_le (n : ℕ) : ‖((e2Coeff n : ℚ) : ℂ)‖ ≤ 24 * (n : ℝ) ^ 2 + 1 := by
  by_cases hn : n = 0
  · simp [e2Coeff, hn]
  · have hs : ((∑ d ∈ n.divisors, (d : ℚ)) : ℚ) = ((ArithmeticFunction.sigma 1 n : ℕ) : ℚ) := by
      simp [ArithmeticFunction.sigma_apply]
    have hle : (ArithmeticFunction.sigma 1 n : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast ArithmeticFunction.sigma_le_pow_succ 1 n
    rw [e2Coeff, if_neg hn, Complex.norm_ratCast, hs]
    push_cast
    rw [abs_mul, abs_neg]
    norm_num
    linarith

theorem summable_norm_E2_terms (z : ℍ) :
    Summable fun n : ℕ => ‖((e2Coeff n : ℚ) : ℂ) * cexp (2 * π * I * (n : ℂ) * z)‖ := by
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  have h1 := summable_norm_pow_mul_geometric_of_norm_lt_one 2 hq
  have h2 := summable_norm_pow_mul_geometric_of_norm_lt_one 0 hq
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((h1.mul_left 24).add h2)
  have hexp : cexp (2 * π * I * (n : ℂ) * z) = cexp (2 * π * I * z) ^ n := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  have hr := norm_nonneg (cexp (2 * π * I * z))
  calc ‖((e2Coeff n : ℚ) : ℂ) * cexp (2 * π * I * (n : ℂ) * z)‖
      = ‖((e2Coeff n : ℚ) : ℂ)‖ * ‖cexp (2 * π * I * z)‖ ^ n := by rw [hexp, norm_mul, norm_pow]
    _ ≤ (24 * (n : ℝ) ^ 2 + 1) * ‖cexp (2 * π * I * z)‖ ^ n :=
        mul_le_mul_of_nonneg_right (norm_e2Coeff_le n) (pow_nonneg hr n)
    _ = 24 * ‖(n : ℂ) ^ 2 * cexp (2 * π * I * z) ^ n‖ +
        ‖(n : ℂ) ^ 0 * cexp (2 * π * I * z) ^ n‖ := by
        simp only [norm_mul, norm_pow, Complex.norm_natCast, pow_zero, one_mul]
        ring

/-- **The Cauchy product** `E₂ Θ_{g+L} = ∑_e (∑_{0 ≤ j ≤ e} E₂[j] N(e - j)) q^e`, as a `HasSum`. -/
theorem E2_mul_theta_hasSum {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) {g : Fin 4 → ℚ} {s : Fin 4 → ℤ}
    (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) (z : ℍ) :
    HasSum (fun x : ℚ =>
      ((∑ j ∈ Finset.range (⌊x⌋₊ + 1), e2Coeff j * thetaCount Gz g (x - j) : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * z))
      (EisensteinSeries.E2 z * latticeTheta (gramR Gz) (ratVec g) z) := by
  set lam := Int.fract (energy Gz g) with hlam
  have hlam0 : 0 ≤ lam := Int.fract_nonneg _
  have hlam1 : lam < 1 := Int.fract_lt_one _
  have hsupp : ∀ x, thetaCount Gz g x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lam :=
    fun x hx => thetaCoeff_support_fract hG hEven hg hx
  have hinj : Function.Injective fun n : ℕ => (n : ℚ) + lam := fun a b h => by simpa using h
  -- `Θ` as an `ℕ`-indexed series
  have hΘ : latticeTheta (gramR Gz) (ratVec g) z = ∑' n : ℕ,
      ((thetaCount Gz g ((n : ℚ) + lam) : ℚ) : ℂ) *
        cexp (2 * π * I * ((((n : ℚ) + lam : ℚ)) : ℂ) * z) := by
    rw [latticeTheta_eq_tsum_thetaCount hG g z.im_pos]
    refine (hinj.tsum_eq (f := fun x : ℚ => ((thetaCount Gz g x : ℚ) : ℂ) *
      cexp (2 * π * I * (x : ℂ) * z)) fun x hx => ?_).symm
    have hx' : thetaCount Gz g x ≠ 0 := fun h0 => hx (by simp [h0])
    obtain ⟨n, hn⟩ := hsupp x hx'
    exact ⟨n, hn.symm⟩
  have hb : Summable fun n : ℕ => ‖((thetaCount Gz g ((n : ℚ) + lam) : ℚ) : ℂ) *
      cexp (2 * π * I * ((((n : ℚ) + lam : ℚ)) : ℂ) * z)‖ := by
    refine ((summable_norm_thetaCount hG g z.im_pos).comp_injective hinj).congr fun n => ?_
    simp only [Function.comp_apply]
    rw [norm_qterm_rat]
  have hprod : HasSum (fun k : ℕ => ∑ kl ∈ Finset.antidiagonal k,
      ((e2Coeff kl.1 : ℚ) : ℂ) * cexp (2 * π * I * (kl.1 : ℂ) * z) *
        (((thetaCount Gz g ((kl.2 : ℚ) + lam) : ℚ) : ℂ) *
          cexp (2 * π * I * ((((kl.2 : ℚ) + lam : ℚ)) : ℂ) * z)))
      (EisensteinSeries.E2 z * latticeTheta (gramR Gz) (ratVec g) z) := by
    have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm (summable_norm_E2_terms z)
      hb).of_norm
    rw [← (hasSum_E2 z).tsum_eq, hΘ,
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_E2_terms z) hb]
    exact hs.hasSum
  have hcsupp : ∀ x : ℚ, x ∉ Set.range (fun n : ℕ => (n : ℚ) + lam) →
      ((∑ j ∈ Finset.range (⌊x⌋₊ + 1), e2Coeff j * thetaCount Gz g (x - j) : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * z) = 0 := by
    intro x hx
    have hsum0 : (∑ j ∈ Finset.range (⌊x⌋₊ + 1), e2Coeff j * thetaCount Gz g (x - j)) = 0 := by
      by_contra hne
      obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
      have hj' : thetaCount Gz g (x - j) ≠ 0 := fun h0 => hj (by rw [h0, mul_zero])
      obtain ⟨n, hn⟩ := hsupp _ hj'
      exact hx ⟨n + j, by push_cast; linarith⟩
    rw [hsum0, Rat.cast_zero, zero_mul]
  rw [← hinj.hasSum_iff hcsupp]
  convert hprod using 1
  funext k
  have hfloor : ⌊((k : ℚ) + lam)⌋₊ = k := by
    rw [Nat.floor_eq_iff (by positivity)]
    constructor <;> linarith
  simp only [Function.comp_apply]
  rw [hfloor, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Rat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have harg : (((k - i : ℕ) : ℚ) + lam) = (k : ℚ) + lam - i := by
    rw [Nat.cast_sub hik]
    ring
  simp only []
  rw [harg]
  have hexp : cexp (2 * π * I * ((i : ℕ) : ℂ) * z) *
      cexp (2 * π * I * ((((k : ℚ) + lam - i : ℚ)) : ℂ) * z) =
        cexp (2 * π * I * ((((k : ℚ) + lam : ℚ)) : ℂ) * z) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hexp]
  push_cast
  ring

/-- **The `q`-expansion of `F = -6 ∂₂ Θ_{g+L}`**: its coefficients are
`minusSixD2Coeff (thetaCount G g)` (`Theta/Basic`, Tables 2 and 4). -/
theorem minusSixSerre_theta_qexp {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) {g : Fin 4 → ℚ} {s : Fin 4 → ℤ}
    (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) (z : ℍ) :
    -6 * Derivative.serreDerivative 2 (fun τ : ℍ => latticeTheta (gramR Gz) (ratVec g) τ) z =
      ∑' x : ℚ, ((minusSixD2Coeff (thetaCount Gz g) x : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * z) := by
  have hE := E2_mul_theta_hasSum hG hEven hg z
  have s1 : Summable fun x : ℚ => ((x * thetaCount Gz g x : ℚ) : ℂ) *
      cexp (2 * π * I * (x : ℂ) * z) := by
    refine summable_qseries_rat (b := fun x : ℚ => ((x * thetaCount Gz g x : ℚ) : ℂ))
      (fun y hy => ?_) z
    have hw := summable_norm_thetaCoeff hG (Gz.map (Int.cast : ℤ → ℚ)) g hy
    refine (hw.mul_left (1 / 2)).congr fun x => ?_
    rw [thetaCoeff_quadOf_gram]
    have h2 : ((2 * x * thetaCount Gz g x : ℚ) : ℂ) = 2 * ((x * thetaCount Gz g x : ℚ) : ℂ) := by
      push_cast
      ring
    rw [h2, norm_mul]
    norm_num
    ring
  rw [minusSix_serre_eq, normDeriv_theta_qexp hG g z, ← hE.tsum_eq, ← tsum_mul_left,
    ← (s1.mul_left (-6)).tsum_add hE.summable]
  refine tsum_congr fun x => ?_
  rw [minusSixD2Coeff]
  push_cast
  ring

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_support_fract
#print axioms HaagerupIzumi.C8.Theta.summable_norm_thetaCount
#print axioms HaagerupIzumi.C8.Theta.hasSum_E2
#print axioms HaagerupIzumi.C8.Theta.E2_mul_theta_hasSum
#print axioms HaagerupIzumi.C8.Theta.minusSixSerre_theta_qexp
