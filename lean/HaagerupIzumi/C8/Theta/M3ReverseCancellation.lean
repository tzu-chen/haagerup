module

public import HaagerupIzumi.C8.Theta.M6ReverseCancellation

@[expose] public section

/-!
# `m = 3`, reverse orientation: `dim U₁ = 14 + 42A` from pole cancellation

W6 plan items 1–4 assembled for Table 2 (`G₇⁻`, lines 3682–3712 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).  The theta side is `φ F + κ Θ_H` with
`F = -6 D₂ Θ`, `φ = 1`, `κ = (3 + 14A)/4` (line 3708), on the separately even block: the
coordinate `(r, s)`, `0 ≤ r ≤ 3`, `0 ≤ s ≤ 1`, is the label `j = 9r + 7s mod 21`, and every
theta vector is replaced by its average over the discriminant-form isometry `j ↦ 13j`
(`r ↦ -r`), which together with `j ↦ -j` gives the projection used by Table 2.

* theta side (proved): `GG7m φ κ` is holomorphic, `σ`-covariant for `σ(S) = SθEG7m`,
  `σ(T) = TθEG7m`; its `q`-coefficients are the averages `FcEG7m`, `HcEG7m`; its complete polar
  part is the vacuum entry and the orbit `{4, 10, 11, 17}` of `(2,1)` at `q^{2/21}`
  (`polar_G7m`); there `F` has `(3/7 · 1 + 3/7 · 0)/2 = 3/14` and `Θ_H` has
  `(-4/7 + 0)/2 = -2/7` (the separately even projection halves the coefficient, line 3705);
* VOA side (named hypotheses, as for Table 1): `σ` (`σ(S)`, `σ(T)`; finite image), the vector
  `V = v` (holomorphic, covariant), its `η⁸` `q`-expansion `δc` (support, convergence), polar
  data `δc (0,0) 0 = 1`, `δc (2,1) (2/21) = -A`, no other polar coefficient, and
  `δc (0,0) 1 = 2 dim U₁ - 94`.

Conclusion: `dim U₁ = 14 + 42A` (`m3_reverse_dimension_of_voa`).
-/

noncomputable section

open Complex Matrix ModularGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups Real Manifold

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Generic facts -/

theorem support_minusSix {Gz : Matrix (Fin 4) (Fin 4) ℤ} (hG : (gramR Gz).PosDef)
    (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m))) {g : Fin 4 → ℚ} {s : Fin 4 → ℤ}
    (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s) (x : ℚ)
    (h : minusSixD2Coeff (thetaCount Gz g) x ≠ 0) : ∃ n : ℕ, x = (n : ℚ) + lamOf Gz g := by
  have hs : ∀ y, thetaCount Gz g y ≠ 0 → ∃ n : ℕ, y = (n : ℚ) + lamOf Gz g := fun y hy =>
    thetaCoeff_support_nat hG hEven hg _ (lamOf_nonpos _ _) (lamOf_congr _ _) (fun _ => 1) y hy
  rw [minusSixD2Coeff] at h
  by_cases h1 : thetaCount Gz g x = 0
  · rw [h1, mul_zero, zero_add] at h
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hj' : thetaCount Gz g (x - j) ≠ 0 := fun h0 => hj (by rw [h0, mul_zero])
    obtain ⟨n, hn⟩ := hs (x - j) hj'
    exact ⟨n + j, by push_cast; linarith⟩
  · exact hs x h1

/-- `∑ a q^x` and `∑ b q^x` averaged. -/
theorem half_add_qseries (a b : ℚ → ℚ)
    (ha : ∀ y : ℝ, 0 < y →
      Summable fun e : ℚ => ‖((a e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hb : ∀ y : ℝ, 0 < y →
      Summable fun e : ℚ => ‖((b e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y)) (τ : ℍ) :
    (1 / 2 : ℂ) * (∑' x : ℚ, ((a x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ) +
      ∑' x : ℚ, ((b x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ)) =
      ∑' x : ℚ, (((a x + b x) / 2 : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ) := by
  rw [← (summable_qseries_rat ha τ).tsum_add (summable_qseries_rat hb τ), ← tsum_mul_left]
  refine tsum_congr fun x => ?_
  push_cast
  ring

theorem summable_half_add (a b : ℚ → ℚ) {y : ℝ}
    (ha : Summable fun e : ℚ => ‖((a e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hb : Summable fun e : ℚ => ‖((b e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y)) :
    Summable fun e : ℚ => ‖((((a e + b e) / 2 : ℚ)) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y) := by
  refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_) (ha.add hb)
  have hn : ‖((((a e + b e) / 2 : ℚ)) : ℂ)‖ ≤ ‖((a e : ℚ) : ℂ)‖ + ‖((b e : ℚ) : ℂ)‖ := by
    have h : ((((a e + b e) / 2 : ℚ)) : ℂ) = (1 / 2 : ℂ) * (((a e : ℚ) : ℂ) + ((b e : ℚ) : ℂ)) := by
      push_cast
      ring
    rw [h, norm_mul]
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h2]
    have := norm_add_le ((a e : ℚ) : ℂ) ((b e : ℚ) : ℂ)
    have h0 := norm_nonneg (((a e : ℚ) : ℂ) + ((b e : ℚ) : ℂ))
    linarith [norm_nonneg ((a e : ℚ) : ℂ), norm_nonneg ((b e : ℚ) : ℂ)]
  have hE := (Real.exp_pos (-2 * π * (e : ℝ) * y)).le
  calc ‖((((a e + b e) / 2 : ℚ)) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y)
      ≤ (‖((a e : ℚ) : ℂ)‖ + ‖((b e : ℚ) : ℂ)‖) * Real.exp (-2 * π * (e : ℝ) * y) :=
        mul_le_mul_of_nonneg_right hn hE
    _ = _ := by ring

/-! ## `G₇⁻`: translates and the `O(D)`-twisted `F` -/

theorem thetaCoeff_repG7m_congr {t t' : ℤ} (hmod : modG7m t = modG7m t')
    (hlam : lamOf gramG7m (repG7m t) = lamOf gramG7m (repG7m t'))
    (M : Matrix (Fin 4) (Fin 4) ℚ) (x : ℚ) :
    thetaCoeff gramG7m (repG7m t) (quadOf M) x = thetaCoeff gramG7m (repG7m t') (quadOf M) x := by
  have key := qcoeff_eq_lincomb (lamOf gramG7m (repG7m t'))
    (thetaCoeff gramG7m (repG7m t) (quadOf M)) (thetaCoeff gramG7m (repG7m t') (quadOf M))
    (fun _ => 0) 1 0
    (fun x hx => hlam ▸ thetaCoeff_support_nat posDef_G7m even_G7m (ratVec_repG7m_eq_inv t) _
      (lamOf_nonpos _ _) (lamOf_congr _ _) _ x hx)
    (fun x hx => thetaCoeff_support_nat posDef_G7m even_G7m (ratVec_repG7m_eq_inv t') _
      (lamOf_nonpos _ _) (lamOf_congr _ _) _ x hx)
    (fun e he => absurd rfl he)
    (fun y hy => summable_norm_thetaCoeff posDef_G7m M _ hy)
    (fun y hy => summable_norm_thetaCoeff posDef_G7m M _ hy) (fun _ _ => by simp)
    (fun τ => by
      rw [← latticeThetaQ_eq_tsum_thetaCoeff posDef_G7m M _ τ.im_pos,
        ← latticeThetaQ_eq_tsum_thetaCoeff posDef_G7m M _ τ.im_pos, latticeThetaQ_repG7m,
        latticeThetaQ_repG7m, hmod]
      simp) x
  rw [key]
  ring

theorem thetaCount_repG7m_congr {t t' : ℤ} (hmod : modG7m t = modG7m t')
    (hlam : lamOf gramG7m (repG7m t) = lamOf gramG7m (repG7m t')) (x : ℚ) :
    thetaCount gramG7m (repG7m t) x = thetaCount gramG7m (repG7m t') x := by
  have key := qcoeff_eq_lincomb (lamOf gramG7m (repG7m t'))
    (thetaCount gramG7m (repG7m t)) (thetaCount gramG7m (repG7m t')) (fun _ => 0) 1 0
    (fun x hx => hlam ▸ thetaCoeff_support_nat posDef_G7m even_G7m (ratVec_repG7m_eq_inv t) _
      (lamOf_nonpos _ _) (lamOf_congr _ _) (fun _ => 1) x hx)
    (fun x hx => thetaCoeff_support_nat posDef_G7m even_G7m (ratVec_repG7m_eq_inv t') _
      (lamOf_nonpos _ _) (lamOf_congr _ _) (fun _ => 1) x hx)
    (fun e he => absurd rfl he)
    (fun y hy => summable_norm_thetaCount posDef_G7m _ hy)
    (fun y hy => summable_norm_thetaCount posDef_G7m _ hy) (fun _ _ => by simp)
    (fun τ => by
      rw [← latticeTheta_eq_tsum_thetaCount posDef_G7m _ τ.im_pos,
        ← latticeTheta_eq_tsum_thetaCount posDef_G7m _ τ.im_pos, latticeTheta_repG7m,
        latticeTheta_repG7m, hmod]
      simp) x
  rw [key]
  ring

theorem thetaG7m_neg (j : Fin 21) (τ : ℂ) : thetaG7m (-j) τ = thetaG7m j τ := by
  rw [← modG7m_neg j, ← latticeTheta_repG7m, ratVec_repG7m_neg, latticeTheta_neg,
    latticeTheta_repG7m, modG7m_self j]

theorem serreThetaG7m_o_S (j : Fin 21) (τ : ℍ) :
    Derivative.serreDerivative 2 (θG7m (oG7m j)) (S • τ) =
      (τ : ℂ) ^ 4 * ∑ k, SθG7m j k * Derivative.serreDerivative 2 (θG7m (oG7m k)) τ := by
  rw [serreThetaG7m_S (oG7m j) τ]
  congr 1
  refine (Fintype.sum_equiv (⟨oG7m, oG7m, oG7m_data.1, oG7m_data.1⟩ : Fin 21 ≃ Fin 21) _ _
    fun k => ?_).symm
  show SθG7m j k * _ = SθG7m (oG7m j) (oG7m k) * _
  simp only [SθG7m, Matrix.of_apply, eChar_sG7m_o]
  rfl

theorem serreThetaG7m_o_T (j : Fin 21) (τ : ℍ) :
    Derivative.serreDerivative 2 (θG7m (oG7m j)) (T • τ) =
      eChar (eG7m j) * Derivative.serreDerivative 2 (θG7m (oG7m j)) τ := by
  rw [serreThetaG7m_T, eChar_eG7m_o]

theorem FFG7m_o_S (τ : ℍ) :
    (fun j => FFG7m (S • τ) (oG7m j)) = SθG7m *ᵥ fun j => FFG7m τ (oG7m j) :=
  weight_zero_S_ℍ (fun j τ => -6 * Derivative.serreDerivative 2 (θG7m (oG7m j)) τ) SθG7m
    (fun j τ => by
      rw [serreThetaG7m_o_S, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring) τ

theorem FFG7m_o_T (τ : ℍ) :
    (fun j => FFG7m (T • τ) (oG7m j)) = TθG7m *ᵥ fun j => FFG7m τ (oG7m j) :=
  weight_zero_T_ℍ (fun j τ => -6 * Derivative.serreDerivative 2 (θG7m (oG7m j)) τ) eG7m
    (fun j τ => by rw [serreThetaG7m_o_T]; ring) τ

/-- The `O(D)` average of `F`. -/
def FaFG7m (τ : ℍ) : Fin 21 → ℂ := (1 / 2 : ℂ) • (FFG7m τ + fun j => FFG7m τ (oG7m j))

theorem FaFG7m_S (τ : ℍ) : FaFG7m (S • τ) = SθG7m *ᵥ FaFG7m τ := by
  funext j
  have h1 := congrFun (FFG7m_S τ) j
  have h2 : FFG7m (S • τ) (oG7m j) = (SθG7m *ᵥ fun k => FFG7m τ (oG7m k)) j :=
    congrFun (FFG7m_o_S τ) j
  simp only [FaFG7m, mulVec_smul, mulVec_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul, h1, h2]

theorem FaFG7m_T (τ : ℍ) : FaFG7m (T • τ) = TθG7m *ᵥ FaFG7m τ := by
  funext j
  have h1 := congrFun (FFG7m_T τ) j
  have h2 : FFG7m (T • τ) (oG7m j) = (TθG7m *ᵥ fun k => FFG7m τ (oG7m k)) j :=
    congrFun (FFG7m_o_T τ) j
  simp only [FaFG7m, mulVec_smul, mulVec_add, Pi.smul_apply, Pi.add_apply, smul_eq_mul, h1, h2]

theorem FFG7m_neg' (τ : ℍ) (j : Fin 21) : FFG7m τ (-j) = FFG7m τ j := by
  have hθ : θG7m (-j) = θG7m j := funext fun τ => thetaG7m_neg j τ
  unfold FFG7m
  rw [hθ]

theorem FaFG7m_const (τ : ℍ) (j : Fin 21) : FaFG7m τ j = FaFG7m τ (ιG7m (πG7m j)) := by
  have hneg : ∀ k, FaFG7m τ (-k) = FaFG7m τ k := fun k => by
    simp only [FaFG7m, Pi.smul_apply, Pi.add_apply, oG7m_neg, FFG7m_neg']
  have ho : ∀ k, FaFG7m τ (oG7m k) = FaFG7m τ k := fun k => by
    simp only [FaFG7m, Pi.smul_apply, Pi.add_apply, oG7m_data.1 k, add_comm]
  rcases orbit_G7m j with h | h | h | h <;> rw [h]
  · rw [hneg]
  · rw [ho]
  · rw [hneg, ho]

/-- The even block of the averaged `F`. -/
def FFEG7m (τ : ℍ) : Fin 4 × Fin 2 → ℂ := fun e => FaFG7m τ (ιG7m e)

theorem FFEG7m_covariant (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG7m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FFEG7m (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FFEG7m τ :=
  covariant_of_S_T σ FFEG7m
    (fun τ => by
      rw [hσS]
      exact reduced_S FaFG7m SθG7m ιG7m πG7m FaFG7m_S FaFG7m_const τ)
    (fun τ => by
      rw [hσT]
      exact reduced_T FaFG7m (fun j => eG7m j - 1 / 3) ιG7m FaFG7m_T τ)

theorem mdifferentiable_FFG7m (j : Fin 21) : MDiff (fun τ : ℍ => FFG7m τ j) := by
  have h1 : MDiff (fun τ : ℍ => -6 * Derivative.serreDerivative 2 (θG7m j) τ) :=
    (Derivative.serreDerivative_mdifferentiable 2 (mdifferentiable_θG7m j)).const_smul
      (-6 : ℂ)
  exact mdifferentiable_div_eta8_ℍ h1

theorem mdifferentiable_FFEG7m (e : Fin 4 × Fin 2) : MDiff (fun τ : ℍ => FFEG7m τ e) := by
  have h := ((mdifferentiable_FFG7m (ιG7m e)).add
    (mdifferentiable_FFG7m (oG7m (ιG7m e)))).const_smul (1 / 2 : ℂ)
  convert h using 1
  funext τ
  rfl

/-! ## Coefficients, `q`-expansions -/

/-- The averaged `F`-coefficients of the even-block coordinate `e`. -/
def FcEG7m (e : Fin 4 × Fin 2) (x : ℚ) : ℚ :=
  (minusSixD2Coeff (thetaCount gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ))) x +
    minusSixD2Coeff (thetaCount gramG7m (repG7m (((oG7m (ιG7m e) : Fin 21) : ℕ) : ℤ))) x) / 2

/-- The averaged `Θ_H`-coefficients of the even-block coordinate `e`. -/
def HcEG7m (e : Fin 4 × Fin 2) (x : ℚ) : ℚ :=
  (thetaCoeff gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ)) (quadOf MHG7m) x +
    thetaCoeff gramG7m (repG7m (((oG7m (ιG7m e) : Fin 21) : ℕ) : ℤ)) (quadOf MHG7m) x) / 2

theorem F_G7m_qexp (j : Fin 21) (τ : ℍ) :
    -6 * Derivative.serreDerivative 2 (θG7m j) τ = ∑' x : ℚ,
      ((minusSixD2Coeff (thetaCount gramG7m (repG7m ((j : ℕ) : ℤ))) x : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * τ) :=
  minusSixSerre_theta_qexp posDef_G7m even_G7m (ratVec_repG7m_eq_inv _) τ

theorem H_G7m_qexp (j : Fin 21) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQG7m MHG7m j τ = ∑' x : ℚ,
      ((thetaCoeff gramG7m (repG7m ((j : ℕ) : ℤ)) (quadOf MHG7m) x : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * τ) :=
  latticeThetaQ_eq_tsum_thetaCoeff posDef_G7m MHG7m _ hτ

theorem summable_F_G7m (j : Fin 21) {y : ℝ} (hy : 0 < y) :
    Summable fun x : ℚ =>
      ‖((minusSixD2Coeff (thetaCount gramG7m (repG7m ((j : ℕ) : ℤ))) x : ℚ) : ℂ)‖ *
        Real.exp (-2 * π * (x : ℝ) * y) :=
  summable_norm_minusSixD2Coeff posDef_G7m even_G7m (ratVec_repG7m_eq_inv _) hy

theorem summable_FcEG7m (e : Fin 4 × Fin 2) {y : ℝ} (hy : 0 < y) :
    Summable fun x : ℚ => ‖((FcEG7m e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y) :=
  summable_half_add _ _ (summable_F_G7m _ hy) (summable_F_G7m _ hy)

theorem summable_HcEG7m (e : Fin 4 × Fin 2) {y : ℝ} (hy : 0 < y) :
    Summable fun x : ℚ => ‖((HcEG7m e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y) :=
  summable_half_add _ _ (summable_norm_thetaCoeff posDef_G7m MHG7m _ hy)
    (summable_norm_thetaCoeff posDef_G7m MHG7m _ hy)

/-- `λ` is the same for `j` and `13 j` (kernel-checked). -/
theorem lamOf_oG7m : ∀ j : Fin 21,
    lamOf gramG7m (repG7m (((oG7m j : Fin 21) : ℕ) : ℤ)) = lamOf gramG7m (repG7m ((j : ℕ) : ℤ)) := by
  decide +kernel

theorem support_FcEG7m (e : Fin 4 × Fin 2) (x : ℚ) (h : FcEG7m e x ≠ 0) :
    ∃ n : ℕ, x = (n : ℚ) + lamOf gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ)) := by
  by_cases h1 : minusSixD2Coeff (thetaCount gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ))) x = 0
  · have h2 : minusSixD2Coeff (thetaCount gramG7m
        (repG7m (((oG7m (ιG7m e) : Fin 21) : ℕ) : ℤ))) x ≠ 0 := by
      intro h2
      apply h
      rw [FcEG7m, h1, h2]
      ring
    rw [← lamOf_oG7m]
    exact support_minusSix posDef_G7m even_G7m (ratVec_repG7m_eq_inv _) x h2
  · exact support_minusSix posDef_G7m even_G7m (ratVec_repG7m_eq_inv _) x h1

theorem support_HcEG7m (e : Fin 4 × Fin 2) (x : ℚ) (h : HcEG7m e x ≠ 0) :
    ∃ n : ℕ, x = (n : ℚ) + lamOf gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ)) := by
  by_cases h1 : thetaCoeff gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ)) (quadOf MHG7m) x = 0
  · have h2 : thetaCoeff gramG7m (repG7m (((oG7m (ιG7m e) : Fin 21) : ℕ) : ℤ))
        (quadOf MHG7m) x ≠ 0 := by
      intro h2
      apply h
      rw [HcEG7m, h1, h2]
      ring
    rw [← lamOf_oG7m]
    exact thetaCoeff_support_nat posDef_G7m even_G7m (ratVec_repG7m_eq_inv _) _
      (lamOf_nonpos _ _) (lamOf_congr _ _) _ x h2
  · exact thetaCoeff_support_nat posDef_G7m even_G7m (ratVec_repG7m_eq_inv _) _
      (lamOf_nonpos _ _) (lamOf_congr _ _) _ x h1

/-- The theta side `φ F + κ Θ_H` (divided by `η⁸`) on the even block. -/
def GG7m (φ κ : ℚ) (τ : ℍ) : Fin 4 × Fin 2 → ℂ :=
  (φ : ℂ) • FFEG7m τ + (κ : ℂ) • FEG7m MHG7m τ

/-- `η⁸ · G = φ ∑ FcE q^x + κ ∑ HcE q^x`. -/
theorem eta8_mul_GG7m (φ κ : ℚ) (τ : ℍ) (e : Fin 4 × Fin 2) :
    eta8 τ * GG7m φ κ τ e =
      (φ : ℂ) * ∑' x : ℚ, ((FcEG7m e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ) +
        (κ : ℂ) * ∑' x : ℚ, ((HcEG7m e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ) := by
  have hη := eta8_ne_zero τ.im_pos
  have hF : ∑' x : ℚ, ((FcEG7m e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ) =
      (1 / 2 : ℂ) * (-6 * Derivative.serreDerivative 2 (θG7m (ιG7m e)) τ +
        -6 * Derivative.serreDerivative 2 (θG7m (oG7m (ιG7m e))) τ) := by
    rw [F_G7m_qexp, F_G7m_qexp, half_add_qseries _ _ (fun y hy => summable_F_G7m _ hy)
      (fun y hy => summable_F_G7m _ hy)]
    rfl
  have hH : ∑' x : ℚ, ((HcEG7m e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ) =
      (1 / 2 : ℂ) * (thetaQG7m MHG7m (ιG7m e) τ + thetaQG7m MHG7m (oG7m (ιG7m e)) τ) := by
    rw [H_G7m_qexp _ τ.im_pos, H_G7m_qexp _ τ.im_pos, half_add_qseries _ _
      (fun y hy => summable_norm_thetaCoeff posDef_G7m MHG7m _ hy)
      (fun y hy => summable_norm_thetaCoeff posDef_G7m MHG7m _ hy)]
    rfl
  rw [hF, hH]
  simp only [GG7m, FFEG7m, FaFG7m, FFG7m, FEG7m, FaG7m, FG7m, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  field_simp

theorem GG7m_covariant (φ κ : ℚ)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG7m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), GG7m φ κ (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ GG7m φ κ τ := by
  intro γ τ
  rw [GG7m, GG7m, FFEG7m_covariant σ hσS hσT γ τ,
    FEG7m_covariant harmonic_quadratics.2.2.2.1 σ hσS hσT γ τ, mulVec_add, mulVec_smul,
    mulVec_smul]

theorem mdifferentiable_GG7m (φ κ : ℚ) (e : Fin 4 × Fin 2) :
    MDiff (fun τ : ℍ => GG7m φ κ τ e) := by
  have h := ((mdifferentiable_FFEG7m e).const_smul (φ : ℂ)).add
    ((mdifferentiable_FEG7m MHG7m e).const_smul (κ : ℂ))
  convert h using 1
  funext τ
  rfl

/-- The polar entries of the even block (kernel-checked). -/
theorem ι_polar_G7m (e : Fin 4 × Fin 2) (x : ℚ) (j : Fin 21)
    (hj : j = ιG7m e ∨ j = oG7m (ιG7m e))
    (h : (j = 0 ∧ x = 0) ∨ ((j = 4 ∨ j = 10 ∨ j = 11 ∨ j = 17) ∧ x = 2 / 21)) :
    (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 2 / 21) := by
  have hι : ∀ e : Fin 4 × Fin 2, ∀ j : Fin 21, (j = ιG7m e ∨ j = oG7m (ιG7m e)) →
      (j = 0 → e = (0, 0)) ∧ ((j = 4 ∨ j = 10 ∨ j = 11 ∨ j = 17) → e = (2, 1)) := by
    decide +kernel
  obtain ⟨h0, h1⟩ := hι e j hj
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact Or.inl ⟨h0 ha, hb⟩
  · exact Or.inr ⟨h1 ha, hb⟩

/-! ## The main theorem -/

/-- **`m = 3`, reverse orientation, from pole cancellation**: `hcancel` on the even block. -/
theorem m3_reverse_hcancel_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG7m)
    (V : ℍ → Fin 4 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 4 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 →
      ∃ n : ℕ, x = (n : ℚ) + lamOf gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ)))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (A : ℕ) (hvac0 : δc (0, 0) 0 = 1) (hpolar : δc (2, 1) (2 / 21) = -(A : ℚ))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 →
      (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 2 / 21)) :
    ∀ e x, δc e x = phiM3Reverse * FcEG7m e x + kappaM3Reverse A * HcEG7m e x := by
  set φ := phiM3Reverse with hφ
  set κ := kappaM3Reverse A with hκ
  have hrem : ∀ e x, x < 1 / 3 → δc e x - φ * FcEG7m e x - κ * HcEG7m e x = 0 := by
    intro e x hx
    by_contra hne
    have hx1 : x < 1 := by linarith
    have hcases : (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 2 / 21) := by
      by_cases hd : δc e x = 0
      · have ht : FcEG7m e x ≠ 0 ∨ HcEG7m e x ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply hne
          rw [hd, hcon.1, hcon.2]
          ring
        rcases ht with ht | ht
        · rw [FcEG7m, minusSixD2Coeff_of_lt_one _ hx1, minusSixD2Coeff_of_lt_one _ hx1] at ht
          by_cases h1 : thetaCount gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ)) x = 0
          · have h2 : thetaCount gramG7m (repG7m (((oG7m (ιG7m e) : Fin 21) : ℕ) : ℤ)) x ≠ 0 := by
              intro h2
              apply ht
              rw [h1, h2]
              ring
            exact ι_polar_G7m e x _ (Or.inr rfl) (polar_G7m _ hx h2)
          · exact ι_polar_G7m e x _ (Or.inl rfl) (polar_G7m _ hx h1)
        · rw [HcEG7m] at ht
          by_cases h1 : thetaCoeff gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ))
              (quadOf MHG7m) x = 0
          · have h2 : thetaCoeff gramG7m (repG7m (((oG7m (ιG7m e) : Fin 21) : ℕ) : ℤ))
                (quadOf MHG7m) x ≠ 0 := by
              intro h2
              apply ht
              rw [h1, h2]
              ring
            exact ι_polar_G7m e x _ (Or.inr rfl) (polar_G7m _ hx h2)
          · exact ι_polar_G7m e x _ (Or.inl rfl) (polar_G7m _ hx h1)
      · exact hother e x hx hd
    apply hne
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hc1 : repG7m (((ιG7m (0, 0) : Fin 21) : ℕ) : ℤ) = cosetG7m 0 0 := by decide +kernel
      have hc2 : repG7m (((oG7m (ιG7m (0, 0)) : Fin 21) : ℕ) : ℤ) = cosetG7m 0 0 := by
        decide +kernel
      rw [FcEG7m, HcEG7m, hc1, hc2, minusSixD2Coeff_of_lt_one _ (by norm_num), count_G7m_vac0,
        thetaCoeff_at_zero posDef_G7m _ (quadOf_zero MHG7m), hvac0, hφ, phiM3Reverse]
      ring
    · have hc1 : repG7m (((ιG7m (2, 1) : Fin 21) : ℕ) : ℤ) = repG7m 4 := by decide +kernel
      have hc2 : repG7m (((oG7m (ιG7m (2, 1)) : Fin 21) : ℕ) : ℤ) = repG7m 10 := by
        decide +kernel
      have h25 : cosetG7m 2 1 = repG7m 25 := by decide +kernel
      have h11 : cosetG7m (-2) 1 = repG7m (-11) := by decide +kernel
      have hN4 : thetaCount gramG7m (repG7m 4) (2 / 21) = 1 := by
        rw [thetaCount_repG7m_congr (t' := 25) (by decide +kernel) (by decide +kernel), ← h25,
          count_G7m_21]
      have hN10 : thetaCount gramG7m (repG7m 10) (2 / 21) = 0 := by
        rw [thetaCount_repG7m_congr (t' := -11) (by decide +kernel) (by decide +kernel), ← h11,
          count_G7m_m21]
      have hH4 : thetaCoeff gramG7m (repG7m 4) (quadOf MHG7m) (2 / 21) = -4 / 7 := by
        rw [thetaCoeff_repG7m_congr (t' := 25) (by decide +kernel) (by decide +kernel), ← h25,
          ← funext HG7m_eq_quad, H_G7m_21]
      have hH10 : thetaCoeff gramG7m (repG7m 10) (quadOf MHG7m) (2 / 21) = 0 := by
        rw [thetaCoeff_repG7m_congr (t' := -11) (by decide +kernel) (by decide +kernel), ← h11,
          ← funext HG7m_eq_quad, H_G7m_m21]
      rw [FcEG7m, HcEG7m, hc1, hc2, minusSixD2Coeff_of_lt_one _ (by norm_num),
        minusSixD2Coeff_of_lt_one _ (by norm_num), hN4, hN10, hH4, hH10, hpolar, hφ, hκ,
        phiM3Reverse, kappaM3Reverse]
      ring
  have hdiff : ∀ e (τ : ℍ), V τ e - GG7m φ κ τ e =
      (∑' x : ℚ, (((δc e x : ℚ) : ℂ) - (φ : ℂ) * ((FcEG7m e x : ℚ) : ℂ) -
        (κ : ℂ) * ((HcEG7m e x : ℚ) : ℂ)) * cexp (2 * π * I * (x : ℂ) * τ)) / eta8 τ := by
    intro e τ
    have hη := eta8_ne_zero τ.im_pos
    have key := tsum_sub_lincomb (fun x => ((δc e x : ℚ) : ℂ))
      (fun x => ((FcEG7m e x : ℚ) : ℂ)) (fun x => ((HcEG7m e x : ℚ) : ℂ)) (φ : ℂ) (κ : ℂ)
      (hsum e) (fun y hy => summable_FcEG7m e hy) (fun y hy => summable_HcEG7m e hy) τ
    rw [← key, ← hVq e τ, ← eta8_mul_GG7m, eq_div_iff hη]
    ring
  have hpp : ∀ e, UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ => V τ e - GG7m φ κ τ e) := by
    intro e
    rw [funext (hdiff e)]
    refine isBoundedAtImInfty_tsum_div_eta8 _ (fun x hx => ?_) (y₀ := 1)
      (summable_lincomb _ _ _ _ _ (hsum e 1 one_pos) (summable_FcEG7m e one_pos)
        (summable_HcEG7m e one_pos))
    by_contra hlt
    push Not at hlt
    apply hx
    have h0 := hrem e x hlt
    have h0' : (((δc e x - φ * FcEG7m e x - κ * HcEG7m e x : ℚ)) : ℂ) = 0 := by
      rw [h0, Rat.cast_zero]
    push_cast at h0'
    exact h0'
  have hVG : V = GG7m φ κ :=
    pole_cancellation σ hfin (noInvariantE_sigma_G7m σ hσS hσT) V (GG7m φ κ) hVhol
      (mdifferentiable_GG7m φ κ) hVcov (GG7m_covariant φ κ σ hσS hσT) hpp
  intro e
  refine qcoeff_eq_lincomb (lamOf gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ))) (δc e) _ _ φ κ
    (hsupp e) (support_FcEG7m e) (support_HcEG7m e) (hsum e)
    (fun y hy => summable_FcEG7m e hy) (fun y hy => summable_HcEG7m e hy) fun τ => ?_
  rw [← hVq e τ, hVG, eta8_mul_GG7m]

/-- **`m = 3`, reverse orientation: `dim U₁ = 14 + 42A`**, with `hcancel` derived from pole
cancellation. -/
theorem m3_reverse_dimension_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG7m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG7m)
    (V : ℍ → Fin 4 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 4 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 →
      ∃ n : ℕ, x = (n : ℚ) + lamOf gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ)))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (A d : ℕ) (hvac0 : δc (0, 0) 0 = 1) (hpolar : δc (2, 1) (2 / 21) = -(A : ℚ))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 →
      (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 2 / 21))
    (hvac1 : δc (0, 0) 1 = 2 * (d : ℚ) - 94) :
    d = 14 + 42 * A := by
  have h := m3_reverse_hcancel_of_voa σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum A hvac0
    hpolar hother (0, 0) 1
  have hc1 : repG7m (((ιG7m (0, 0) : Fin 21) : ℕ) : ℤ) = cosetG7m 0 0 := by decide +kernel
  have hc2 : repG7m (((oG7m (ιG7m (0, 0)) : Fin 21) : ℕ) : ℤ) = cosetG7m 0 0 := by
    decide +kernel
  rw [FcEG7m, HcEG7m, hc1, hc2, minusSixD2Coeff_one, count_G7m_vac1, count_G7m_vac0,
    ← funext HG7m_eq_quad, H_G7m_vac1, hvac1, phiM3Reverse, kappaM3Reverse] at h
  have hd : (d : ℚ) = 14 + 42 * A := by linarith
  exact_mod_cast hd

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.thetaCount_repG7m_congr
#print axioms HaagerupIzumi.C8.Theta.FFEG7m_covariant
#print axioms HaagerupIzumi.C8.Theta.eta8_mul_GG7m
#print axioms HaagerupIzumi.C8.Theta.m3_reverse_hcancel_of_voa
#print axioms HaagerupIzumi.C8.Theta.m3_reverse_dimension_of_voa
