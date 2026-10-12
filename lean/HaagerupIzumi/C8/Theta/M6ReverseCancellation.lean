module

public import HaagerupIzumi.C8.Theta.E2ThetaSummable
public import HaagerupIzumi.C8.Theta.M3FirstCancellation

@[expose] public section

/-!
# `m = 6`, reverse orientation: `dim U₁ = 5 + 12P` from pole cancellation

W6 plan items 1–4 assembled for Table 4 (`G₆⁻`, lines 3742–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`), as `Theta/M3FirstCancellation` does for
Table 1.  Here the theta side is `φ F + κ Θ_H` with `F = -6 D₂ Θ` (Serre derivative,
`Theta/SerreTheta`, `Theta/E2Theta`), `φ = 1`, `κ = P` (line 3767).

**Superseded by `Theta/M6ReverseSym`.**  This file uses the 8-dimensional block of orbits under
`-1` only; the manuscript's `m = 6` representation is the 6-dimensional quotient by `-1` and the
interchange `b ↔ c` (lines 3714–3720, 3762–3766), on which the VOA provides `σ`.
`Theta/M6ReverseSym` (`m6_reverse_hcancel_of_voa_sym`, `m6_reverse_dimension_of_voa_sym`) and
`Theta/ObstructionsOfVoa` (`m6_reverse_obstruction_of_voa`) use that block; the theorems below
remain valid statements about the 8-dimensional block.

* theta side (proved): the even-block vector (`E = Fin 2 × Fin 2 × Fin 2`, orbits under `-1`)
  `φ F/η⁸ + κ Θ_H/η⁸` (`GG6m`) is holomorphic, `σ`-covariant for `σ(S) = SθEG6m`,
  `σ(T) = TθEG6m`; its `q`-expansions have coefficients `minusSixD2Coeff` and `thetaCoeff`;
  its complete polar part is the vacuum entry and the polar coset `(1,1,1) = -w/3 + L` at
  `q^{1/6}` (`polar_G6m`, `minusSixD2Coeff_of_lt_one`); no `T`-fixed coordinate;
* VOA side (named hypotheses, as for Table 1): `σ` (`σ(S)`, `σ(T)`, finite image); the vector
  `V = v` (holomorphic, covariant) with `η⁸`-multiplied `q`-expansion `δc`, support and
  convergence; polar data `δc (0,0,0) 0 = 1` (vacuum `q⁰` of `η⁸ χ_B`),
  `δc (1,1,1) (1/6) = -P`, no other polar coefficient; vacuum coefficient
  `δc (0,0,0) 1 = 2 dim U₁ - 94`.

Conclusion: `dim U₁ = 5 + 12P` (`m6_reverse_dimension_of_voa`).
-/

noncomputable section

open Complex Matrix ModularGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups Real Manifold

namespace HaagerupIzumi.C8
namespace Theta

/-- `f/η⁸` is holomorphic on `ℍ` for `f` holomorphic on `ℍ`. -/
theorem mdifferentiable_div_eta8_ℍ {F : ℍ → ℂ} (hF : MDiff F) :
    MDiff (fun τ : ℍ => F τ / eta8 τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hF ⊢
  refine (hF.div differentiableOn_eta8 fun z hz => eta8_ne_zero hz).congr fun z hz => ?_
  simp [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem thetaG6m_neg (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaG6m (-p.1, -p.2.1, -p.2.2) τ = thetaG6m p τ := by
  rw [← modG6m_neg p, ← latticeTheta_cosetG6m, ratVec_cosetG6m_neg, latticeTheta_neg,
    latticeTheta_cosetG6m, modG6m_self p]

theorem FFG6m_const (τ : ℍ) (q : Fin 2 × Fin 2 × Fin 3) :
    FFG6m τ q = FFG6m τ (ιG6m (πG6m q)) := by
  rcases orbit_G6m q with h | h <;> rw [h]
  have hθ : θG6m (-q.1, -q.2.1, -q.2.2) = θG6m q := funext fun τ => thetaG6m_neg q τ
  unfold FFG6m
  rw [hθ]

/-- The even block of `F = -6 D₂ Θ / η⁸`. -/
def FFEG6m (τ : ℍ) : Fin 2 × Fin 2 × Fin 2 → ℂ := fun e => FFG6m τ (ιG6m e)

theorem FFEG6m_covariant (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG6m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG6m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FFEG6m (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FFEG6m τ :=
  covariant_of_S_T σ FFEG6m
    (fun τ => by
      rw [hσS]
      exact reduced_S FFG6m SθG6m ιG6m πG6m FFG6m_S FFG6m_const τ)
    (fun τ => by
      rw [hσT]
      exact reduced_T FFG6m (fun p => eG6m p - 1 / 3) ιG6m FFG6m_T τ)

theorem mdifferentiable_FFEG6m (e : Fin 2 × Fin 2 × Fin 2) :
    MDiff (fun τ : ℍ => FFEG6m τ e) := by
  have h1 : MDiff (fun τ : ℍ => -6 * Derivative.serreDerivative 2 (θG6m (ιG6m e)) τ) :=
    (Derivative.serreDerivative_mdifferentiable 2 (mdifferentiable_θG6m (ιG6m e))).const_smul
      (-6 : ℂ)
  exact mdifferentiable_div_eta8_ℍ h1

/-- The coset of the even-block label `e`. -/
abbrev cosetEG6m (e : Fin 2 × Fin 2 × Fin 2) : Fin 4 → ℚ :=
  cosetG6m (((ιG6m e).1 : ℕ) : ℤ) (((ιG6m e).2.1 : ℕ) : ℤ) (((ιG6m e).2.2 : ℕ) : ℤ)

theorem F_G6m_qexp (e : Fin 2 × Fin 2 × Fin 2) (τ : ℍ) :
    -6 * Derivative.serreDerivative 2 (θG6m (ιG6m e)) τ = ∑' x : ℚ,
      ((minusSixD2Coeff (thetaCount gramG6m (cosetEG6m e)) x : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * τ) :=
  minusSixSerre_theta_qexp posDef_G6m even_G6m (ratVec_cosetG6m_eq_inv _ _ _) τ

theorem H_G6m_qexp (e : Fin 2 × Fin 2 × Fin 2) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQG6m MHG6m (ιG6m e) τ = ∑' x : ℚ,
      ((thetaCoeff gramG6m (cosetEG6m e) (quadOf MHG6m) x : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * τ) :=
  latticeThetaQ_eq_tsum_thetaCoeff posDef_G6m MHG6m _ hτ

/-- The theta side `φ F + κ Θ_H` (divided by `η⁸`) on the even block. -/
def GG6m (φ κ : ℚ) (τ : ℍ) : Fin 2 × Fin 2 × Fin 2 → ℂ :=
  (φ : ℂ) • FFEG6m τ + (κ : ℂ) • FEG6m MHG6m τ

theorem GG6m_apply (φ κ : ℚ) (τ : ℍ) (e : Fin 2 × Fin 2 × Fin 2) :
    GG6m φ κ τ e = ((φ : ℂ) * (-6 * Derivative.serreDerivative 2 (θG6m (ιG6m e)) τ) +
      (κ : ℂ) * thetaQG6m MHG6m (ιG6m e) τ) / eta8 τ := by
  simp only [GG6m, FFEG6m, FFG6m, FEG6m, FG6m, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem GG6m_covariant (φ κ : ℚ)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG6m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG6m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), GG6m φ κ (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ GG6m φ κ τ := by
  intro γ τ
  rw [GG6m, GG6m, FFEG6m_covariant σ hσS hσT γ τ,
    FEG6m_covariant harmonic_quadratics.2.2.2.2.2 σ hσS hσT γ τ, mulVec_add, mulVec_smul,
    mulVec_smul]

theorem mdifferentiable_GG6m (φ κ : ℚ) (e : Fin 2 × Fin 2 × Fin 2) :
    MDiff (fun τ : ℍ => GG6m φ κ τ e) := by
  have h := ((mdifferentiable_FFEG6m e).const_smul (φ : ℂ)).add
    ((mdifferentiable_FEG6m MHG6m e).const_smul (κ : ℂ))
  convert h using 1
  funext τ
  rfl

theorem ι_polar_G6m (e : Fin 2 × Fin 2 × Fin 2) (x : ℚ)
    (h : (ιG6m e = (0, 0, 0) ∧ x = 0) ∨ ((ιG6m e = (1, 1, 1) ∨ ιG6m e = (1, 1, 2)) ∧ x = 1 / 6)) :
    (e = (0, 0, 0) ∧ x = 0) ∨ (e = (1, 1, 1) ∧ x = 1 / 6) := by
  have hι : ∀ e : Fin 2 × Fin 2 × Fin 2, (ιG6m e = (0, 0, 0) → e = (0, 0, 0)) ∧
      (ιG6m e = (1, 1, 1) → e = (1, 1, 1)) ∧ ιG6m e ≠ (1, 1, 2) := by
    decide +kernel
  obtain ⟨h0, h1, h2⟩ := hι e
  rcases h with ⟨ha, hb⟩ | ⟨ha | ha, hb⟩
  · exact Or.inl ⟨h0 ha, hb⟩
  · exact Or.inr ⟨h1 ha, hb⟩
  · exact absurd ha h2

theorem support_lamOf_G6m (e : Fin 2 × Fin 2 × Fin 2) (H : (Fin 4 → ℚ) → ℚ) (x : ℚ)
    (h : thetaCoeff gramG6m (cosetEG6m e) H x ≠ 0) :
    ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetEG6m e) :=
  thetaCoeff_support_nat posDef_G6m even_G6m (ratVec_cosetG6m_eq_inv _ _ _) _
    (lamOf_nonpos _ _) (lamOf_congr _ _) H x h

theorem support_minusSix_G6m (e : Fin 2 × Fin 2 × Fin 2) (x : ℚ)
    (h : minusSixD2Coeff (thetaCount gramG6m (cosetEG6m e)) x ≠ 0) :
    ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetEG6m e) := by
  rw [minusSixD2Coeff] at h
  by_cases h1 : thetaCount gramG6m (cosetEG6m e) x = 0
  · rw [h1, mul_zero, zero_add] at h
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hj' : thetaCount gramG6m (cosetEG6m e) (x - j) ≠ 0 := fun h0 => hj (by rw [h0, mul_zero])
    obtain ⟨n, hn⟩ := support_lamOf_G6m e (fun _ => 1) (x - j) hj'
    exact ⟨n + j, by push_cast; linarith⟩
  · exact support_lamOf_G6m e (fun _ => 1) x h1

/-- The polar coset: `polarG6m` and the label `(1,1,1)` have the same `Θ_H`-coefficients. -/
theorem thetaCoeff_polarG6m_eq (x : ℚ) :
    thetaCoeff gramG6m (cosetG6m 1 1 1) (quadOf MHG6m) x =
      thetaCoeff gramG6m polarG6m (quadOf MHG6m) x := by
  have hpol : ratVec polarG6m = (gramR gramG6m)⁻¹ *ᵥ
      intVec (![-1 - 1 + 1, 1, 1, 2 * 1 + 2 * 1 - 2 * 1] + gramG6m *ᵥ ![-1, -1, -1, -1]) := by
    rw [ratVec_polarG6m, ratVec_cosetG6m_eq_inv, intVec_add, mulVec_add, intVec_mulVec,
      mulVec_mulVec, nonsing_inv_mul _ (isUnit_det_of_posDef posDef_G6m), one_mulVec]
  have hlam : lamOf gramG6m polarG6m = lamOf gramG6m (cosetG6m 1 1 1) := by decide +kernel
  have key := qcoeff_eq_lincomb (lamOf gramG6m (cosetG6m 1 1 1))
    (thetaCoeff gramG6m (cosetG6m 1 1 1) (quadOf MHG6m))
    (thetaCoeff gramG6m polarG6m (quadOf MHG6m)) (fun _ => 0) 1 0
    (fun x hx => thetaCoeff_support_nat posDef_G6m even_G6m (ratVec_cosetG6m_eq_inv 1 1 1) _
      (lamOf_nonpos _ _) (lamOf_congr _ _) _ x hx)
    (fun x hx => hlam ▸ thetaCoeff_support_nat posDef_G6m even_G6m hpol _
      (lamOf_nonpos _ _) (lamOf_congr _ _) _ x hx)
    (fun e he => absurd rfl he)
    (fun y hy => summable_norm_thetaCoeff posDef_G6m MHG6m _ hy)
    (fun y hy => summable_norm_thetaCoeff posDef_G6m MHG6m _ hy) (fun _ _ => by simp)
    (fun τ => by
      rw [← latticeThetaQ_eq_tsum_thetaCoeff posDef_G6m MHG6m _ τ.im_pos,
        ← latticeThetaQ_eq_tsum_thetaCoeff posDef_G6m MHG6m _ τ.im_pos, ratVec_polarG6m,
        latticeThetaQ_add_intVec]
      simp) x
  rw [key]
  ring

/-- **`m = 6`, reverse orientation, from pole cancellation**: `hcancel` on the even block. -/
theorem m6_reverse_hcancel_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG6m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG6m)
    (V : ℍ → Fin 2 × Fin 2 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 2 × Fin 2 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetEG6m e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (P : ℕ) (hvac0 : δc (0, 0, 0) 0 = 1) (hpolar : δc (1, 1, 1) (1 / 6) = -(P : ℚ))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 →
      (e = (0, 0, 0) ∧ x = 0) ∨ (e = (1, 1, 1) ∧ x = 1 / 6)) :
    ∀ e x, δc e x = phiM6Reverse * minusSixD2Coeff (thetaCount gramG6m (cosetEG6m e)) x +
      kappaM6Reverse P * thetaCoeff gramG6m (cosetEG6m e) (quadOf MHG6m) x := by
  set φ := phiM6Reverse with hφ
  set κ := kappaM6Reverse P with hκ
  have hrem : ∀ e x, x < 1 / 3 →
      δc e x - φ * minusSixD2Coeff (thetaCount gramG6m (cosetEG6m e)) x -
        κ * thetaCoeff gramG6m (cosetEG6m e) (quadOf MHG6m) x = 0 := by
    intro e x hx
    by_contra hne
    have hx1 : x < 1 := by linarith
    have hcases : (e = (0, 0, 0) ∧ x = 0) ∨ (e = (1, 1, 1) ∧ x = 1 / 6) := by
      by_cases hd : δc e x = 0
      · have ht : thetaCount gramG6m (cosetEG6m e) x ≠ 0 ∨
            thetaCoeff gramG6m (cosetEG6m e) (quadOf MHG6m) x ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply hne
          rw [hd, minusSixD2Coeff_of_lt_one _ hx1, hcon.1, hcon.2]
          ring
        rcases ht with ht | ht
        · exact ι_polar_G6m e x (polar_G6m (ιG6m e) hx ht)
        · exact ι_polar_G6m e x (polar_G6m (ιG6m e) hx ht)
      · exact hother e x hx hd
    apply hne
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hc : cosetEG6m (0, 0, 0) = 0 := by decide +kernel
      rw [minusSixD2Coeff_of_lt_one _ (by norm_num), hc, count_G6m_vac0,
        thetaCoeff_at_zero posDef_G6m _ (quadOf_zero MHG6m), hvac0, hφ, phiM6Reverse]
      ring
    · have hc : cosetEG6m (1, 1, 1) = cosetG6m 1 1 1 := by decide +kernel
      rw [minusSixD2Coeff_of_lt_one _ (by norm_num), hc, thetaCoeff_polarG6m_eq,
        ← funext HG6m_eq_quad, H_G6m_polar, hpolar, hκ, kappaM6Reverse]
      ring
  have hdiff : ∀ e (τ : ℍ), V τ e - GG6m φ κ τ e =
      (∑' x : ℚ, (((δc e x : ℚ) : ℂ) -
        (φ : ℂ) * ((minusSixD2Coeff (thetaCount gramG6m (cosetEG6m e)) x : ℚ) : ℂ) -
        (κ : ℂ) * ((thetaCoeff gramG6m (cosetEG6m e) (quadOf MHG6m) x : ℚ) : ℂ)) *
          cexp (2 * π * I * (x : ℂ) * τ)) / eta8 τ := by
    intro e τ
    have hη := eta8_ne_zero τ.im_pos
    have key := tsum_sub_lincomb (fun x => ((δc e x : ℚ) : ℂ))
      (fun x => ((minusSixD2Coeff (thetaCount gramG6m (cosetEG6m e)) x : ℚ) : ℂ))
      (fun x => ((thetaCoeff gramG6m (cosetEG6m e) (quadOf MHG6m) x : ℚ) : ℂ)) (φ : ℂ) (κ : ℂ)
      (hsum e)
      (fun y hy => summable_norm_minusSixD2Coeff posDef_G6m even_G6m
        (ratVec_cosetG6m_eq_inv _ _ _) hy)
      (fun y hy => summable_norm_thetaCoeff posDef_G6m MHG6m _ hy) τ
    rw [← key, ← hVq e τ, ← F_G6m_qexp e τ, ← H_G6m_qexp e τ.im_pos, GG6m_apply, eq_div_iff hη,
      sub_mul, div_mul_cancel₀ _ hη]
    ring
  have hpp : ∀ e, UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ => V τ e - GG6m φ κ τ e) := by
    intro e
    rw [funext (hdiff e)]
    refine isBoundedAtImInfty_tsum_div_eta8 _ (fun x hx => ?_) (y₀ := 1)
      (summable_lincomb _ _ _ _ _ (hsum e 1 one_pos)
        (summable_norm_minusSixD2Coeff posDef_G6m even_G6m (ratVec_cosetG6m_eq_inv _ _ _) one_pos)
        (summable_norm_thetaCoeff posDef_G6m MHG6m _ one_pos))
    by_contra hlt
    push Not at hlt
    apply hx
    have h0 := hrem e x hlt
    have h0' : (((δc e x - φ * minusSixD2Coeff (thetaCount gramG6m (cosetEG6m e)) x -
        κ * thetaCoeff gramG6m (cosetEG6m e) (quadOf MHG6m) x : ℚ)) : ℂ) = 0 := by
      rw [h0, Rat.cast_zero]
    push_cast at h0'
    exact h0'
  have hVG : V = GG6m φ κ :=
    pole_cancellation σ hfin (noInvariantE_sigma_G6m σ hσS hσT) V (GG6m φ κ) hVhol
      (mdifferentiable_GG6m φ κ) hVcov (GG6m_covariant φ κ σ hσS hσT) hpp
  intro e
  refine qcoeff_eq_lincomb (lamOf gramG6m (cosetEG6m e)) (δc e) _ _ φ κ (hsupp e)
    (support_minusSix_G6m e) (support_lamOf_G6m e _) (hsum e)
    (fun y hy => summable_norm_minusSixD2Coeff posDef_G6m even_G6m
      (ratVec_cosetG6m_eq_inv _ _ _) hy)
    (fun y hy => summable_norm_thetaCoeff posDef_G6m MHG6m _ hy) fun τ => ?_
  have hη := eta8_ne_zero τ.im_pos
  rw [← hVq e τ, hVG, GG6m_apply, ← F_G6m_qexp e τ, ← H_G6m_qexp e τ.im_pos,
    mul_div_cancel₀ _ hη]

/-- **`m = 6`, reverse orientation: `dim U₁ = 5 + 12P`**, with `hcancel` derived from pole
cancellation. -/
theorem m6_reverse_dimension_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 2 × Fin 2 × Fin 2) ℂ)
    (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEG6m) (hσT : (σ T : Matrix _ _ ℂ) = TθEG6m)
    (V : ℍ → Fin 2 × Fin 2 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 2 × Fin 2 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetEG6m e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (P d : ℕ) (hvac0 : δc (0, 0, 0) 0 = 1) (hpolar : δc (1, 1, 1) (1 / 6) = -(P : ℚ))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 →
      (e = (0, 0, 0) ∧ x = 0) ∨ (e = (1, 1, 1) ∧ x = 1 / 6))
    (hvac1 : δc (0, 0, 0) 1 = 2 * (d : ℚ) - 94) :
    d = 5 + 12 * P := by
  have h := m6_reverse_hcancel_of_voa σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum P hvac0
    hpolar hother (0, 0, 0) 1
  have hc : cosetEG6m (0, 0, 0) = 0 := by decide +kernel
  rw [hc, minusSixD2Coeff_one, count_G6m_vac1, count_G6m_vac0, ← funext HG6m_eq_quad,
    H_G6m_vac1, hvac1, phiM6Reverse, kappaM6Reverse] at h
  have hd : (d : ℚ) = 5 + 12 * P := by linarith
  exact_mod_cast hd

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.FFEG6m_covariant
#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_polarG6m_eq
#print axioms HaagerupIzumi.C8.Theta.m6_reverse_hcancel_of_voa
#print axioms HaagerupIzumi.C8.Theta.m6_reverse_dimension_of_voa
