module

public import HaagerupIzumi.C8.Theta.M3FirstCancellation

@[expose] public section

/-!
# `m = 6`, first orientation: `dim U₁ = 8 + A` from pole cancellation

W6 plan items 1–4 assembled for Table 3 (`A₁ ⊕ A₁ ⊕ A₂`) of the proof of Proposition
`prop:near-group-current-obstructions` (lines 3714–3740 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`), as `Theta/M3FirstCancellation` does for
Table 1.  The identity `hcancel` is derived from `pole_cancellation` on the even block; its
integer-label form, the hypothesis `hcancel` of `m6_first_obstruction`, is
`m6_first_hcancel_table_of_voa` (`Theta/ObstructionsOfVoa`):

* theta side (proved): `κ F_H` on the even block `E = Fin 3 × Fin 2` (`κ = 8 - A`, line 3736)
  is holomorphic and `σ`-covariant for `σ(S) = SθEA1A1A2`, `σ(T) = TθEA1A1A2`; its complete
  polar part is the vacuum entry and the quarter-twist row `((10,0), q^{1/4})`
  (`polar_A1A1A2`); `σ` has no invariant vector;
* VOA side (named hypotheses, as for Table 1): `σ` with `σ(S)`, `σ(T)` as above and finite
  image (`hfin`, a property of the explicit matrices since `σ` is pinned at `S`, `T`); the difference vector `V` (holomorphic, covariant), its `η⁸`-multiplied
  `q`-expansion `∑ δc e x q^x` with support and convergence; polar data `δc (0,0) 0 = 0`,
  `δc (1,0) (1/4) = -A/2 - (-8/2)` (the projected polar coefficient, reference `A = 8`), no
  other polar coefficient; vacuum coefficient `δc (0,0) 1 = 2(dim U₁ - 16)`.

Conclusion: `dim U₁ = 8 + A` (`m6_first_dimension_of_voa`).
-/

noncomputable section

open Complex Matrix ModularGroup
open scoped MatrixGroups UpperHalfPlane Real Manifold

namespace HaagerupIzumi.C8
namespace Theta

theorem tsum_sub_smul (a b : ℚ → ℂ) (l : ℂ)
    (ha : ∀ y : ℝ, 0 < y → Summable fun e : ℚ => ‖a e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hb : ∀ y : ℝ, 0 < y → Summable fun e : ℚ => ‖b e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (τ : ℍ) :
    ∑' e : ℚ, a e * cexp (2 * π * I * (e : ℂ) * τ) -
        l * ∑' e : ℚ, b e * cexp (2 * π * I * (e : ℂ) * τ) =
      ∑' e : ℚ, (a e - l * b e) * cexp (2 * π * I * (e : ℂ) * τ) := by
  have s0 := summable_qseries_rat ha τ
  have s1 := (summable_qseries_rat hb τ).mul_left l
  rw [← tsum_mul_left, ← s0.tsum_sub s1]
  refine tsum_congr fun e => ?_
  ring

theorem summable_sub_smul (a b : ℚ → ℂ) (l : ℂ) {y : ℝ}
    (ha : Summable fun e : ℚ => ‖a e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hb : Summable fun e : ℚ => ‖b e‖ * Real.exp (-2 * π * (e : ℝ) * y)) :
    Summable fun e : ℚ => ‖a e - l * b e‖ * Real.exp (-2 * π * (e : ℝ) * y) := by
  refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_)
    (ha.add (hb.mul_left ‖l‖))
  have hn : ‖a e - l * b e‖ ≤ ‖a e‖ + ‖l‖ * ‖b e‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul]
  have hE := (Real.exp_pos (-2 * π * (e : ℝ) * y)).le
  calc ‖a e - l * b e‖ * Real.exp (-2 * π * (e : ℝ) * y)
      ≤ (‖a e‖ + ‖l‖ * ‖b e‖) * Real.exp (-2 * π * (e : ℝ) * y) :=
        mul_le_mul_of_nonneg_right hn hE
    _ = _ := by ring

/-- The coset of the even-block label `e`. -/
abbrev cosetEA1A1A2 (e : Fin 3 × Fin 2) : Fin 4 → ℚ :=
  cosetA1A1A2 (((ιA1A1A2 e).1 : ℕ) : ℤ) (((ιA1A1A2 e).2.1 : ℕ) : ℤ) (((ιA1A1A2 e).2.2 : ℕ) : ℤ)

theorem thetaQA1A1A2_ι_eq_tsum (e : Fin 3 × Fin 2) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQA1A1A2 MHA1A1A2 (ιA1A1A2 e) τ = ∑' x : ℚ,
      ((thetaCoeff gramA1A1A2 (cosetEA1A1A2 e) (quadOf MHA1A1A2) x : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * τ) :=
  latticeThetaQ_eq_tsum_thetaCoeff posDef_A1A1A2 MHA1A1A2 _ hτ

/-- The theta side `κ F_H` on the even block. -/
def GA1A1A2 (k : ℚ) (τ : ℍ) : Fin 3 × Fin 2 → ℂ := (k : ℂ) • FEA1A1A2 τ

theorem GA1A1A2_apply (k : ℚ) (τ : ℍ) (e : Fin 3 × Fin 2) :
    GA1A1A2 k τ e = ((k : ℂ) * thetaQA1A1A2 MHA1A1A2 (ιA1A1A2 e) τ) / eta8 τ := by
  simp only [GA1A1A2, FEA1A1A2, FA1A1A2, Pi.smul_apply, smul_eq_mul]
  ring

theorem GA1A1A2_covariant (k : ℚ)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEA1A1A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEA1A1A2) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), GA1A1A2 k (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ GA1A1A2 k τ := by
  intro γ τ
  rw [GA1A1A2, GA1A1A2, FEA1A1A2_covariant σ hσS hσT γ τ, mulVec_smul]

theorem mdifferentiable_GA1A1A2 (k : ℚ) (e : Fin 3 × Fin 2) :
    MDiff (fun τ : ℍ => GA1A1A2 k τ e) := by
  have h : (fun τ : ℍ => GA1A1A2 k τ e) = fun τ : ℍ =>
      (fun z : ℂ => (k : ℂ) * thetaQA1A1A2 MHA1A1A2 (ιA1A1A2 e) z) τ / eta8 τ :=
    funext fun τ => GA1A1A2_apply k τ e
  rw [h]
  exact mdifferentiable_div_eta8 ((differentiableOn_latticeThetaQ posDef_A1A1A2 _ _).const_mul _)

theorem ι_polar_A1A1A2 (e : Fin 3 × Fin 2) (x : ℚ)
    (h : (ιA1A1A2 e = (0, 0, 0) ∧ x = 0) ∨
      ((ιA1A1A2 e = (1, 0, 0) ∨ ιA1A1A2 e = (0, 1, 0)) ∧ x = 1 / 4)) :
    (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 4) := by
  have hι : ∀ e : Fin 3 × Fin 2, (ιA1A1A2 e = (0, 0, 0) → e = (0, 0)) ∧
      (ιA1A1A2 e = (1, 0, 0) → e = (1, 0)) ∧ ιA1A1A2 e ≠ (0, 1, 0) := by
    decide +kernel
  obtain ⟨h0, h1, h2⟩ := hι e
  rcases h with ⟨ha, hb⟩ | ⟨ha | ha, hb⟩
  · exact Or.inl ⟨h0 ha, hb⟩
  · exact Or.inr ⟨h1 ha, hb⟩
  · exact absurd ha h2

theorem thetaCoeff_A1A1A2_support_E (e : Fin 3 × Fin 2) (x : ℚ)
    (h : thetaCoeff gramA1A1A2 (cosetEA1A1A2 e) (quadOf MHA1A1A2) x ≠ 0) :
    ∃ n : ℕ, x = (n : ℚ) + lamOf gramA1A1A2 (cosetEA1A1A2 e) :=
  thetaCoeff_support_nat posDef_A1A1A2 even_A1A1A2 (ratVec_cosetA1A1A2_eq_inv _ _ _) _
    (lamOf_nonpos _ _) (lamOf_congr _ _) _ x h

/-- **`m = 6`, first orientation, from pole cancellation**: `hcancel` on the even block. -/
theorem m6_first_hcancel_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEA1A1A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEA1A1A2)
    (V : ℍ → Fin 3 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 3 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramA1A1A2 (cosetEA1A1A2 e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (A : ℕ) (hvac0 : δc (0, 0) 0 = 0)
    (hpolar : δc (1, 0) (1 / 4) = -(A : ℚ) / 2 - (-(8 : ℚ) / 2))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 → (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 4)) :
    ∀ e x, δc e x = kappaM6First A * thetaCoeff gramA1A1A2 (cosetEA1A1A2 e) (quadOf MHA1A1A2) x := by
  set k := kappaM6First A with hk
  have hrem : ∀ e x, x < 1 / 3 →
      δc e x - k * thetaCoeff gramA1A1A2 (cosetEA1A1A2 e) (quadOf MHA1A1A2) x = 0 := by
    intro e x hx
    by_contra hne
    have hcases : (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 4) := by
      by_cases hd : δc e x = 0
      · have ht : thetaCoeff gramA1A1A2 (cosetEA1A1A2 e) (quadOf MHA1A1A2) x ≠ 0 := by
          intro ht
          apply hne
          rw [hd, ht]
          ring
        exact ι_polar_A1A1A2 e x (polar_A1A1A2 (ιA1A1A2 e) hx ht)
      · exact hother e x hx hd
    apply hne
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hvac0, thetaCoeff_at_zero posDef_A1A1A2 _ (quadOf_zero MHA1A1A2)]
      ring
    · have hc : cosetEA1A1A2 (1, 0) = cosetA1A1A2 1 0 0 := by decide +kernel
      rw [hc, ← HA1A1A2_eq_quadOf, H_A_10, hpolar, hk, kappaM6First]
      ring
  have hdiff : ∀ e (τ : ℍ), V τ e - GA1A1A2 k τ e =
      (∑' x : ℚ, (((δc e x : ℚ) : ℂ) -
        (k : ℂ) * ((thetaCoeff gramA1A1A2 (cosetEA1A1A2 e) (quadOf MHA1A1A2) x : ℚ) : ℂ)) *
          cexp (2 * π * I * (x : ℂ) * τ)) / eta8 τ := by
    intro e τ
    have hη := eta8_ne_zero τ.im_pos
    have key := tsum_sub_smul (fun x => ((δc e x : ℚ) : ℂ))
      (fun x => ((thetaCoeff gramA1A1A2 (cosetEA1A1A2 e) (quadOf MHA1A1A2) x : ℚ) : ℂ)) (k : ℂ)
      (hsum e) (fun y hy => summable_norm_thetaCoeff posDef_A1A1A2 MHA1A1A2 _ hy) τ
    rw [← key, ← hVq e τ, ← thetaQA1A1A2_ι_eq_tsum e τ.im_pos, GA1A1A2_apply, eq_div_iff hη,
      sub_mul, div_mul_cancel₀ _ hη]
    ring
  have hpp : ∀ e, UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ => V τ e - GA1A1A2 k τ e) := by
    intro e
    rw [funext (hdiff e)]
    refine isBoundedAtImInfty_tsum_div_eta8 _ (fun x hx => ?_) (y₀ := 1)
      (summable_sub_smul _ _ _ (hsum e 1 one_pos)
        (summable_norm_thetaCoeff posDef_A1A1A2 MHA1A1A2 _ one_pos))
    by_contra hlt
    push Not at hlt
    apply hx
    have h0 := hrem e x hlt
    have h0' : (((δc e x - k * thetaCoeff gramA1A1A2 (cosetEA1A1A2 e) (quadOf MHA1A1A2) x : ℚ)) :
        ℂ) = 0 := by
      rw [h0, Rat.cast_zero]
    push_cast at h0'
    exact h0'
  have hVG : V = GA1A1A2 k :=
    pole_cancellation σ hfin (noInvariantE_sigma_A1A1A2 σ hσS hσT) V (GA1A1A2 k) hVhol
      (mdifferentiable_GA1A1A2 k) hVcov (GA1A1A2_covariant k σ hσS hσT) hpp
  intro e x
  have key := qcoeff_eq_lincomb (lamOf gramA1A1A2 (cosetEA1A1A2 e)) (δc e)
    (fun x => thetaCoeff gramA1A1A2 (cosetEA1A1A2 e) (quadOf MHA1A1A2) x) (fun _ => 0) k 0
    (hsupp e) (thetaCoeff_A1A1A2_support_E e) (fun e he => absurd rfl he) (hsum e)
    (fun y hy => summable_norm_thetaCoeff posDef_A1A1A2 MHA1A1A2 _ hy) (fun _ _ => by simp)
    (fun τ => by
      have hη := eta8_ne_zero τ.im_pos
      rw [← hVq e τ, hVG, GA1A1A2_apply, ← thetaQA1A1A2_ι_eq_tsum e τ.im_pos,
        mul_div_cancel₀ _ hη]
      simp) x
  rw [key]
  ring

/-- **`m = 6`, first orientation: `dim U₁ = 8 + A`**, with `hcancel` derived from pole
cancellation. -/
theorem m6_first_dimension_of_voa
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθEA1A1A2) (hσT : (σ T : Matrix _ _ ℂ) = TθEA1A1A2)
    (V : ℍ → Fin 3 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 3 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramA1A1A2 (cosetEA1A1A2 e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (A d : ℕ) (hvac0 : δc (0, 0) 0 = 0)
    (hpolar : δc (1, 0) (1 / 4) = -(A : ℚ) / 2 - (-(8 : ℚ) / 2))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 → (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 4))
    (hvac : δc (0, 0) 1 = 2 * ((d : ℚ) - 16)) :
    d = 8 + A := by
  have h := m6_first_hcancel_of_voa σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum A hvac0
    hpolar hother (0, 0) 1
  have hc : cosetEA1A1A2 (0, 0) = cosetA1A1A2 0 0 0 := by decide +kernel
  rw [hc, ← HA1A1A2_eq_quadOf, H_A_vac, hvac] at h
  unfold kappaM6First at h
  have hd : (d : ℚ) = 8 + A := by linarith
  exact_mod_cast hd

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.GA1A1A2_covariant
#print axioms HaagerupIzumi.C8.Theta.m6_first_hcancel_of_voa
#print axioms HaagerupIzumi.C8.Theta.m6_first_dimension_of_voa
