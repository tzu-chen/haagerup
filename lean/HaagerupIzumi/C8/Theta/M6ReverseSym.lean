module

public import HaagerupIzumi.C8.Theta.TableLinks
public import HaagerupIzumi.C8.Theta.EvenBlockDataSigns

@[expose] public section

/-!
# `m = 6`, reverse orientation, on the 6-dimensional swap-symmetric block

Table 4 (`G₆⁻`) of the proof of Proposition `prop:near-group-current-obstructions`
(lines 3742–3770 of `c8_expanded_20260929/haagerup_c8_expanded.tex`).  The manuscript's `m = 6`
representation is 6-dimensional: `(v₀, v_A, v_B)` tensored with the even pointed factor
(lines 3714–3720, 3762–3766), with `v_A` not split between the labels `(1,0)` and `(0,1)`.
`Theta/M6ReverseCancellation` used the 8-dimensional block of orbits under `-1` only; here the
block is the quotient by `-1` **and** the interchange `b ↔ c` of `G₆⁻` (the isometry `swapG6m`,
labels `(a, b, t) ↦ (b, a, t)`), indexed as for `A₁ ⊕ A₁ ⊕ A₂` by
`(ab, t) ∈ Fin 3 × Fin 2` (`ab ∈ {00, 10, 11}`), with representatives `ιA1A1A2` and orbit map
`πA1A1A2`.

* theta side (proved): orbit-constancy of `Θ_H/η⁸` and `F/η⁸` (`F = -6 D₂ Θ`) under the swap and
  `-1`; the reduced matrices `SθE6G6m`, `TθE6G6m`; covariance given `σ(S) = SθE6G6m`,
  `σ(T) = TθE6G6m`; no `σ`-invariant vector; the even-block `S`-matrix in closed form
  `SθE6G6m = -(1/√12) C₂₂ ⊗ C₃`, the same as for `A₁ ⊕ A₁ ⊕ A₂` (`SθE6G6m_eq`);
* `m6_reverse_hcancel_of_voa_sym`, `m6_reverse_dimension_of_voa_sym`: the capstones on this
  block (VOA side as named hypotheses, as in `Theta/M6ReverseCancellation`; the integer-label
  form is `m6_reverse_hcancel_table_of_voa` in `Theta/ObstructionsOfVoa`), with the polar
  coordinate `(ab, t) = (11, 1)` (the coset `-w/3 = (1,1,1)`) and the vacuum `(00, 0)`;
* `PFG6m_link_sym`, `PThetaG6m_link_sym`: the links to the Table 4 functions.

Nothing here is an external hypothesis; the VOA inputs are hypotheses of the capstones only.
-/

noncomputable section

open Complex Matrix ModularGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups Real Manifold

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Orbits under the swap and `-1` -/

theorem fin2_neg : ∀ a : Fin 2, -a = a := by
  decide

/-- Invariance under the swap and `-1` gives invariance on the `πA1A1A2`-orbits. -/
theorem orbit_inv_G6s {X : Type*} (Ψ : Fin 2 × Fin 2 × Fin 3 → X)
    (hsw : ∀ p, Ψ (p.2.1, p.1, p.2.2) = Ψ p) (hng : ∀ p, Ψ (-p.1, -p.2.1, -p.2.2) = Ψ p)
    (q : Fin 2 × Fin 2 × Fin 3) : Ψ (ιA1A1A2 (πA1A1A2 q)) = Ψ q := by
  have hcj : ∀ p : Fin 2 × Fin 2 × Fin 3, Ψ (p.1, p.2.1, -p.2.2) = Ψ p := fun p => by
    have h := hng p
    rwa [fin2_neg p.1, fin2_neg p.2.1] at h
  rcases orbit_A1A1A2 q with h | h | h | h <;> rw [h]
  · exact hsw q
  · exact hcj q
  · exact (hsw (q.1, q.2.1, -q.2.2)).trans (hcj q)

theorem thetaG6m_swap (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaG6m (p.2.1, p.1, p.2.2) τ = thetaG6m p τ := by
  show latticeTheta (gramR gramG6m)
      (ratVec (cosetG6m ((p.2.1 : ℕ) : ℤ) ((p.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ))) τ =
    latticeTheta (gramR gramG6m)
      (ratVec (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ))) τ
  rw [← swap_cosetG6m]
  exact latticeTheta_isometry iso_G6m.1 iso_G6m.1 (gramR_transpose_mul_mul iso_G6m.2.1) _ τ

theorem thetaQG6m_swap (p : Fin 2 × Fin 2 × Fin 3) (τ : ℂ) :
    thetaQG6m MHG6m (p.2.1, p.1, p.2.2) τ = thetaQG6m MHG6m p τ :=
  thetaQ_cosetG6m_swap ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ) τ

theorem FG6m_sym_const (τ : ℍ) (q : Fin 2 × Fin 2 × Fin 3) :
    FG6m MHG6m τ q = FG6m MHG6m τ (ιA1A1A2 (πA1A1A2 q)) :=
  (orbit_inv_G6s (fun p => FG6m MHG6m τ p)
    (fun p => by
      show thetaQG6m MHG6m (p.2.1, p.1, p.2.2) τ / eta8 τ = thetaQG6m MHG6m p τ / eta8 τ
      rw [thetaQG6m_swap])
    (fun p => by
      show thetaQG6m MHG6m (-p.1, -p.2.1, -p.2.2) τ / eta8 τ = thetaQG6m MHG6m p τ / eta8 τ
      rw [thetaQG6m_neg]) q).symm

theorem FFG6m_sym_const (τ : ℍ) (q : Fin 2 × Fin 2 × Fin 3) :
    FFG6m τ q = FFG6m τ (ιA1A1A2 (πA1A1A2 q)) :=
  (orbit_inv_G6s (fun p => FFG6m τ p)
    (fun p => by
      have hθ : θG6m (p.2.1, p.1, p.2.2) = θG6m p := funext fun τ => thetaG6m_swap p τ
      show -6 * Derivative.serreDerivative 2 (θG6m (p.2.1, p.1, p.2.2)) τ / eta8 τ =
        -6 * Derivative.serreDerivative 2 (θG6m p) τ / eta8 τ
      rw [hθ])
    (fun p => by
      have hθ : θG6m (-p.1, -p.2.1, -p.2.2) = θG6m p := funext fun τ => thetaG6m_neg p τ
      show -6 * Derivative.serreDerivative 2 (θG6m (-p.1, -p.2.1, -p.2.2)) τ / eta8 τ =
        -6 * Derivative.serreDerivative 2 (θG6m p) τ / eta8 τ
      rw [hθ]) q).symm

/-! ## The 6-dimensional block -/

/-- `Θ_H/η⁸` on the swap-symmetric block. -/
def FE6G6m (τ : ℍ) : Fin 3 × Fin 2 → ℂ := fun e => FG6m MHG6m τ (ιA1A1A2 e)

/-- `F/η⁸`, `F = -6 D₂ Θ`, on the swap-symmetric block. -/
def FFE6G6m (τ : ℍ) : Fin 3 × Fin 2 → ℂ := fun e => FFG6m τ (ιA1A1A2 e)

def SθE6G6m : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ := reduceMat ιA1A1A2 πA1A1A2 SθG6m

def TθE6G6m : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ :=
  Matrix.diagonal fun e => eChar (eG6m (ιA1A1A2 e) - 1 / 3)

theorem FE6G6m_covariant (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθE6G6m) (hσT : (σ T : Matrix _ _ ℂ) = TθE6G6m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FE6G6m (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FE6G6m τ :=
  covariant_of_S_T σ FE6G6m
    (fun τ => by
      rw [hσS]
      exact reduced_S (FG6m MHG6m) SθG6m ιA1A1A2 πA1A1A2
        (FG6m_S harmonic_quadratics.2.2.2.2.2) FG6m_sym_const τ)
    (fun τ => by
      rw [hσT]
      exact reduced_T (FG6m MHG6m) (fun p => eG6m p - 1 / 3) ιA1A1A2 (FG6m_T MHG6m) τ)

theorem FFE6G6m_covariant (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθE6G6m) (hσT : (σ T : Matrix _ _ ℂ) = TθE6G6m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), FFE6G6m (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ FFE6G6m τ :=
  covariant_of_S_T σ FFE6G6m
    (fun τ => by
      rw [hσS]
      exact reduced_S FFG6m SθG6m ιA1A1A2 πA1A1A2 FFG6m_S FFG6m_sym_const τ)
    (fun τ => by
      rw [hσT]
      exact reduced_T FFG6m (fun p => eG6m p - 1 / 3) ιA1A1A2 FFG6m_T τ)

theorem noInvariantE6_G6m (v : Fin 3 × Fin 2 → ℂ) (_hS : SθE6G6m *ᵥ v = v)
    (hT : TθE6G6m *ᵥ v = v) : v = 0 :=
  funext fun e => supp_of_T_fixed (fun e => eG6m (ιA1A1A2 e) - 1 / 3) v hT e
    (eChar_ne_one_of_den (eG6m_sub _) (tfixed_G6m _))

/-- **`hinv` of `pole_cancellation`** on the swap-symmetric block of `G₆⁻`. -/
theorem noInvariantE6_sigma_G6m (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθE6G6m) (hσT : (σ T : Matrix _ _ ℂ) = TθE6G6m) :
    ∀ v : Fin 3 × Fin 2 → ℂ, (∀ γ, (σ γ : Matrix _ _ ℂ) *ᵥ v = v) → v = 0 :=
  noInvariant_sigma σ _ _ hσS hσT noInvariantE6_G6m

/-- The coset of the label `e` of the swap-symmetric block. -/
abbrev cosetE6G6m (e : Fin 3 × Fin 2) : Fin 4 → ℚ :=
  cosetG6m (((ιA1A1A2 e).1 : ℕ) : ℤ) (((ιA1A1A2 e).2.1 : ℕ) : ℤ) (((ιA1A1A2 e).2.2 : ℕ) : ℤ)

theorem F_G6s_qexp (e : Fin 3 × Fin 2) (τ : ℍ) :
    -6 * Derivative.serreDerivative 2 (θG6m (ιA1A1A2 e)) τ = ∑' x : ℚ,
      ((minusSixD2Coeff (thetaCount gramG6m (cosetE6G6m e)) x : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * τ) :=
  minusSixSerre_theta_qexp posDef_G6m even_G6m (ratVec_cosetG6m_eq_inv _ _ _) τ

theorem H_G6s_qexp (e : Fin 3 × Fin 2) {τ : ℂ} (hτ : 0 < τ.im) :
    thetaQG6m MHG6m (ιA1A1A2 e) τ = ∑' x : ℚ,
      ((thetaCoeff gramG6m (cosetE6G6m e) (quadOf MHG6m) x : ℚ) : ℂ) *
        cexp (2 * π * I * (x : ℂ) * τ) :=
  latticeThetaQ_eq_tsum_thetaCoeff posDef_G6m MHG6m _ hτ

/-- The theta side `φ F + κ Θ_H` (divided by `η⁸`) on the swap-symmetric block. -/
def GG6s (φ κ : ℚ) (τ : ℍ) : Fin 3 × Fin 2 → ℂ :=
  (φ : ℂ) • FFE6G6m τ + (κ : ℂ) • FE6G6m τ

theorem GG6s_apply (φ κ : ℚ) (τ : ℍ) (e : Fin 3 × Fin 2) :
    GG6s φ κ τ e = ((φ : ℂ) * (-6 * Derivative.serreDerivative 2 (θG6m (ιA1A1A2 e)) τ) +
      (κ : ℂ) * thetaQG6m MHG6m (ιA1A1A2 e) τ) / eta8 τ := by
  simp only [GG6s, FFE6G6m, FFG6m, FE6G6m, FG6m, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem GG6s_covariant (φ κ : ℚ)
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ)
    (hσS : (σ S : Matrix _ _ ℂ) = SθE6G6m) (hσT : (σ T : Matrix _ _ ℂ) = TθE6G6m) :
    ∀ (γ : SL(2, ℤ)) (τ : ℍ), GG6s φ κ (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ GG6s φ κ τ := by
  intro γ τ
  rw [GG6s, GG6s, FFE6G6m_covariant σ hσS hσT γ τ, FE6G6m_covariant σ hσS hσT γ τ, mulVec_add,
    mulVec_smul, mulVec_smul]

theorem mdifferentiable_GG6s (φ κ : ℚ) (e : Fin 3 × Fin 2) :
    MDiff (fun τ : ℍ => GG6s φ κ τ e) := by
  have hF : MDiff (fun τ : ℍ => FFE6G6m τ e) := by
    have h1 : MDiff (fun τ : ℍ => -6 * Derivative.serreDerivative 2 (θG6m (ιA1A1A2 e)) τ) :=
      (Derivative.serreDerivative_mdifferentiable 2
        (mdifferentiable_θG6m (ιA1A1A2 e))).const_smul (-6 : ℂ)
    exact mdifferentiable_div_eta8_ℍ h1
  have h := (hF.const_smul (φ : ℂ)).add
    ((mdifferentiable_FG6m MHG6m (ιA1A1A2 e)).const_smul (κ : ℂ))
  convert h using 1
  funext τ
  rfl

theorem ι_polar_G6s (e : Fin 3 × Fin 2) (x : ℚ)
    (h : (ιA1A1A2 e = (0, 0, 0) ∧ x = 0) ∨
      ((ιA1A1A2 e = (1, 1, 1) ∨ ιA1A1A2 e = (1, 1, 2)) ∧ x = 1 / 6)) :
    (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 1 / 6) := by
  have hι : ∀ e : Fin 3 × Fin 2, (ιA1A1A2 e = (0, 0, 0) → e = (0, 0)) ∧
      (ιA1A1A2 e = (1, 1, 1) → e = (2, 1)) ∧ ιA1A1A2 e ≠ (1, 1, 2) := by
    decide +kernel
  obtain ⟨h0, h1, h2⟩ := hι e
  rcases h with ⟨ha, hb⟩ | ⟨ha | ha, hb⟩
  · exact Or.inl ⟨h0 ha, hb⟩
  · exact Or.inr ⟨h1 ha, hb⟩
  · exact absurd ha h2

theorem support_lamOf_G6s (e : Fin 3 × Fin 2) (H : (Fin 4 → ℚ) → ℚ) (x : ℚ)
    (h : thetaCoeff gramG6m (cosetE6G6m e) H x ≠ 0) :
    ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetE6G6m e) :=
  thetaCoeff_support_nat posDef_G6m even_G6m (ratVec_cosetG6m_eq_inv _ _ _) _
    (lamOf_nonpos _ _) (lamOf_congr _ _) H x h

/-! ## The capstones on the 6-dimensional block -/

/-- **`m = 6`, reverse orientation, from pole cancellation**, on the swap-symmetric block. -/
theorem m6_reverse_hcancel_of_voa_sym
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθE6G6m) (hσT : (σ T : Matrix _ _ ℂ) = TθE6G6m)
    (V : ℍ → Fin 3 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 3 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetE6G6m e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (P : ℕ) (hvac0 : δc (0, 0) 0 = 1) (hpolar : δc (2, 1) (1 / 6) = -(P : ℚ))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 → (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 1 / 6)) :
    ∀ e x, δc e x = phiM6Reverse * minusSixD2Coeff (thetaCount gramG6m (cosetE6G6m e)) x +
      kappaM6Reverse P * thetaCoeff gramG6m (cosetE6G6m e) (quadOf MHG6m) x := by
  set φ := phiM6Reverse with hφ
  set κ := kappaM6Reverse P with hκ
  have hsuppF : ∀ e x, minusSixD2Coeff (thetaCount gramG6m (cosetE6G6m e)) x ≠ 0 →
      ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetE6G6m e) := fun e x h =>
    support_minusSix posDef_G6m even_G6m (ratVec_cosetG6m_eq_inv _ _ _) x h
  have hrem : ∀ e x, x < 1 / 3 →
      δc e x - φ * minusSixD2Coeff (thetaCount gramG6m (cosetE6G6m e)) x -
        κ * thetaCoeff gramG6m (cosetE6G6m e) (quadOf MHG6m) x = 0 := by
    intro e x hx
    by_contra hne
    have hx1 : x < 1 := by linarith
    have hcases : (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 1 / 6) := by
      by_cases hd : δc e x = 0
      · have ht : thetaCount gramG6m (cosetE6G6m e) x ≠ 0 ∨
            thetaCoeff gramG6m (cosetE6G6m e) (quadOf MHG6m) x ≠ 0 := by
          by_contra hcon
          push Not at hcon
          apply hne
          rw [hd, minusSixD2Coeff_of_lt_one _ hx1, hcon.1, hcon.2]
          ring
        rcases ht with ht | ht
        · exact ι_polar_G6s e x (polar_G6m (ιA1A1A2 e) hx ht)
        · exact ι_polar_G6s e x (polar_G6m (ιA1A1A2 e) hx ht)
      · exact hother e x hx hd
    apply hne
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hc : cosetE6G6m (0, 0) = 0 := by decide +kernel
      rw [minusSixD2Coeff_of_lt_one _ (by norm_num), hc, count_G6m_vac0,
        thetaCoeff_at_zero posDef_G6m _ (quadOf_zero MHG6m), hvac0, hφ, phiM6Reverse]
      ring
    · have hc : cosetE6G6m (2, 1) = cosetG6m 1 1 1 := by decide +kernel
      rw [minusSixD2Coeff_of_lt_one _ (by norm_num), hc, thetaCoeff_polarG6m_eq,
        ← funext HG6m_eq_quad, H_G6m_polar, hpolar, hκ, kappaM6Reverse]
      ring
  have hdiff : ∀ e (τ : ℍ), V τ e - GG6s φ κ τ e =
      (∑' x : ℚ, (((δc e x : ℚ) : ℂ) -
        (φ : ℂ) * ((minusSixD2Coeff (thetaCount gramG6m (cosetE6G6m e)) x : ℚ) : ℂ) -
        (κ : ℂ) * ((thetaCoeff gramG6m (cosetE6G6m e) (quadOf MHG6m) x : ℚ) : ℂ)) *
          cexp (2 * π * I * (x : ℂ) * τ)) / eta8 τ := by
    intro e τ
    have hη := eta8_ne_zero τ.im_pos
    have key := tsum_sub_lincomb (fun x => ((δc e x : ℚ) : ℂ))
      (fun x => ((minusSixD2Coeff (thetaCount gramG6m (cosetE6G6m e)) x : ℚ) : ℂ))
      (fun x => ((thetaCoeff gramG6m (cosetE6G6m e) (quadOf MHG6m) x : ℚ) : ℂ)) (φ : ℂ) (κ : ℂ)
      (hsum e)
      (fun y hy => summable_norm_minusSixD2Coeff posDef_G6m even_G6m
        (ratVec_cosetG6m_eq_inv _ _ _) hy)
      (fun y hy => summable_norm_thetaCoeff posDef_G6m MHG6m _ hy) τ
    rw [← key, ← hVq e τ, ← F_G6s_qexp e τ, ← H_G6s_qexp e τ.im_pos, GG6s_apply, eq_div_iff hη,
      sub_mul, div_mul_cancel₀ _ hη]
    ring
  have hpp : ∀ e, UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ => V τ e - GG6s φ κ τ e) := by
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
    have h0' : (((δc e x - φ * minusSixD2Coeff (thetaCount gramG6m (cosetE6G6m e)) x -
        κ * thetaCoeff gramG6m (cosetE6G6m e) (quadOf MHG6m) x : ℚ)) : ℂ) = 0 := by
      rw [h0, Rat.cast_zero]
    push_cast at h0'
    exact h0'
  have hVG : V = GG6s φ κ :=
    pole_cancellation σ hfin (noInvariantE6_sigma_G6m σ hσS hσT) V (GG6s φ κ) hVhol
      (mdifferentiable_GG6s φ κ) hVcov (GG6s_covariant φ κ σ hσS hσT) hpp
  intro e
  refine qcoeff_eq_lincomb (lamOf gramG6m (cosetE6G6m e)) (δc e) _ _ φ κ (hsupp e)
    (hsuppF e) (support_lamOf_G6s e _) (hsum e)
    (fun y hy => summable_norm_minusSixD2Coeff posDef_G6m even_G6m
      (ratVec_cosetG6m_eq_inv _ _ _) hy)
    (fun y hy => summable_norm_thetaCoeff posDef_G6m MHG6m _ hy) fun τ => ?_
  have hη := eta8_ne_zero τ.im_pos
  rw [← hVq e τ, hVG, GG6s_apply, ← F_G6s_qexp e τ, ← H_G6s_qexp e τ.im_pos,
    mul_div_cancel₀ _ hη]

/-- **`m = 6`, reverse orientation: `dim U₁ = 5 + 12P`**, on the swap-symmetric block. -/
theorem m6_reverse_dimension_of_voa_sym
    (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ) (hfin : (Set.range σ).Finite)
    (hσS : (σ S : Matrix _ _ ℂ) = SθE6G6m) (hσT : (σ T : Matrix _ _ ℂ) = TθE6G6m)
    (V : ℍ → Fin 3 × Fin 2 → ℂ) (hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e))
    (hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ)
    (δc : Fin 3 × Fin 2 → ℚ → ℚ)
    (hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
      ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ))
    (hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetE6G6m e))
    (hsum : ∀ e (y : ℝ), 0 < y →
      Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y))
    (P d : ℕ) (hvac0 : δc (0, 0) 0 = 1) (hpolar : δc (2, 1) (1 / 6) = -(P : ℚ))
    (hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 → (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 1 / 6))
    (hvac1 : δc (0, 0) 1 = 2 * (d : ℚ) - 94) :
    d = 5 + 12 * P := by
  have h := m6_reverse_hcancel_of_voa_sym σ hfin hσS hσT V hVhol hVcov δc hVq hsupp hsum P hvac0
    hpolar hother (0, 0) 1
  have hc : cosetE6G6m (0, 0) = 0 := by decide +kernel
  rw [hc, minusSixD2Coeff_one, count_G6m_vac1, count_G6m_vac0, ← funext HG6m_eq_quad,
    H_G6m_vac1, hvac1, phiM6Reverse, kappaM6Reverse] at h
  have hd : (d : ℚ) = 5 + 12 * P := by linarith
  exact_mod_cast hd

/-! ## Links to the Table 4 functions -/

/-- Equal theta series and congruent energies give equal coefficient counts. -/
theorem thetaCount_congr_of_latticeTheta {Gz : Matrix (Fin 4) (Fin 4) ℤ}
    (hG : (gramR Gz).PosDef) (hEven : ∀ m : Fin 4 → ℤ, Even (m ⬝ᵥ (Gz *ᵥ m)))
    {g g' : Fin 4 → ℚ} {s s' : Fin 4 → ℤ} (hg : ratVec g = (gramR Gz)⁻¹ *ᵥ intVec s)
    (hg' : ratVec g' = (gramR Gz)⁻¹ *ᵥ intVec s')
    (hfr : Int.fract (energy Gz g) = Int.fract (energy Gz g'))
    (hθ : ∀ τ : ℂ, 0 < τ.im →
      latticeTheta (gramR Gz) (ratVec g) τ = latticeTheta (gramR Gz) (ratVec g') τ) (x : ℚ) :
    thetaCount Gz g x = thetaCount Gz g' x := by
  have key := qcoeff_eq_lincomb (Int.fract (energy Gz g)) (thetaCount Gz g) (thetaCount Gz g')
    (fun _ => 0) 1 0
    (fun y hy => thetaCoeff_support_fract hG hEven hg hy)
    (fun y hy => by rw [hfr]; exact thetaCoeff_support_fract hG hEven hg' hy)
    (fun y hy => absurd rfl hy)
    (fun y hy => summable_norm_thetaCount hG g hy)
    (fun y hy => summable_norm_thetaCount hG g' hy) (fun _ _ => by simp)
    (fun τ => by
      rw [← latticeTheta_eq_tsum_thetaCount hG g τ.im_pos,
        ← latticeTheta_eq_tsum_thetaCount hG g' τ.im_pos, hθ τ τ.im_pos]
      simp) x
  rw [key]
  ring

theorem energy_cosetG6m_swap (a b t : ℤ) :
    energy gramG6m (cosetG6m b a t) = energy gramG6m (cosetG6m a b t) := by
  have h1 := qf_gramR_ratVec_eq_energy gramG6m (cosetG6m b a t)
  have h2 := qf_gramR_ratVec_eq_energy gramG6m (cosetG6m a b t)
  rw [← swap_cosetG6m, qf_mulVec, gramR_transpose_mul_mul iso_G6m.2.1] at h1
  have h3 : ((energy gramG6m (cosetG6m b a t) : ℚ) : ℝ) =
      ((energy gramG6m (cosetG6m a b t) : ℚ) : ℝ) := by linarith
  exact Rat.cast_injective h3

theorem thetaCount_cosetG6m_swap (a b t : ℤ) :
    thetaCount gramG6m (cosetG6m b a t) = thetaCount gramG6m (cosetG6m a b t) :=
  funext fun x => thetaCount_congr_of_latticeTheta posDef_G6m even_G6m
    (ratVec_cosetG6m_eq_inv b a t) (ratVec_cosetG6m_eq_inv a b t)
    (by rw [energy_cosetG6m_swap])
    (fun τ _ => by
      rw [← swap_cosetG6m]
      exact latticeTheta_isometry iso_G6m.1 iso_G6m.1 (gramR_transpose_mul_mul iso_G6m.2.1) _ τ)
    x

theorem thetaCoeff_cosetG6m_swap' (a b t : ℤ) (x : ℚ) :
    thetaCoeff gramG6m (cosetG6m b a t) (quadOf MHG6m) x =
      thetaCoeff gramG6m (cosetG6m a b t) (quadOf MHG6m) x :=
  thetaCoeff_congr_of_latticeThetaQ posDef_G6m even_G6m (ratVec_cosetG6m_eq_inv b a t)
    (ratVec_cosetG6m_eq_inv a b t) (by rw [energy_cosetG6m_swap]) MHG6m
    (fun τ _ => thetaQ_cosetG6m_swap a b t τ) x

/-- The `±` projection of Table 4 at a coset `cosetG6m p + n` is the value at the
representative of `p` in the swap-symmetric block. -/
theorem avgNeg_link_G6s (Φ : (Fin 4 → ℚ) → ℚ) (htr : ∀ g n, Φ (cosetPt g n) = Φ g)
    (hneg : ∀ g, Φ (-g) = Φ g) (hswap : ∀ a b t, Φ (cosetG6m b a t) = Φ (cosetG6m a b t))
    (p : Fin 2 × Fin 2 × Fin 3) (n : Fin 4 → ℤ) :
    avgNeg Φ (cosetPt (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) n) =
      Φ (cosetE6G6m (πA1A1A2 p)) := by
  have hmod : ∀ a b t : ℤ, Φ (cosetG6m a b t) =
      Φ (cosetG6m (((modG6m a b t).1 : ℕ) : ℤ) (((modG6m a b t).2.1 : ℕ) : ℤ)
        (((modG6m a b t).2.2 : ℕ) : ℤ)) :=
    fun a b t => by rw [cosetG6m_mod a b t, htr]
  rw [avgNeg, hneg, htr, add_self_div_two]
  exact (orbit_inv_G6s (fun q => Φ (cosetG6m ((q.1 : ℕ) : ℤ) ((q.2.1 : ℕ) : ℤ) ((q.2.2 : ℕ) : ℤ)))
    (fun q => hswap ((q.1 : ℕ) : ℤ) ((q.2.1 : ℕ) : ℤ) ((q.2.2 : ℕ) : ℤ))
    (fun q => by
      rw [← modG6m_neg q, ← hmod, cosetG6m_neg, hneg]) p).symm

/-- **Link, Table 4, `F`**, swap-symmetric block. -/
theorem PFG6m_link_sym {g : Fin 4 → ℚ} {p : Fin 2 × Fin 2 × Fin 3} {n : Fin 4 → ℤ}
    (hg : g = cosetPt (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) n)
    (x : ℚ) : PFG6m g x = minusSixD2Coeff (thetaCount gramG6m (cosetE6G6m (πA1A1A2 p))) x := by
  rw [PFG6m, hg]
  exact avgNeg_link_G6s (fun g => minusSixD2Coeff (thetaCount gramG6m g) x)
    (fun g n => minusSix_cosetPt gramG6m g n x) (fun g => minusSix_neg gramG6m g x)
    (fun a b t => by
      show minusSixD2Coeff (thetaCount gramG6m (cosetG6m b a t)) x =
        minusSixD2Coeff (thetaCount gramG6m (cosetG6m a b t)) x
      rw [thetaCount_cosetG6m_swap]) p n

/-- **Link, Table 4, `Θ_H`**, swap-symmetric block. -/
theorem PThetaG6m_link_sym {g : Fin 4 → ℚ} {p : Fin 2 × Fin 2 × Fin 3} {n : Fin 4 → ℤ}
    (hg : g = cosetPt (cosetG6m ((p.1 : ℕ) : ℤ) ((p.2.1 : ℕ) : ℤ) ((p.2.2 : ℕ) : ℤ)) n)
    (x : ℚ) :
    PThetaG6m g x = thetaCoeff gramG6m (cosetE6G6m (πA1A1A2 p)) (quadOf MHG6m) x := by
  have hH : HG6m = quadOf MHG6m := funext HG6m_eq_quad
  rw [PThetaG6m, hg, hH]
  exact avgNeg_link_G6s (fun g => thetaCoeff gramG6m g (quadOf MHG6m) x)
    (fun g n => thetaCoeff_cosetPt _ g n _ x)
    (fun g => thetaCoeff_neg _ g _ (quadOf_neg MHG6m) x)
    (fun a b t => thetaCoeff_cosetG6m_swap' a b t x) p n

/-! ## The `S`-block in closed form -/

/-- `6 s(γ, δ) ≡ 3(aa' + bb') + 4tx (mod 6)` at `δ = (a', b', -x)`, any `γ = (a, b, t)`
(kernel-checked). -/
theorem sG6m_gen_data : ∀ (p : Fin 2 × Fin 2 × Fin 3) (a' b' : Fin 2) (x : Fin 3),
    (6 : ℤ) ∣ (9 * ((p.1 : ℕ) : ℤ) * ((a' : ℕ) : ℤ) + 9 * ((p.2.1 : ℕ) : ℤ) * ((b' : ℕ) : ℤ) +
      8 * ((p.2.2 : ℕ) : ℤ) * (((-x : Fin 3) : ℕ) : ℤ) +
      6 * (((p.1 : ℕ) : ℤ) * ((b' : ℕ) : ℤ) + ((p.2.1 : ℕ) : ℤ) * ((a' : ℕ) : ℤ)) -
      6 * (((p.1 : ℕ) : ℤ) * (((-x : Fin 3) : ℕ) : ℤ) + ((p.2.2 : ℕ) : ℤ) * ((a' : ℕ) : ℤ)) -
      6 * (((p.2.1 : ℕ) : ℤ) * (((-x : Fin 3) : ℕ) : ℤ) + ((p.2.2 : ℕ) : ℤ) * ((b' : ℕ) : ℤ))) -
      3 * (((p.1 : ℕ) : ℤ) * ((a' : ℕ) : ℤ) + ((p.2.1 : ℕ) : ℤ) * ((b' : ℕ) : ℤ)) -
      4 * ((p.2.2 : ℕ) : ℤ) * ((x : ℕ) : ℤ) := by
  decide +kernel

theorem eChar_sG6m_gen (p : Fin 2 × Fin 2 × Fin 3) (a' b' : Fin 2) (x : Fin 3) :
    eChar (-sG6m p (a', b', -x)) =
      (-1 : ℂ) ^ ((p.1 : ℕ) * (a' : ℕ) + (p.2.1 : ℕ) * (b' : ℕ)) *
        eChar (-(2 * ((p.2.2 : ℕ) : ℝ) * ((x : ℕ) : ℝ) / 3)) := by
  obtain ⟨c, hc⟩ := sG6m_gen_data p a' b' x
  have hc' : (9 * ((p.1 : ℕ) : ℝ) * ((a' : ℕ) : ℝ) + 9 * ((p.2.1 : ℕ) : ℝ) * ((b' : ℕ) : ℝ) +
      8 * ((p.2.2 : ℕ) : ℝ) * (((-x : Fin 3) : ℕ) : ℝ) +
      6 * (((p.1 : ℕ) : ℝ) * ((b' : ℕ) : ℝ) + ((p.2.1 : ℕ) : ℝ) * ((a' : ℕ) : ℝ)) -
      6 * (((p.1 : ℕ) : ℝ) * (((-x : Fin 3) : ℕ) : ℝ) + ((p.2.2 : ℕ) : ℝ) * ((a' : ℕ) : ℝ)) -
      6 * (((p.2.1 : ℕ) : ℝ) * (((-x : Fin 3) : ℕ) : ℝ) + ((p.2.2 : ℕ) : ℝ) * ((b' : ℕ) : ℝ))) -
      3 * (((p.1 : ℕ) : ℝ) * ((a' : ℕ) : ℝ) + ((p.2.1 : ℕ) : ℝ) * ((b' : ℕ) : ℝ)) -
      4 * ((p.2.2 : ℕ) : ℝ) * ((x : ℕ) : ℝ) = 6 * (c : ℝ) := by
    exact_mod_cast hc
  rw [← eChar_neg_half_nat, ← eChar_add]
  refine eChar_eq_of_sub_eq_int (-c) ?_
  simp only [sG6m]
  push_cast
  linear_combination (-1 / 6 : ℝ) * hc'

theorem filter_πA1A1A2_image_neg : ∀ e' : Fin 3 × Fin 2,
    (Finset.univ.filter fun q : Fin 2 × Fin 2 × Fin 3 => πA1A1A2 q = e') =
      (O2 e'.1 ×ˢ R3 e'.2).image (fun y : (Fin 2 × Fin 2) × Fin 3 => (y.1.1, y.1.2, -y.2)) := by
  decide +kernel

/-- **The `S`-block of `G₆⁻` on the swap-symmetric block**: `-(1/√12) C₂₂(ab, ab') C₃(t, t')`. -/
theorem SθE6G6m_eq (e e' : Fin 3 × Fin 2) :
    SθE6G6m e e' =
      -(((Real.sqrt 12)⁻¹ : ℝ) : ℂ) * (((c22 e.1 e'.1 : ℤ) : ℂ) * ((c3 e.2 e'.2 : ℝ) : ℂ)) := by
  have hval : (((ιA1A1A2 e).2.2 : Fin 3) : ℕ) = (e.2 : ℕ) := rfl
  show (∑ q ∈ Finset.univ.filter fun q => πA1A1A2 q = e', SθG6m (ιA1A1A2 e) q) = _
  rw [filter_πA1A1A2_image_neg e', Finset.sum_image (fun x _ y _ h => by
      simp only [Prod.mk.injEq, neg_inj] at h
      exact Prod.ext (Prod.ext h.1 h.2.1) h.2.2),
    Finset.sum_product, ← sum_R3 e.2 e'.2, ← sum_O2 e e'.1, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [SθG6m, Matrix.of_apply]
  rw [eChar_sG6m_gen (ιA1A1A2 e) u.1 u.2 x, hval]

/-- The `S`-blocks of `G₆⁻` (swap-symmetric) and `A₁ ⊕ A₁ ⊕ A₂` coincide. -/
theorem SθE6G6m_eq_SθEA1A1A2 : SθE6G6m = SθEA1A1A2 := by
  ext e e'
  rw [SθE6G6m_eq, SθEA1A1A2_eq]

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.FE6G6m_covariant
#print axioms HaagerupIzumi.C8.Theta.FFE6G6m_covariant
#print axioms HaagerupIzumi.C8.Theta.noInvariantE6_sigma_G6m
#print axioms HaagerupIzumi.C8.Theta.m6_reverse_hcancel_of_voa_sym
#print axioms HaagerupIzumi.C8.Theta.m6_reverse_dimension_of_voa_sym
#print axioms HaagerupIzumi.C8.Theta.PFG6m_link_sym
#print axioms HaagerupIzumi.C8.Theta.PThetaG6m_link_sym
#print axioms HaagerupIzumi.C8.Theta.SθE6G6m_eq
#print axioms HaagerupIzumi.C8.Theta.SθE6G6m_eq_SθEA1A1A2
