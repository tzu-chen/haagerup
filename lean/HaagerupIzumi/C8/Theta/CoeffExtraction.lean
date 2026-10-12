module

public import HaagerupIzumi.C8.Theta.ObstructionCoefficients

@[expose] public section

/-!
# Coefficient extraction: from `η⁸ δv = λ Θ_{H₁} + μ Θ_{H₂}` to `hcancel`

W6 plan item 4 (`Theta/W6_PLAN.md`) for the theta-only orientations of the proof of
Proposition `prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`): `M3First` (`L₇ ⊕ A₂`) and `M6First`
(`A₁ ⊕ A₁ ⊕ A₂`).

* `qcoeff_eq_lincomb`: if `∑ a_e q^e = l ∑ b_e q^e + m ∑ b'_e q^e` on `ℍ`, all three series
  supported on `λ + ℕ` and absolutely convergent at every height, then `a = l b + m b'`
  (from `qcoeff_eq_of_tsum_eq`).
* `lamOf G g = q(g) - ⌈q(g)⌉ ≤ 0`, a common support exponent for the coset `g + L`
  (`thetaCoeff_support_nat`).
* `hcancel_L7A2_of_eq`: the hypothesis `hcancel` of `m3_first_obstruction` follows from the
  functional identity `η⁸ δv_{(r,s)} = λ Θ_{H₁,(r,s)} + μ Θ_{H₂,(r,s)}` on `ℍ` (the output of
  `pole_cancellation`, componentwise), where the left side is written as the `q`-series of
  the VOA coefficients `δc r s e`.
* `thetaCoeff_cosetA1A1A2_swap`, `_conj`: the Table 3 coefficients are invariant under the
  interchange and the conjugation (coefficients of equal functions), so the projection
  `PThetaA1A1A2` equals the plain coefficient (`PThetaA1A1A2_eq`), and
  `hcancel_A1A1A2_of_eq` gives the hypothesis `hcancel` of `m6_first_obstruction`.

External (VOA-side) hypotheses, named in the statements: the functional identity `hfun`, the
support `hsupp` of the VOA coefficients on `λ + ℕ` (`λ = lamOf …`, i.e. conformal weights of the
module `(r, s)` shifted by `1/3 - c/24` are `≡ q(γ_{r,s}) (mod 1)`), and their absolute
convergence `hsum`.
-/

noncomputable section

open Complex
open scoped Real

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Uniqueness of coefficients of linear combinations -/

theorem norm_qterm_rat (c : ℂ) (e : ℚ) (τ : UpperHalfPlane) :
    ‖c * cexp (2 * π * I * (e : ℂ) * τ)‖ = ‖c‖ * Real.exp (-2 * π * (e : ℝ) * τ.im) := by
  have h := CharacterUniqueness.norm_qterm c (e : ℝ) τ
  rwa [Complex.ofReal_ratCast] at h

theorem summable_qseries_rat {b : ℚ → ℂ}
    (hb : ∀ y : ℝ, 0 < y → Summable fun e : ℚ => ‖b e‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (τ : UpperHalfPlane) : Summable fun e : ℚ => b e * cexp (2 * π * I * (e : ℂ) * τ) :=
  Summable.of_norm ((hb τ.im τ.im_pos).congr fun e => (norm_qterm_rat (b e) e τ).symm)

/-- **Coefficient extraction.**  `∑ a q^e = l ∑ b q^e + m ∑ b' q^e` on `ℍ`, with all three
supported on `λ + ℕ` and absolutely convergent at every height, forces `a = l b + m b'`. -/
theorem qcoeff_eq_lincomb (lam : ℚ) (a b b' : ℚ → ℚ) (l m : ℚ)
    (ha : ∀ e, a e ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lam)
    (hb : ∀ e, b e ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lam)
    (hb' : ∀ e, b' e ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lam)
    (hsa : ∀ y : ℝ, 0 < y →
      Summable fun e : ℚ => ‖((a e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hsb : ∀ y : ℝ, 0 < y →
      Summable fun e : ℚ => ‖((b e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hsb' : ∀ y : ℝ, 0 < y →
      Summable fun e : ℚ => ‖((b' e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (h : ∀ τ : UpperHalfPlane,
      ∑' e : ℚ, ((a e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) =
        (l : ℂ) * ∑' e : ℚ, ((b e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) +
          (m : ℂ) * ∑' e : ℚ, ((b' e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ)) :
    ∀ e, a e = l * b e + m * b' e := by
  set c : ℚ → ℚ := fun e => l * b e + m * b' e with hc
  have hcC : ∀ e, ((c e : ℚ) : ℂ) = (l : ℂ) * ((b e : ℚ) : ℂ) + (m : ℂ) * ((b' e : ℚ) : ℂ) :=
    fun e => by simp only [hc]; push_cast; ring
  have ha' : ∀ e, ((a e : ℚ) : ℂ) ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lam :=
    fun e he => ha e fun h0 => he (by rw [h0, Rat.cast_zero])
  have hc' : ∀ e, ((c e : ℚ) : ℂ) ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lam := by
    intro e he
    by_cases h1 : b e = 0
    · refine hb' e fun h2 => he ?_
      rw [hcC, h1, h2]
      simp
    · exact hb e h1
  have hsc : ∀ y : ℝ, 0 < y →
      Summable fun e : ℚ => ‖((c e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y) := by
    intro y hy
    refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_)
      (((hsb y hy).mul_left ‖(l : ℂ)‖).add ((hsb' y hy).mul_left ‖(m : ℂ)‖))
    rw [hcC]
    have hn : ‖(l : ℂ) * ((b e : ℚ) : ℂ) + (m : ℂ) * ((b' e : ℚ) : ℂ)‖ ≤
        ‖(l : ℂ)‖ * ‖((b e : ℚ) : ℂ)‖ + ‖(m : ℂ)‖ * ‖((b' e : ℚ) : ℂ)‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    calc ‖(l : ℂ) * ((b e : ℚ) : ℂ) + (m : ℂ) * ((b' e : ℚ) : ℂ)‖ *
          Real.exp (-2 * π * (e : ℝ) * y)
        ≤ (‖(l : ℂ)‖ * ‖((b e : ℚ) : ℂ)‖ + ‖(m : ℂ)‖ * ‖((b' e : ℚ) : ℂ)‖) *
          Real.exp (-2 * π * (e : ℝ) * y) :=
          mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
      _ = ‖(l : ℂ)‖ * (‖((b e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y)) +
          ‖(m : ℂ)‖ * (‖((b' e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y)) := by ring
  have h' : ∀ τ : UpperHalfPlane,
      ∑' e : ℚ, ((a e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) =
        ∑' e : ℚ, ((c e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) := by
    intro τ
    rw [h τ]
    have s1 := (summable_qseries_rat (b := fun e => ((b e : ℚ) : ℂ)) hsb τ).mul_left (l : ℂ)
    have s2 := (summable_qseries_rat (b := fun e => ((b' e : ℚ) : ℂ)) hsb' τ).mul_left (m : ℂ)
    rw [← tsum_mul_left, ← tsum_mul_left, ← s1.tsum_add s2]
    refine tsum_congr fun e => ?_
    rw [hcC]
    ring
  intro e
  have key := qcoeff_eq_of_tsum_eq lam (fun e => ((a e : ℚ) : ℂ)) (fun e => ((c e : ℚ) : ℂ))
    ha' hc' hsa hsc h' e
  exact_mod_cast key

/-! ## A common support exponent for a coset -/

/-- `λ(g) = q(g) - ⌈q(g)⌉ ∈ (-1, 0]`, congruent to the energy of the coset. -/
def lamOf (Gz : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) : ℚ := energy Gz g - ⌈energy Gz g⌉

theorem lamOf_nonpos (Gz : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) : lamOf Gz g ≤ 0 :=
  sub_nonpos.2 (Int.le_ceil _)

theorem lamOf_congr (Gz : Matrix (Fin 4) (Fin 4) ℤ) (g : Fin 4 → ℚ) :
    ∃ k : ℤ, lamOf Gz g = energy Gz g + k :=
  ⟨-⌈energy Gz g⌉, by rw [lamOf]; push_cast; ring⟩

/-! ## `M3First`: `hcancel` from the functional identity -/

theorem H1_eq_quadOf : H1 = quadOf MH1 := funext H1_eq_quad

theorem H2_eq_quadOf : H2 = quadOf MH2 := funext H2_eq_quad

theorem HA1A1A2_eq_quadOf : HA1A1A2 = quadOf MHA1A1A2 := funext HA1A1A2_eq_quad

theorem thetaCoeff_L7A2_support_lamOf (r s : ℤ) (H : (Fin 4 → ℚ) → ℚ) (e : ℚ)
    (h : thetaCoeff gramL7A2 (cosetL7A2 r s) H e ≠ 0) :
    ∃ n : ℕ, e = (n : ℚ) + lamOf gramL7A2 (cosetL7A2 r s) :=
  thetaCoeff_support_nat posDef_L7A2 even_L7A2 (ratVec_cosetL7A2_eq_inv r s) _
    (lamOf_nonpos _ _) (lamOf_congr _ _) H e h

/-- **`hcancel` of `m3_first_obstruction` from the functional identity.**  If, for every
coordinate `(r, s)`, the `q`-series of the VOA coefficients `δc r s e` (supported on
`λ + ℕ`, `λ = lamOf …`, absolutely convergent) equals `λ Θ_{H₁} + μ Θ_{H₂}` at that
coordinate on `ℍ`, then `δc r s e = λ [q^e] Θ_{H₁,(r,s)} + μ [q^e] Θ_{H₂,(r,s)}`. -/
theorem hcancel_L7A2_of_eq (δc : ℤ → ℤ → ℚ → ℚ) (lam mu : ℚ)
    (hsupp : ∀ r s e, δc r s e ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lamOf gramL7A2 (cosetL7A2 r s))
    (hsum : ∀ r s (y : ℝ), 0 < y →
      Summable fun e : ℚ => ‖((δc r s e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hfun : ∀ r s (τ : UpperHalfPlane),
      ∑' e : ℚ, ((δc r s e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) =
        (lam : ℂ) * thetaQL7A2 MH1 (modL7A2 r s) τ + (mu : ℂ) * thetaQL7A2 MH2 (modL7A2 r s) τ) :
    ∀ r s e, δc r s e = lam * thetaCoeff gramL7A2 (cosetL7A2 r s) H1 e +
      mu * thetaCoeff gramL7A2 (cosetL7A2 r s) H2 e := by
  intro r s
  rw [H1_eq_quadOf, H2_eq_quadOf]
  refine qcoeff_eq_lincomb _ _ _ _ lam mu (hsupp r s)
    (thetaCoeff_L7A2_support_lamOf r s _) (thetaCoeff_L7A2_support_lamOf r s _) (hsum r s)
    (fun y hy => summable_norm_thetaCoeff posDef_L7A2 MH1 _ hy)
    (fun y hy => summable_norm_thetaCoeff posDef_L7A2 MH2 _ hy) fun τ => ?_
  rw [hfun r s τ, thetaQL7A2_mod_eq_tsum MH1 r s τ.im_pos, thetaQL7A2_mod_eq_tsum MH2 r s τ.im_pos]

/-- **`m = 3`, first orientation, from the functional identity**: the dimension formula
`dim U₁ = 15 + A + 10B` from `η⁸ δv = λ Θ_{H₁} + μ Θ_{H₂}` on `ℍ` with the manuscript's
`λ, μ` (`lamM3First`, `muM3First`) and the vacuum coefficient. -/
theorem m3_first_obstruction_of_functional (δc : ℤ → ℤ → ℚ → ℚ) (A B d : ℕ)
    (hsupp : ∀ r s e, δc r s e ≠ 0 → ∃ n : ℕ, e = (n : ℚ) + lamOf gramL7A2 (cosetL7A2 r s))
    (hsum : ∀ r s (y : ℝ), 0 < y →
      Summable fun e : ℚ => ‖((δc r s e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hfun : ∀ r s (τ : UpperHalfPlane),
      ∑' e : ℚ, ((δc r s e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) =
        (lamM3First A B : ℂ) * thetaQL7A2 MH1 (modL7A2 r s) τ +
          (muM3First A B : ℂ) * thetaQL7A2 MH2 (modL7A2 r s) τ)
    (hvac : δc 0 0 1 = 2 * ((d : ℚ) - 22)) :
    d = 15 + A + 10 * B :=
  (m3_first_obstruction_of_defined δc A B d (hcancel_L7A2_of_eq δc _ _ hsupp hsum hfun)
    hvac).2.2

/-! ## `M6First`: symmetries of the coefficients and `hcancel` -/

theorem energy_cosetA1A1A2_swap (a b s : ℤ) :
    energy gramA1A1A2 (cosetA1A1A2 b a s) = energy gramA1A1A2 (cosetA1A1A2 a b s) := by
  simp only [energy, gramNorm_A1A1A2, cosetA1A1A2]
  simp
  ring

theorem energy_cosetA1A1A2_conj (a b s : ℤ) :
    energy gramA1A1A2 (cosetA1A1A2 a b (-s)) = energy gramA1A1A2 (cosetA1A1A2 a b s) := by
  simp only [energy, gramNorm_A1A1A2, cosetA1A1A2]
  simp
  ring

theorem thetaCoeff_A1A1A2_support_lamOf (a b s : ℤ) (H : (Fin 4 → ℚ) → ℚ) (e : ℚ)
    (h : thetaCoeff gramA1A1A2 (cosetA1A1A2 a b s) H e ≠ 0) :
    ∃ n : ℕ, e = (n : ℚ) + lamOf gramA1A1A2 (cosetA1A1A2 a b s) :=
  thetaCoeff_support_nat posDef_A1A1A2 even_A1A1A2 (ratVec_cosetA1A1A2_eq_inv a b s) _
    (lamOf_nonpos _ _) (lamOf_congr _ _) H e h

/-- Coefficients of two cosets with equal theta series and equal energy agree. -/
theorem thetaCoeff_A1A1A2_eq_of_eq {a b s a' b' s' : ℤ}
    (hE : energy gramA1A1A2 (cosetA1A1A2 a' b' s') = energy gramA1A1A2 (cosetA1A1A2 a b s))
    (hθ : ∀ τ : ℂ, thetaQA1A1A2 MHA1A1A2 (modA1A1A2 a' b' s') τ =
      thetaQA1A1A2 MHA1A1A2 (modA1A1A2 a b s) τ) (e : ℚ) :
    thetaCoeff gramA1A1A2 (cosetA1A1A2 a' b' s') HA1A1A2 e =
      thetaCoeff gramA1A1A2 (cosetA1A1A2 a b s) HA1A1A2 e := by
  have hlam : lamOf gramA1A1A2 (cosetA1A1A2 a' b' s') = lamOf gramA1A1A2 (cosetA1A1A2 a b s) := by
    rw [lamOf, lamOf, hE]
  rw [HA1A1A2_eq_quadOf]
  have key := qcoeff_eq_lincomb (lamOf gramA1A1A2 (cosetA1A1A2 a b s))
    (thetaCoeff gramA1A1A2 (cosetA1A1A2 a' b' s') (quadOf MHA1A1A2))
    (thetaCoeff gramA1A1A2 (cosetA1A1A2 a b s) (quadOf MHA1A1A2)) (fun _ => 0) 1 0
    (fun e he => hlam ▸ thetaCoeff_A1A1A2_support_lamOf a' b' s' _ e he)
    (thetaCoeff_A1A1A2_support_lamOf a b s _) (fun e he => absurd rfl he)
    (fun y hy => summable_norm_thetaCoeff posDef_A1A1A2 MHA1A1A2 _ hy)
    (fun y hy => summable_norm_thetaCoeff posDef_A1A1A2 MHA1A1A2 _ hy)
    (fun _ _ => by simp) (fun τ => by
      rw [← thetaQA1A1A2_mod_eq_tsum MHA1A1A2 a' b' s' τ.im_pos,
        ← thetaQA1A1A2_mod_eq_tsum MHA1A1A2 a b s τ.im_pos, hθ τ]
      simp) e
  rw [key]
  ring

theorem thetaCoeff_cosetA1A1A2_swap (a b s : ℤ) (e : ℚ) :
    thetaCoeff gramA1A1A2 (cosetA1A1A2 b a s) HA1A1A2 e =
      thetaCoeff gramA1A1A2 (cosetA1A1A2 a b s) HA1A1A2 e :=
  thetaCoeff_A1A1A2_eq_of_eq (energy_cosetA1A1A2_swap a b s) (fun τ => by
    rw [← latticeThetaQ_cosetA1A1A2, ← latticeThetaQ_cosetA1A1A2, thetaQ_cosetA1A1A2_swap]) e

theorem thetaCoeff_cosetA1A1A2_conj (a b s : ℤ) (e : ℚ) :
    thetaCoeff gramA1A1A2 (cosetA1A1A2 a b (-s)) HA1A1A2 e =
      thetaCoeff gramA1A1A2 (cosetA1A1A2 a b s) HA1A1A2 e :=
  thetaCoeff_A1A1A2_eq_of_eq (energy_cosetA1A1A2_conj a b s) (fun τ => by
    rw [← latticeThetaQ_cosetA1A1A2, ← latticeThetaQ_cosetA1A1A2, thetaQ_cosetA1A1A2_conj]) e

/-- The projection of Table 3 does not change the coefficients. -/
theorem PThetaA1A1A2_eq (a b s : ℤ) (e : ℚ) :
    PThetaA1A1A2 a b s e = thetaCoeff gramA1A1A2 (cosetA1A1A2 a b s) HA1A1A2 e := by
  simp only [PThetaA1A1A2, symA1A1A2]
  rw [thetaCoeff_cosetA1A1A2_swap a b s, thetaCoeff_cosetA1A1A2_conj a b s,
    thetaCoeff_cosetA1A1A2_conj b a s, thetaCoeff_cosetA1A1A2_swap a b s]
  ring

/-- **`hcancel` of `m6_first_obstruction` from the functional identity**
`η⁸ δv_{(ab,s)} = κ Θ_{H,(a,b,s)}` on `ℍ`. -/
theorem hcancel_A1A1A2_of_eq (δc : ℤ → ℤ → ℤ → ℚ → ℚ) (κ : ℚ)
    (hsupp : ∀ a b s e, δc a b s e ≠ 0 →
      ∃ n : ℕ, e = (n : ℚ) + lamOf gramA1A1A2 (cosetA1A1A2 a b s))
    (hsum : ∀ a b s (y : ℝ), 0 < y →
      Summable fun e : ℚ => ‖((δc a b s e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hfun : ∀ a b s (τ : UpperHalfPlane),
      ∑' e : ℚ, ((δc a b s e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) =
        (κ : ℂ) * thetaQA1A1A2 MHA1A1A2 (modA1A1A2 a b s) τ) :
    ∀ a b s e, δc a b s e = κ * PThetaA1A1A2 a b s e := by
  intro a b s e
  rw [PThetaA1A1A2_eq, HA1A1A2_eq_quadOf]
  have key := qcoeff_eq_lincomb (lamOf gramA1A1A2 (cosetA1A1A2 a b s)) (δc a b s)
    (thetaCoeff gramA1A1A2 (cosetA1A1A2 a b s) (quadOf MHA1A1A2)) (fun _ => 0) κ 0
    (hsupp a b s) (thetaCoeff_A1A1A2_support_lamOf a b s _) (fun e he => absurd rfl he)
    (hsum a b s) (fun y hy => summable_norm_thetaCoeff posDef_A1A1A2 MHA1A1A2 _ hy)
    (fun _ _ => by simp) (fun τ => by
      rw [hfun a b s τ, thetaQA1A1A2_mod_eq_tsum MHA1A1A2 a b s τ.im_pos]
      simp) e
  rw [key]
  ring

/-- **`m = 6`, first orientation, from the functional identity** with `κ = 8 - A`. -/
theorem m6_first_obstruction_of_functional (δc : ℤ → ℤ → ℤ → ℚ → ℚ) (A d : ℕ)
    (hsupp : ∀ a b s e, δc a b s e ≠ 0 →
      ∃ n : ℕ, e = (n : ℚ) + lamOf gramA1A1A2 (cosetA1A1A2 a b s))
    (hsum : ∀ a b s (y : ℝ), 0 < y →
      Summable fun e : ℚ => ‖((δc a b s e : ℚ) : ℂ)‖ * Real.exp (-2 * π * (e : ℝ) * y))
    (hfun : ∀ a b s (τ : UpperHalfPlane),
      ∑' e : ℚ, ((δc a b s e : ℚ) : ℂ) * cexp (2 * π * I * (e : ℂ) * τ) =
        (kappaM6First A : ℂ) * thetaQA1A1A2 MHA1A1A2 (modA1A1A2 a b s) τ)
    (hvac : δc 0 0 0 1 = 2 * ((d : ℚ) - 16)) :
    d = 8 + A :=
  (m6_first_obstruction_of_defined δc A d (hcancel_A1A1A2_of_eq δc _ hsupp hsum hfun) hvac).2

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.qcoeff_eq_lincomb
#print axioms HaagerupIzumi.C8.Theta.hcancel_L7A2_of_eq
#print axioms HaagerupIzumi.C8.Theta.m3_first_obstruction_of_functional
#print axioms HaagerupIzumi.C8.Theta.thetaCoeff_cosetA1A1A2_swap
#print axioms HaagerupIzumi.C8.Theta.PThetaA1A1A2_eq
#print axioms HaagerupIzumi.C8.Theta.hcancel_A1A1A2_of_eq
#print axioms HaagerupIzumi.C8.Theta.m6_first_obstruction_of_functional
