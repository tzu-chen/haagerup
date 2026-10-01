module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Arithmetic of Lemma `lem:rank6-induction`

Lines 3828–3914 of `c8_expanded_20260929/haagerup_c8_expanded.tex`.

With `d² = 3md + 1` and `s = 1 + d²`:

* `rank6_induction_dims` — the forgetful images `F(X) = 1 + mR`,
  `F(Y) = 2·1 + mR`, `F(C_j) = a + a² + mR` (with `FPdim R = 3d`) have dimensions
  `d²`, `s`, `s`, and `FPdim I(1) = 1 + d_X + 2 d_Y = 3s = Dim 𝓕`.
* `rank6_indicator_first`, `rank6_indicator_second` — eq:indicator-first and
  eq:indicator-second.  The external input is the Ng–Schauenburg twist-trace
  formula for `I(ρ) = mX + mY + m(C₀+C₁+C₂) + ∑ n_j Z_j` (with
  `d_{Z_j} = 3d n_j`): the hypotheses `htrace1`, `htrace2` say
  `∑ [I(ρ):Z] d_Z θ_Z = Dim 𝓕 · ν₁(ρ) = 0` and
  `∑ [I(ρ):Z] d_Z θ_Z² = Dim 𝓕 · ν₂(ρ) = 3sε`, where `S₁ = ∑ n_j² θ_j` and
  `S₂ = ∑ n_j² θ_j²`.  We prove `S₁ = m² - md` and
  `S₂ = m² - md + ε(2d - 3m)`; for `d = (3m + √Δ)/2` these are
  `-(m² + m√Δ)/2` and `(-m² + (2ε - m)√Δ)/2` (`rank6_indicator_sqrt`).
* `rank6_m_gt_one_bound` — the identity
  `36m²(9m²+4) - 13(4m²+2)² = 4(m²-1)(29m²+13)` (line 3945).
-/

namespace HaagerupIzumi.C8.Fusion

/-- Dimensions of the induced objects (lines 3866–3873). -/
theorem rank6_induction_dims (m d s : ℝ) (hd : d ^ 2 = 3 * m * d + 1) (hs : s = 1 + d ^ 2) :
    1 + m * (3 * d) = d ^ 2 ∧ 2 + m * (3 * d) = s ∧ 1 + d ^ 2 + 2 * s = 3 * s := by
  refine ⟨by linear_combination -hd, by linear_combination (-1 : ℝ) * hs - hd, by rw [hs]; ring⟩

/-- eq:indicator-first: from the first twist trace of `I(ρ)`,
`m d² + m s + m(s + sζ + sζ²) + 3d S₁ = 0`, one gets `S₁ = m² - md`. -/
theorem rank6_indicator_first (m d s ζ S₁ : ℂ) (hd0 : d ≠ 0) (hd : d ^ 2 = 3 * m * d + 1)
    (hs : s = 1 + d ^ 2) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (htrace1 : m * d ^ 2 + m * s + m * (s + s * ζ + s * ζ ^ 2) + 3 * d * S₁ = 0) :
    S₁ = m ^ 2 - m * d := by
  have h : d * (S₁ - (m ^ 2 - m * d)) = 0 := by
    linear_combination (1 / 3 : ℂ) * htrace1 - (m * s / 3) * hζ - (m / 3) * hs + (m / 3) * hd
  have h' := (mul_eq_zero.mp h).resolve_left hd0
  linear_combination h'

/-- eq:indicator-second: from the second twist trace of `I(ρ)`,
`m d² + m s + m(s + sζ² + sζ⁴) + 3d S₂ = 3sε`, one gets
`S₂ = m² - md + ε(2d - 3m)`. -/
theorem rank6_indicator_second (m d s ζ S₂ ε : ℂ) (hd0 : d ≠ 0) (hd : d ^ 2 = 3 * m * d + 1)
    (hs : s = 1 + d ^ 2) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (htrace2 : m * d ^ 2 + m * s + m * (s + s * ζ ^ 2 + s * ζ ^ 4) + 3 * d * S₂ = 3 * s * ε) :
    S₂ = m ^ 2 - m * d + ε * (2 * d - 3 * m) := by
  have h : d * (S₂ - (m ^ 2 - m * d + ε * (2 * d - 3 * m))) = 0 := by
    linear_combination (1 / 3 : ℂ) * htrace2 - (m * s / 3) * (ζ ^ 2 - ζ + 1) * hζ -
      (m / 3) * hs + ε * hs + (m / 3) * hd - ε * hd
  have h' := (mul_eq_zero.mp h).resolve_left hd0
  linear_combination h'

/-- In terms of `Δ = 9m² + 4` and `d = (3m + √Δ)/2`: `m² - md = -(m² + m√Δ)/2` and
`m² - md + ε(2d - 3m) = (-m² + (2ε - m)√Δ)/2`. -/
theorem rank6_indicator_sqrt (m ε : ℝ) :
    let d := (3 * m + Real.sqrt (9 * m ^ 2 + 4)) / 2
    m ^ 2 - m * d = -(m ^ 2 + m * Real.sqrt (9 * m ^ 2 + 4)) / 2 ∧
      m ^ 2 - m * d + ε * (2 * d - 3 * m) =
        (-m ^ 2 + (2 * ε - m) * Real.sqrt (9 * m ^ 2 + 4)) / 2 ∧
      d ^ 2 = 3 * m * d + 1 := by
  intro d
  have hΔ : Real.sqrt (9 * m ^ 2 + 4) ^ 2 = 9 * m ^ 2 + 4 :=
    Real.sq_sqrt (by positivity)
  refine ⟨by simp only [d]; ring, by simp only [d]; ring, ?_⟩
  simp only [d]
  linear_combination (1 / 4 : ℝ) * hΔ

/-- The `m > 1` exclusion identity (line 3945). -/
theorem rank6_m_gt_one_bound (m : ℝ) :
    36 * m ^ 2 * (9 * m ^ 2 + 4) - 13 * (4 * m ^ 2 + 2) ^ 2 =
      4 * (m ^ 2 - 1) * (29 * m ^ 2 + 13) := by
  ring

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.rank6_indicator_first
#print axioms HaagerupIzumi.C8.Fusion.rank6_indicator_second
#print axioms HaagerupIzumi.C8.Fusion.rank6_indicator_sqrt
