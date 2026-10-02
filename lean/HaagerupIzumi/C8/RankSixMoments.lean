module

public import HaagerupIzumi.C8.CubeRootTwists
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# The two twist moments of Lemma `lem:rank6-induction`

For a pseudo-unitary categorification of eq:rank6-ring with untwisted pointed part, center
induction gives (lines 3900–3913 of the expanded draft)

  `I(ρ) = mX + mY + m(C₀ + C₁ + C₂) + ∑_j n_j Z_j`,

with `d_X = d²`, `d_Y = s = 1 + d²`, `d_{C_j} = s`, twists `θ_X = θ_Y = 1`,
`θ_{C_j} = 1, ζ₃, ζ₃²`, and `d_{Z_j} = 3 n_j d` (since `F(Z_j) = n_j R`).  The first and
second twist traces of `I(ρ)` are `Dim 𝓕 · ν₁(ρ) = 0` and `Dim 𝓕 · ν₂(ρ) = 3 s ε`
(Ng–Schauenburg).  Using `d⁻¹ = d - 3m` the manuscript obtains

  `∑ n_j² θ_j = -(m² + m√Δ)/2`  (eq:indicator-first),
  `∑ n_j² θ_j² = (-m² + (2ε - m)√Δ)/2`  (eq:indicator-second),   `Δ = 9m² + 4`.

`indicator_moments` derives both identities from the two trace equations, with
`d = (3m + √Δ)/2` the positive root of `d² = 3md + 1`.  The hypotheses `trace1`, `trace2` are
the Ng–Schauenburg trace formula (Theorem 4.1) *already evaluated on* the induction
decomposition of Lemma `lem:rank6-induction`; that decomposition (multiplicities `m`,
dimensions `d², s, 3n_j d`, `C`-twists `1, ζ, ζ²`) comes from Ostrik's induction–codegree
correspondence (external) together with `CubeRootTwists.rank6_twists` and
`CubeRootTwists.eq_one_of_weighted_sum` (manuscript steps, proved there).
`TwistTraces.indicator_moments_of_trace` derives `trace1`, `trace2` from the Ng–Schauenburg
formula stated for the list of center constituents of `I(ρ)`.
-/

namespace HaagerupIzumi.C8.RankSixMoments

open Complex HaagerupIzumi.C8.CubeRootTwists

/-- `1 + ζ₃ + ζ₃² = 0`. -/
theorem one_add_zeta3_add_sq : (1 : ℂ) + zeta3 + zeta3 ^ 2 = 0 := by
  rw [zeta3_sq]; ring

/-- `ζ₃⁴ = ζ₃`. -/
theorem zeta3_pow_four : zeta3 ^ 4 = zeta3 := by
  have h : zeta3 ^ 4 = zeta3 ^ 3 * zeta3 := by ring
  rw [h, zeta3_cube, one_mul]

/-- `√Δ = 2d - 3m` for the positive root `d` of `d² = 3md + 1`. -/
theorem sqrt_delta (m : ℕ) (d : ℝ) (hd : d ^ 2 = 3 * m * d + 1) (hpos : 0 < d) :
    Real.sqrt (9 * (m : ℝ) ^ 2 + 4) = 2 * d - 3 * m := by
  have hsq : (2 * d - 3 * m) ^ 2 = 9 * (m : ℝ) ^ 2 + 4 := by nlinarith [hd]
  have hnn : 0 ≤ 2 * d - 3 * m := by
    -- `d (d - 3m) = 1 > 0` and `d > 0` give `d > 3m`, so `2d - 3m > 0`
    have h1 : d * (d - 3 * m) = 1 := by nlinarith [hd]
    have h2 : 0 < d - 3 * m := by
      by_contra h
      push Not at h
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hpos.le h]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [← hsq, Real.sqrt_sq hnn]

/-- **eq:indicator-first and eq:indicator-second.**  If `d > 0`, `d² = 3md + 1`,
`s = 1 + d²`, and the first and second twist traces of
`I(ρ) = mX + mY + m(C₀ + C₁ + C₂) + ∑ n_j Z_j` are `0` and `3sε`, written with
`S₁ = ∑ n_j² θ_j` and `S₂ = ∑ n_j² θ_j²`, then
`S₁ = -(m² + m√Δ)/2` and `S₂ = (-m² + (2ε - m)√Δ)/2`. -/
theorem indicator_moments (m : ℕ) (d ε : ℝ) (hd : d ^ 2 = 3 * m * d + 1) (hpos : 0 < d)
    (S₁ S₂ : ℂ)
    (trace1 : (m : ℂ) * (d : ℂ) ^ 2 + m * (1 + (d : ℂ) ^ 2) +
        m * (1 + (d : ℂ) ^ 2) * (1 + zeta3 + zeta3 ^ 2) + 3 * (d : ℂ) * S₁ = 0)
    (trace2 : (m : ℂ) * (d : ℂ) ^ 2 + m * (1 + (d : ℂ) ^ 2) +
        m * (1 + (d : ℂ) ^ 2) * (1 + zeta3 ^ 2 + zeta3 ^ 4) + 3 * (d : ℂ) * S₂ =
        3 * (1 + (d : ℂ) ^ 2) * ε) :
    S₁ = -(((m : ℝ) ^ 2 + m * Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℝ) : ℂ) / 2 ∧
      S₂ = ((-(m : ℝ) ^ 2 + (2 * ε - m) * Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℝ) : ℂ) / 2 := by
  rw [sqrt_delta m d hd hpos]
  have hdC : (d : ℂ) ^ 2 = 3 * (m : ℂ) * d + 1 := by exact_mod_cast hd
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hz1 := one_add_zeta3_add_sq
  have hz2 : (1 : ℂ) + zeta3 ^ 2 + zeta3 ^ 4 = 0 := by rw [zeta3_pow_four]; linear_combination hz1
  rw [hz1] at trace1
  rw [hz2] at trace2
  constructor
  · -- `3 d S₁ = -m (2d² + 1) = -m(6md + 3)`, hence `S₁ = -m(2m + 1/d) = m² - md`
    have h : (3 * (d : ℂ)) * S₁ = (3 * (d : ℂ)) * (-(((m : ℂ) ^ 2 + m * (2 * d - 3 * m))) / 2) := by
      linear_combination trace1 + (m : ℂ) * hdC
    have h3d : (3 * (d : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hd0
    have := mul_left_cancel₀ h3d h
    rw [this]
    push_cast
    ring
  · have h : (3 * (d : ℂ)) * S₂ =
        (3 * (d : ℂ)) * ((-(m : ℂ) ^ 2 + (2 * ε - m) * (2 * d - 3 * m)) / 2) := by
      linear_combination trace2 + ((m : ℂ) - 3 * ε) * hdC
    have h3d : (3 * (d : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hd0
    have := mul_left_cancel₀ h3d h
    rw [this]
    push_cast
    ring

#print axioms indicator_moments

end HaagerupIzumi.C8.RankSixMoments
