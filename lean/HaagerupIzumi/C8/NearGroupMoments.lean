module

public import HaagerupIzumi.C8.RankSixMoments

@[expose] public section

/-!
# The twist moments of Lemma `lem:near-group-induction`

For the rank-four near-group ring `ρ² = 1 + a + a² + mρ`, `m = 3k`, Lemma
`lem:near-group-induction` (lines 3392–3449 of the expanded draft) lists the known center
objects and their forgetful images:
`X: 1 + kρ`, `Y, Y': 1 + a + kρ, 1 + a² + kρ`, `C: a + a² + kρ`, `D, D': a + pρ, a² + pρ`,
`E, E': a + qρ, a² + qρ`, with twists `1, 1, 1, ζ, ζ², ζ², ζ², ζ²`, and further simples `Z_j`
with `F(Z_j) = n_j ρ`, `p + q = k`.  With `d² = 3 + 3kd` and `s = 2 + kd`, adjunction gives

  `I(ρ) = kX + kY + kY' + kC + pD + pD' + qE + qE' + ∑ n_j Z_j`,

and the first and second twist traces are `0` and `Dim 𝓕 · ν₂(ρ) = 3 s ε`.  The manuscript
concludes (eq:near-group-moments, using `3/d = d - 3k` and `3s/d = √(9k² + 12)`)

  `∑ n_j² θ_j = k² - kd - (p - q)² ζ²`,   `∑ n_j² θ_j² = conj(that) + ε √(9k² + 12)`.

`neargroup_moments` derives both from the trace equations.  The hypotheses `trace1`,
`trace2` are the Ng–Schauenburg formula already evaluated on the induction decomposition
displayed above (whose twists come from `CubeRootTwists.neargroup_twists` and
`CubeRootTwists.neargroup_multiplicities`, and whose objects come from Ostrik's
correspondence, external).
-/

namespace HaagerupIzumi.C8.NearGroupMoments

open Complex HaagerupIzumi.C8.CubeRootTwists HaagerupIzumi.C8.RankSixMoments

/-- `√(9k² + 12) = 2d - 3k` for the positive root `d` of `d² = 3 + 3kd`. -/
theorem sqrt_neargroup (k : ℕ) (d : ℝ) (hd : d ^ 2 = 3 + 3 * k * d) (hpos : 0 < d) :
    Real.sqrt (9 * (k : ℝ) ^ 2 + 12) = 2 * d - 3 * k := by
  have hsq : (2 * d - 3 * k) ^ 2 = 9 * (k : ℝ) ^ 2 + 12 := by nlinarith [hd]
  have hnn : 0 ≤ 2 * d - 3 * k := by
    have h1 : d * (d - 3 * k) = 3 := by nlinarith [hd]
    have h2 : 0 < d - 3 * k := by
      by_contra h
      push Not at h
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hpos.le h]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  rw [← hsq, Real.sqrt_sq hnn]

/-- **eq:near-group-moments.**  With `d > 0`, `d² = 3 + 3kd`, `s = 2 + kd`, `p + q = k`, the
first and second twist traces of `I(ρ)` (written with `S₁ = ∑ n_j² θ_j`,
`S₂ = ∑ n_j² θ_j²`, the `Z_j` contributing `n_j · (n_j d) · θ_j`) force
`S₁ = k² - kd - (p - q)² ζ²` and `S₂ = k² - kd - (p - q)² ζ + ε √(9k² + 12)`. -/
theorem neargroup_moments (k p q : ℕ) (hpq : p + q = k) (d ε : ℝ)
    (hd : d ^ 2 = 3 + 3 * k * d) (hpos : 0 < d) (S₁ S₂ : ℂ)
    (trace1 : (k : ℂ) * (1 + k * d) + 2 * k * (2 + k * d) + k * (2 + k * d) * zeta3 +
        2 * p * (1 + p * d) * zeta3 ^ 2 + 2 * q * (1 + q * d) * zeta3 ^ 2 + (d : ℂ) * S₁ = 0)
    (trace2 : (k : ℂ) * (1 + k * d) + 2 * k * (2 + k * d) + k * (2 + k * d) * zeta3 ^ 2 +
        2 * p * (1 + p * d) * zeta3 ^ 4 + 2 * q * (1 + q * d) * zeta3 ^ 4 + (d : ℂ) * S₂ =
        3 * (2 + k * d) * ε) :
    S₁ = (k : ℂ) ^ 2 - k * d - ((p : ℂ) - q) ^ 2 * zeta3 ^ 2 ∧
      S₂ = (k : ℂ) ^ 2 - k * d - ((p : ℂ) - q) ^ 2 * zeta3 +
        ((ε * Real.sqrt (9 * (k : ℝ) ^ 2 + 12) : ℝ) : ℂ) := by
  rw [sqrt_neargroup k d hd hpos]
  have hdC : (d : ℂ) ^ 2 = 3 + 3 * (k : ℂ) * d := by exact_mod_cast hd
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hk : (k : ℂ) = p + q := by exact_mod_cast hpq.symm
  have hζ := one_add_zeta3_add_sq
  rw [zeta3_pow_four] at trace2
  rw [hk] at trace1 trace2 hdC
  constructor
  · have h : (d : ℂ) * S₁ = (d : ℂ) * ((k : ℂ) ^ 2 - k * d - ((p : ℂ) - q) ^ 2 * zeta3 ^ 2) := by
      rw [hk]
      linear_combination trace1 + ((p : ℂ) + q) * hdC -
        (2 * ((p : ℂ) + q) + ((p : ℂ) + q) ^ 2 * d) * hζ
    exact mul_left_cancel₀ hd0 h
  · have h : (d : ℂ) * S₂ = (d : ℂ) * ((k : ℂ) ^ 2 - k * d - ((p : ℂ) - q) ^ 2 * zeta3 +
        ((ε * (2 * d - 3 * k) : ℝ) : ℂ)) := by
      push_cast
      rw [hk]
      linear_combination trace2 + ((p : ℂ) + q - 2 * ε) * hdC -
        (2 * ((p : ℂ) + q) + ((p : ℂ) + q) ^ 2 * d) * hζ
    exact mul_left_cancel₀ hd0 h

#print axioms neargroup_moments

end HaagerupIzumi.C8.NearGroupMoments
