module

public import HaagerupIzumi.C8.NearGroupMoments
public import HaagerupIzumi.C8.CenterDimension
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Twist traces from the Ng–Schauenburg formula

`RankSixMoments.indicator_moments` (eq:indicator-first/second, lemma `lem:rank6-induction`,
lines 3846–3853 and 3906–3913 of `c8_expanded_20260929/haagerup_c8_expanded.tex`) and
`NearGroupMoments.neargroup_moments` (eq:near-group-moments, lemma `lem:near-group-induction`,
lines 3392–3449) take their hypotheses `trace1`, `trace2` as the Ng–Schauenburg formula *already
evaluated* on the induction decomposition.  This file states the formula itself, for an arbitrary
index set of center simples, and proves the evaluation:

* `NgSchauenburgTrace mult dim θ Dim ν`: **Ng–Schauenburg, Theorem 4.1** for one object `V`:
  `Dim 𝓕 · ν_n(V) = ∑_Z [I(V) : Z] d_Z θ_Z^n` for `n ≥ 1` (external).  The sum may run over
  any index set containing the support of `I(V)` (simples with `[I(V) : Z] = 0` contribute
  nothing); below it runs over the constituents of `I(ρ)`.
* `rank6Mult`, `rank6Dim`, `rank6Twist`: the decomposition
  `I(ρ) = mX + mY + m(C₀ + C₁ + C₂) + ∑ n_j Z_j` with dimensions `d², s, s, s, s, 3n_j d` and
  twists `1, 1, 1, ζ, ζ², θ_j` (lines 3838–3843, 3907; obtained from Ostrik's
  induction–codegree correspondence, external, and `CubeRootTwists`);
* `indicator_moments_of_trace`: eq:indicator-first and eq:indicator-second from the formula,
  `Dim 𝓕 = ∑ d_x² = 3s` (`CenterDimension.rank6_DimF`), `ν₁(ρ) = 0` and `ν₂(ρ) = ε` (the
  Frobenius–Schur indicators of the simple self-dual `ρ ≠ 𝟏`);
* `nearGroupMult`, `nearGroupDim`, `nearGroupTwist` and `neargroup_moments_of_trace`: the same for
  `I(ρ) = kX + kY + kY' + kC + pD + pD' + qE + qE' + ∑ n_j Z_j` (lines 3398–3407, 3441–3449),
  with `Dim 𝓕 = 3s` (`CenterDimension.nearGroup_DimF`), for either primitive cube root `ζ`
  (the manuscript's `ζ` is existential; `CubeRootTwists.neargroup_twists` has two branches):
  `neargroup_moments_gen` is `NearGroupMoments.neargroup_moments` with `ζ₃` replaced by any `ζ`
  with `1 + ζ + ζ² = 0`.
-/

namespace HaagerupIzumi.C8.TwistTraces

open Complex HaagerupIzumi.C8.CubeRootTwists

/-- **Ng–Schauenburg, Theorem 4.1** (twist-trace formula for the Frobenius–Schur indicators of
an object `V` of a spherical fusion category `𝓕`): `Dim 𝓕 · ν_n(V) = ∑_Z [I(V) : Z] d_Z θ_Z^n`,
for `n ≥ 1`, summed over simple objects `Z` of the center (any index set containing those with
`mult Z = [I(V) : Z] ≠ 0`). -/
def NgSchauenburgTrace {ι : Type*} [Fintype ι] (mult : ι → ℕ) (dim : ι → ℝ) (θ : ι → ℂ)
    (DimF : ℝ) (ν : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, 0 < n → (DimF : ℂ) * ν n = ∑ Z, (mult Z : ℂ) * (dim Z : ℂ) * θ Z ^ n

variable {J : Type*} [Fintype J]

/-- The residual columns: `∑_j n_j (c n_j d) θ_j^k = c d ∑_j n_j² θ_j^k`. -/
theorem residual_sum (n : J → ℕ) (θ : J → ℂ) (c d : ℝ) (k : ℕ) :
    ∑ j, (n j : ℂ) * ((c * (n j : ℝ) * d : ℝ) : ℂ) * θ j ^ k =
      (c : ℂ) * (d : ℂ) * ∑ j, (n j : ℂ) ^ 2 * θ j ^ k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-! ### Rank six (`lem:rank6-induction`) -/

/-- Multiplicities `[I(ρ) : Z]` for `Z = X, Y, C₀, C₁, C₂, Z_j`. -/
def rank6Mult (m : ℕ) (n : J → ℕ) : Fin 5 ⊕ J → ℕ := Sum.elim (fun _ => m) n

/-- Dimensions `d², s, s, s, s, 3 n_j d` with `s = 1 + d²`. -/
noncomputable def rank6Dim (d : ℝ) (n : J → ℕ) : Fin 5 ⊕ J → ℝ :=
  Sum.elim ![d ^ 2, 1 + d ^ 2, 1 + d ^ 2, 1 + d ^ 2, 1 + d ^ 2] (fun j => 3 * (n j : ℝ) * d)

/-- Twists `1, 1, 1, ζ, ζ², θ_j`. -/
noncomputable def rank6Twist (θ : J → ℂ) : Fin 5 ⊕ J → ℂ :=
  Sum.elim ![1, 1, 1, zeta3, zeta3 ^ 2] θ

/-- **eq:indicator-first and eq:indicator-second from the Ng–Schauenburg formula.**  For the
induction decomposition of `lem:rank6-induction`, `Dim 𝓕 = 3s`, `ν₁(ρ) = 0`, `ν₂(ρ) = ε`:
`∑ n_j² θ_j = -(m² + m√Δ)/2` and `∑ n_j² θ_j² = (-m² + (2ε - m)√Δ)/2`. -/
theorem indicator_moments_of_trace (m : ℕ) (d ε : ℝ) (hd : d ^ 2 = 3 * m * d + 1)
    (hpos : 0 < d) (n : J → ℕ) (θ : J → ℂ) (ν : ℕ → ℂ)
    (hNS : NgSchauenburgTrace (rank6Mult m n) (rank6Dim d n) (rank6Twist θ)
      (∑ x, CenterDimension.rank6FusionDim d x ^ 2) ν)
    (hν1 : ν 1 = 0) (hν2 : ν 2 = ε) :
    ∑ j, (n j : ℂ) ^ 2 * θ j = -(((m : ℝ) ^ 2 + m * Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℝ) : ℂ) / 2 ∧
      ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 =
        ((-(m : ℝ) ^ 2 + (2 * ε - m) * Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℝ) : ℂ) / 2 := by
  have h1 := hNS 1 one_pos
  have h2 := hNS 2 two_pos
  rw [CenterDimension.rank6_DimF] at h1 h2
  rw [Fintype.sum_sum_type] at h1 h2
  simp only [rank6Mult, rank6Dim, rank6Twist, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at h1 h2
  rw [residual_sum n θ 3 d 1] at h1
  rw [residual_sum n θ 3 d 2] at h2
  simp only [pow_one] at h1
  rw [hν1] at h1
  rw [hν2] at h2
  push_cast at h1 h2
  exact RankSixMoments.indicator_moments m d ε hd hpos _ _
    (by linear_combination -h1) (by linear_combination -h2)

/-! ### Near-group (`lem:near-group-induction`) -/

/-- Multiplicities `[I(ρ) : Z]` for `Z = X, Y, Y', C, D, D', E, E', Z_j`. -/
def nearGroupMult (k p q : ℕ) (n : J → ℕ) : Fin 8 ⊕ J → ℕ :=
  Sum.elim ![k, k, k, k, p, p, q, q] n

/-- Dimensions of `X: 1+kρ`, `Y, Y': 1+a+kρ, 1+a²+kρ`, `C: a+a²+kρ`, `D, D': a+pρ, a²+pρ`,
`E, E': a+qρ, a²+qρ`, and `Z_j: n_j ρ`. -/
noncomputable def nearGroupDim (k p q : ℕ) (d : ℝ) (n : J → ℕ) : Fin 8 ⊕ J → ℝ :=
  Sum.elim ![1 + k * d, 2 + k * d, 2 + k * d, 2 + k * d, 1 + p * d, 1 + p * d, 1 + q * d,
    1 + q * d] (fun j => 1 * (n j : ℝ) * d)

/-- Twists `1, 1, 1, ζ, ζ², ζ², ζ², ζ², θ_j`. -/
noncomputable def nearGroupTwist (ζ : ℂ) (θ : J → ℂ) : Fin 8 ⊕ J → ℂ :=
  Sum.elim ![1, 1, 1, ζ, ζ ^ 2, ζ ^ 2, ζ ^ 2, ζ ^ 2] θ

/-- `NearGroupMoments.neargroup_moments` for an arbitrary primitive cube root `ζ`
(`1 + ζ + ζ² = 0`); the proof is the same. -/
theorem neargroup_moments_gen (k p q : ℕ) (hpq : p + q = k) (d ε : ℝ)
    (hd : d ^ 2 = 3 + 3 * k * d) (hpos : 0 < d) (ζ : ℂ) (hζ : 1 + ζ + ζ ^ 2 = 0) (S₁ S₂ : ℂ)
    (trace1 : (k : ℂ) * (1 + k * d) + 2 * k * (2 + k * d) + k * (2 + k * d) * ζ +
        2 * p * (1 + p * d) * ζ ^ 2 + 2 * q * (1 + q * d) * ζ ^ 2 + (d : ℂ) * S₁ = 0)
    (trace2 : (k : ℂ) * (1 + k * d) + 2 * k * (2 + k * d) + k * (2 + k * d) * ζ ^ 2 +
        2 * p * (1 + p * d) * ζ ^ 4 + 2 * q * (1 + q * d) * ζ ^ 4 + (d : ℂ) * S₂ =
        3 * (2 + k * d) * ε) :
    S₁ = (k : ℂ) ^ 2 - k * d - ((p : ℂ) - q) ^ 2 * ζ ^ 2 ∧
      S₂ = (k : ℂ) ^ 2 - k * d - ((p : ℂ) - q) ^ 2 * ζ +
        ((ε * Real.sqrt (9 * (k : ℝ) ^ 2 + 12) : ℝ) : ℂ) := by
  rw [NearGroupMoments.sqrt_neargroup k d hd hpos]
  have hdC : (d : ℂ) ^ 2 = 3 + 3 * (k : ℂ) * d := by exact_mod_cast hd
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hk : (k : ℂ) = p + q := by exact_mod_cast hpq.symm
  have hζ4 : ζ ^ 4 = ζ := by linear_combination (ζ ^ 2 - ζ) * hζ
  rw [hζ4] at trace2
  rw [hk] at trace1 trace2 hdC
  constructor
  · have h : (d : ℂ) * S₁ = (d : ℂ) * ((k : ℂ) ^ 2 - k * d - ((p : ℂ) - q) ^ 2 * ζ ^ 2) := by
      rw [hk]
      linear_combination trace1 + ((p : ℂ) + q) * hdC -
        (2 * ((p : ℂ) + q) + ((p : ℂ) + q) ^ 2 * d) * hζ
    exact mul_left_cancel₀ hd0 h
  · have h : (d : ℂ) * S₂ = (d : ℂ) * ((k : ℂ) ^ 2 - k * d - ((p : ℂ) - q) ^ 2 * ζ +
        ((ε * (2 * d - 3 * k) : ℝ) : ℂ)) := by
      push_cast
      rw [hk]
      linear_combination trace2 + ((p : ℂ) + q - 2 * ε) * hdC -
        (2 * ((p : ℂ) + q) + ((p : ℂ) + q) ^ 2 * d) * hζ
    exact mul_left_cancel₀ hd0 h

/-- **eq:near-group-moments from the Ng–Schauenburg formula.**  For the induction
decomposition of `lem:near-group-induction` with a primitive cube root `ζ`,
`Dim 𝓕 = ∑ d_x² = 3s` (`s = 2 + kd`), `ν₁(ρ) = 0`, `ν₂(ρ) = ε`:
`∑ n_j² θ_j = k² - kd - (p - q)² ζ²` and
`∑ n_j² θ_j² = k² - kd - (p - q)² ζ + ε √(9k² + 12)`. -/
theorem neargroup_moments_of_trace (k p q : ℕ) (hpq : p + q = k) (d ε : ℝ)
    (hd : d ^ 2 = 3 + 3 * k * d) (hpos : 0 < d) (ζ : ℂ) (hζ : 1 + ζ + ζ ^ 2 = 0)
    (n : J → ℕ) (θ : J → ℂ) (ν : ℕ → ℂ)
    (hNS : NgSchauenburgTrace (nearGroupMult k p q n) (nearGroupDim k p q d n)
      (nearGroupTwist ζ θ) (∑ x, CenterDimension.nearGroupFusionDim d x ^ 2) ν)
    (hν1 : ν 1 = 0) (hν2 : ν 2 = ε) :
    ∑ j, (n j : ℂ) ^ 2 * θ j = (k : ℂ) ^ 2 - k * d - ((p : ℂ) - q) ^ 2 * ζ ^ 2 ∧
      ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 = (k : ℂ) ^ 2 - k * d - ((p : ℂ) - q) ^ 2 * ζ +
        ((ε * Real.sqrt (9 * (k : ℝ) ^ 2 + 12) : ℝ) : ℂ) := by
  have h1 := hNS 1 one_pos
  have h2 := hNS 2 two_pos
  rw [CenterDimension.nearGroup_DimF k d hd] at h1 h2
  rw [Fintype.sum_sum_type] at h1 h2
  simp only [nearGroupMult, nearGroupDim, nearGroupTwist, Sum.elim_inl, Sum.elim_inr,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at h1 h2
  rw [residual_sum n θ 1 d 1] at h1
  rw [residual_sum n θ 1 d 2] at h2
  simp only [pow_one] at h1
  rw [hν1] at h1
  rw [hν2] at h2
  push_cast at h1 h2
  exact neargroup_moments_gen k p q hpq d ε hd hpos ζ hζ _ _
    (by linear_combination -h1) (by linear_combination -h2)

/-- Both primitive cube roots qualify: `ζ₃` and `ζ₃²`. -/
theorem zeta3_cases : (1 + zeta3 + zeta3 ^ 2 = 0) ∧ (1 + zeta3 ^ 2 + (zeta3 ^ 2) ^ 2 = 0) := by
  have h := RankSixMoments.one_add_zeta3_add_sq
  refine ⟨h, ?_⟩
  have h4 : (zeta3 ^ 2) ^ 2 = zeta3 := by
    rw [← pow_mul]
    exact RankSixMoments.zeta3_pow_four
  rw [h4]
  linear_combination h

#print axioms indicator_moments_of_trace
#print axioms neargroup_moments_gen
#print axioms neargroup_moments_of_trace

end HaagerupIzumi.C8.TwistTraces
