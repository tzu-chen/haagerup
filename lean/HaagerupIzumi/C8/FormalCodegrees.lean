module

public import HaagerupIzumi.C8.RankSixMoments

@[expose] public section

/-!
# Formal codegrees of the near-group and rank-six fusion algebras

Lemma `lem:near-group-induction` (lines 3418–3420): "The four one-dimensional representations
of the fusion algebra have formal codegrees `3s, 9s/d², 3, 3`.  Thus induction of the unit is
`1 + X + Y + Y'`, with dimensions `1, d²/3, s, s`."  Lemma `lem:rank6-induction`
(lines 3856–3866): the characters `a ↦ 1, ρ ↦ d, -d⁻¹` and the two-dimensional representation
have formal codegrees `3s, 3s/d², 3`, giving `I(1) = 1 + X + 2Y` with `d_X = d²`, `d_Y = s`.

This file checks the relations of the near-group characters `a ↦ ζ, ρ ↦ 0`, the second roots
`-3/d` and `-1/d`, the formal codegrees `f_χ = ∑_X χ(X) χ(X*)` of the one-dimensional
characters, and the resulting dimensions `Dim 𝓕 / f_χ`.  The codegree `3` of the rank-six
two-dimensional representation is taken from the manuscript, not computed here; Ostrik's
induction–codegree correspondence (Theorems 2.5, 2.13) is the external input.
-/

namespace HaagerupIzumi.C8.FormalCodegrees

open Complex HaagerupIzumi.C8.CubeRootTwists HaagerupIzumi.C8.RankSixMoments

/-! ## Near group `ρ² = 1 + a + a² + mρ`, `m = 3k`, `d² = 3 + 3kd`, `s = 2 + kd`. -/

/-- The value `x = -3/d` is the second root of `x² = 3 + mx`. -/
theorem neargroup_second_root (k : ℕ) (d : ℝ) (hd : d ^ 2 = 3 + 3 * k * d) (hpos : 0 < d) :
    (-3 / d) ^ 2 = 3 + 3 * k * (-3 / d) := by
  field_simp
  nlinarith [hd]

/-- Characters `a ↦ ζ`, `ρ ↦ 0` respect `a³ = 1`, `aρ = ρ`, `ρ² = 1 + a + a² + mρ`. -/
theorem neargroup_zeta_character (m : ℕ) :
    zeta3 ^ 3 = 1 ∧ zeta3 * 0 = (0 : ℂ) ∧ (0 : ℂ) ^ 2 = 1 + zeta3 + zeta3 ^ 2 + m * 0 := by
  refine ⟨zeta3_cube, by ring, ?_⟩
  rw [one_add_zeta3_add_sq]; ring

/-- Formal codegrees `3 + x²` (for `a ↦ 1, ρ ↦ x`) at `x = d` and `x = -3/d` are `3s` and
`9s/d²`; the `ζ`-characters have `1 + ζζ² + ζ²ζ = 3`. -/
theorem neargroup_codegrees (k : ℕ) (d : ℝ) (hd : d ^ 2 = 3 + 3 * k * d) (hpos : 0 < d) :
    3 + d ^ 2 = 3 * (2 + k * d) ∧
      3 + (-3 / d) ^ 2 = 9 * (2 + k * d) / d ^ 2 ∧
      (1 : ℂ) + zeta3 * zeta3 ^ 2 + zeta3 ^ 2 * zeta3 = 3 := by
  refine ⟨by nlinarith [hd], ?_, ?_⟩
  · have hd0 : d ≠ 0 := hpos.ne'
    field_simp
    nlinarith [hd]
  · have h : zeta3 * zeta3 ^ 2 = zeta3 ^ 3 := by ring
    rw [h, show zeta3 ^ 2 * zeta3 = zeta3 ^ 3 by ring, zeta3_cube]
    norm_num

/-- The induced unit has dimensions `Dim 𝓕 / f_χ = 1, d²/3, s, s` with `Dim 𝓕 = 3 + d² = 3s`;
the second equals `1 + kd = d_X`. -/
theorem neargroup_induction_dims (k : ℕ) (d : ℝ) (hd : d ^ 2 = 3 + 3 * k * d) (hpos : 0 < d) :
    (3 + d ^ 2) / (3 * (2 + k * d)) = 1 ∧
      (3 + d ^ 2) / (9 * (2 + k * d) / d ^ 2) = d ^ 2 / 3 ∧
      d ^ 2 / 3 = 1 + k * d ∧ (3 + d ^ 2) / 3 = 2 + k * d := by
  have hs : (0 : ℝ) < 2 + k * d := by positivity
  have hd0 : d ≠ 0 := hpos.ne'
  refine ⟨?_, ?_, by linarith [hd], by linarith [hd]⟩
  · rw [div_eq_one_iff_eq (by positivity : (3 : ℝ) * (2 + k * d) ≠ 0)]
    linarith [hd]
  · field_simp
    nlinarith [hd]

/-! ## Rank six `ρ² = 1 + m(ρ + aρ + a²ρ)`, `d² = 3md + 1`, `s = 1 + d²`. -/

/-- `-1/d` is the second root of `x² = 1 + 3mx` (the value of `ρ` under the second
character with `a ↦ 1`). -/
theorem rank6_second_root (m : ℕ) (d : ℝ) (hd : d ^ 2 = 3 * m * d + 1) (hpos : 0 < d) :
    (-1 / d) ^ 2 = 3 * m * (-1 / d) + 1 := by
  field_simp
  nlinarith [hd]

/-- Formal codegrees: `3 + 3d² = 3s` and `3 + 3/d² = 3s/d²`; the dimensions of the induced
unit are `1`, `d²` and (twice) `s`. -/
theorem rank6_codegrees (m : ℕ) (d : ℝ) (hd : d ^ 2 = 3 * m * d + 1) (hpos : 0 < d) :
    3 + 3 * d ^ 2 = 3 * (1 + d ^ 2) ∧ 3 + 3 * (-1 / d) ^ 2 = 3 * (1 + d ^ 2) / d ^ 2 ∧
      (3 * (1 + d ^ 2)) / (3 * (1 + d ^ 2) / d ^ 2) = d ^ 2 ∧
      (3 * (1 + d ^ 2)) / 3 = 1 + d ^ 2 := by
  have hd0 : d ≠ 0 := hpos.ne'
  have hs : (0 : ℝ) < 1 + d ^ 2 := by positivity
  refine ⟨by ring, ?_, ?_, by ring⟩
  · field_simp
    ring
  · field_simp

#print axioms neargroup_codegrees
#print axioms rank6_codegrees

end HaagerupIzumi.C8.FormalCodegrees
