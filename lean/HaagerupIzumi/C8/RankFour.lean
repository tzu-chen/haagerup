module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Exclusion of rank four (Section "Excluding rank four", lines 3356–3790)

At rank four the boundary fusion ring is the near group `a³ = 1`, `aρ = ρa = ρ`,
`ρ² = 1 + a + a² + mρ`; Larson's Theorem 1.1 (pseudo-unitary, two self-dual simples) restricts
`m` to `0, 2, 3, 6`.  The manuscript then excludes each case:

* `m = 0`: `d² = 3`, so `Dim 𝓕 = 3 + d² = 6 = 3s`, `s = 2` and `d_X = s - 1 = 1`, i.e. `X` would be
  invertible, contradicting Lemma `lem:no-sign-extension` (`nearGroup_m0_impossible`, proved
  here in full);
* `m = 2`: the twisted `A₄` double gives a holomorphic `H' ≅ V_{E₈}` with `U = H'^{A₄}` (EGO,
  HKL, Dong–Mason; external), and `dim U₁ = dim 𝔢₈^{A₄} ≥ 16`
  (`Fusion.e8_A4_invariants_ge`);
* `m = 3, 6`: Proposition `prop:near-group-current-obstructions` gives
  `dim U₁ ∈ {15 + A + 10B, 14 + 42A}` resp. `{8 + A, 5 + 12P}` (the theta tables are kernel-checked
  in `Theta/`, and the pole-cancellation lemma in `Analytic/PoleCancellation.lean`; the
  identification with Weil representations is external).

`rank_four_excluded` assembles these: with `dim U₁ = 6`, no case survives.  The case inputs are
the conclusions of the case analyses named above.
-/

namespace HaagerupIzumi.C8.RankFour

/-- **The case `m = 0`.**  From `d² = 3 + 0·d`, `Dim 𝓕 = 3 + d² = 3s` and `d_X = s - 1`, one gets
`d_X = 1`, contradicting Lemma `lem:no-sign-extension` (`X` is not invertible, `d_X ≠ 1`). -/
theorem nearGroup_m0_impossible (d s dX : ℝ) (hd : d ^ 2 = 3 + 0 * d)
    (hDim : 3 + d ^ 2 = 3 * s) (hX : dX = s - 1) (hnoSign : dX ≠ 1) : False := by
  apply hnoSign
  have hs : s = 2 := by nlinarith
  rw [hX, hs]
  norm_num

/-- **Rank four is excluded.**  Inputs: Larson's restriction `m ∈ {0,2,3,6}`; the near-group
dimension data and Lemma `lem:no-sign-extension` (for `m = 0`); the conclusions of the `m = 2`
analysis (`dim U₁ ≥ 16`) and of Proposition `prop:near-group-current-obstructions` (for
`m = 3, 6`); and the six-current result `dim U₁ = 6`. -/
theorem rank_four_excluded (m : ℕ) (hLarson : m = 0 ∨ m = 2 ∨ m = 3 ∨ m = 6)
    (d s dX : ℝ) (hd : d ^ 2 = 3 + (m : ℝ) * d) (hDim : 3 + d ^ 2 = 3 * s)
    (hX : dX = s - 1) (hnoSign : dX ≠ 1)
    (dimU1 : ℕ) (hU1 : dimU1 = 6)
    (case2 : m = 2 → 16 ≤ dimU1)
    (case3 : m = 3 → ∃ A B : ℕ, dimU1 = 15 + A + 10 * B ∨ dimU1 = 14 + 42 * A)
    (case6 : m = 6 → ∃ A P : ℕ, dimU1 = 8 + A ∨ dimU1 = 5 + 12 * P) : False := by
  rcases hLarson with rfl | rfl | rfl | rfl
  · exact nearGroup_m0_impossible d s dX (by simpa using hd) hDim hX hnoSign
  · have := case2 rfl
    omega
  · obtain ⟨A, B, h | h⟩ := case3 rfl <;> omega
  · obtain ⟨A, P, h | h⟩ := case6 rfl <;> omega

#print axioms nearGroup_m0_impossible
#print axioms rank_four_excluded

end HaagerupIzumi.C8.RankFour
