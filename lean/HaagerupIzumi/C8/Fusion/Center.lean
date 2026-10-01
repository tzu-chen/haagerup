module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.ZMod.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Dimension arithmetic of the Haagerup center

Appendix G and Sections J–K of `c8_expanded_20260929/haagerup_c8_expanded.tex`.

* `rank6_center_count` — for the rank-six ring with `d² = 3md + 1`,
  `s = 1 + d²`, the center-dimension identity
  `9s² = 1 + d⁴ + 4s² + 9d² ∑ n_j²` holds iff `∑ n_j² = 4m² + 2`
  (Lemma `lem:rank6-induction`, line 3900).  The identity itself is
  `Dim Z(𝓕) = (Dim 𝓕)²` for the forgetful images determined there (external
  categorical input).
* Haagerup numbers (eq:haagerup-dimensions, line 4013):
  `d = (3+√13)/2`, `d² = 3d + 1`, `s = 1 + d² = (13 + 3√13)/2`,
  `d_X = d² = (11 + 3√13)/2`.
* The twelve center dimensions `1, d², s (×4), 3d (×6)` have
  `∑ dim² = 9s² = Dim(𝓗₃)²` with `Dim(𝓗₃) = 1 + 1 + 1 + 3d² = 3s`
  (line 4053; Theorem `thm:analytic-e8-extension`, lines 5173–5176).
* The `6 · 6 = 36` defect labels `x ⊠ y` have total squared dimension
  `(∑ d_x²)² = Dim(𝓗₃)²` (`sum_sq_pairs`, line 5173).
* `H²(ℤ/3, ℂˣ) = ℂˣ/(ℂˣ)³ = 0`: every nonzero complex number is a cube
  (`units_cube_surjective`, line 4966); `(ℤ/3)/2(ℤ/3) = 0` (line 4969).
  The identification `H²(ℤ/n, A) ≅ A/nA` for trivial action and the Izumi
  obstruction theory that uses these groups are external.
-/

namespace HaagerupIzumi.C8.Fusion

/-! ### The center count for the rank-six ring -/

/-- Lemma `lem:rank6-induction`, first equation: with `d² = 3md + 1` and `s = 1 + d²`,
`9s² = 1 + d⁴ + 4s² + 9d² S ↔ S = 4m² + 2`. -/
theorem rank6_center_count (m d S : ℝ) (hd : d ^ 2 = 3 * m * d + 1) :
    9 * (1 + d ^ 2) ^ 2 = 1 + d ^ 4 + 4 * (1 + d ^ 2) ^ 2 + 9 * d ^ 2 * S ↔
      S = 4 * m ^ 2 + 2 := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    norm_num at hd
  have key : 9 * (1 + d ^ 2) ^ 2 - (1 + d ^ 4 + 4 * (1 + d ^ 2) ^ 2) =
      9 * d ^ 2 * (4 * m ^ 2 + 2) := by
    linear_combination 4 * (d ^ 2 - 1 + 3 * m * d) * hd
  constructor
  · intro h
    have h9 : 9 * d ^ 2 * S = 9 * d ^ 2 * (4 * m ^ 2 + 2) := by
      linear_combination key - h
    have hne : 9 * d ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hd0)
    exact mul_left_cancel₀ hne h9
  · intro h
    rw [h]
    linear_combination key

/-! ### Haagerup numbers -/

/-- The Haagerup dimension `d = (3 + √13)/2`. -/
noncomputable def haagerupD : ℝ := (3 + Real.sqrt 13) / 2

/-- `s = 1 + d²`, the dimension of `Y` and of the `C_j`. -/
noncomputable def haagerupS : ℝ := 1 + haagerupD ^ 2

theorem sqrt13_sq : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)

theorem haagerupD_sq : haagerupD ^ 2 = 3 * haagerupD + 1 := by
  unfold haagerupD
  linear_combination (1 / 4 : ℝ) * sqrt13_sq

theorem haagerupD_pos : 0 < haagerupD := by
  unfold haagerupD
  have := Real.sqrt_nonneg 13
  linarith

theorem haagerupS_eq : haagerupS = (13 + 3 * Real.sqrt 13) / 2 := by
  unfold haagerupS haagerupD
  linear_combination (1 / 4 : ℝ) * sqrt13_sq

/-- `d_X = d² = (11 + 3√13)/2`. -/
theorem haagerup_dX : haagerupD ^ 2 = (11 + 3 * Real.sqrt 13) / 2 := by
  unfold haagerupD
  linear_combination (1 / 4 : ℝ) * sqrt13_sq

/-- `m = 1` instance of `rank6_center_count`: `∑ n_j² = 6`. -/
theorem haagerup_center_count (S : ℝ) :
    9 * haagerupS ^ 2 = 1 + haagerupD ^ 4 + 4 * haagerupS ^ 2 + 9 * haagerupD ^ 2 * S ↔
      S = 6 := by
  have h := rank6_center_count 1 haagerupD S (by rw [haagerupD_sq]; ring)
  unfold haagerupS
  rw [h]
  norm_num

/-- `Dim(𝓗₃) = 1 + 1 + 1 + 3d² = 3s`. -/
theorem haagerup_global_dim : 1 + 1 + 1 + 3 * haagerupD ^ 2 = 3 * haagerupS := by
  unfold haagerupS
  ring

/-- The twelve center dimensions `1, d², s, s, s, s, 3d (×6)` have total squared
dimension `9 s² = Dim(𝓗₃)²`. -/
theorem haagerup_center_dims :
    1 + (haagerupD ^ 2) ^ 2 + 4 * haagerupS ^ 2 + 6 * (3 * haagerupD) ^ 2 =
      9 * haagerupS ^ 2 ∧ 9 * haagerupS ^ 2 = (3 * haagerupS) ^ 2 := by
  constructor
  · have h := (haagerup_center_count 6).mpr rfl
    linear_combination -h
  · ring

/-- Total squared dimension of the bimodule category `𝓗₃ ⊠ 𝓗₃^op`:
`∑_{x,y} (d_x d_y)² = (∑_x d_x²)²`. -/
theorem sum_sq_pairs {κ : Type*} [Fintype κ] (dim : κ → ℝ) :
    ∑ p : κ × κ, (dim p.1 * dim p.2) ^ 2 = (∑ i, dim i ^ 2) ^ 2 := by
  rw [Fintype.sum_prod_type, sq (∑ i, dim i ^ 2), Fintype.sum_mul_sum]
  simp [mul_pow]

/-- There are `6 · 6 = 36` simple defects labelled by ordered pairs. -/
theorem defect_count {κ : Type*} [Fintype κ] (h : Fintype.card κ = 6) :
    Fintype.card (κ × κ) = 36 := by
  simp [Fintype.card_prod, h]

/-- The `𝓗₃` dimensions `1, 1, 1, d, d, d` have `∑ d_x² = 3s`, so the 36 defects have
total squared dimension `(3s)² = 9 s² = Dim Rep(U)`. -/
theorem haagerup_defect_dims :
    ((1 : ℝ) ^ 2 + 1 ^ 2 + 1 ^ 2 + haagerupD ^ 2 + haagerupD ^ 2 + haagerupD ^ 2) ^ 2 =
      9 * haagerupS ^ 2 := by
  unfold haagerupS
  ring

/-! ### Vanishing of the obstruction groups -/

/-- Every complex number has a cube root. -/
theorem complex_cube_root (z : ℂ) : ∃ w : ℂ, w ^ 3 = z :=
  IsAlgClosed.exists_pow_nat_eq z (by norm_num)

/-- `ℂˣ = (ℂˣ)³`, i.e. `ℂˣ/(ℂˣ)³ = 0`: the cube map on `ℂˣ` is surjective.  With the
standard identification `H²(ℤ/3, ℂˣ) ≅ ℂˣ/(ℂˣ)³` (trivial action) this is the vanishing
used for the Izumi obstruction (line 4966). -/
theorem units_cube_surjective (z : ℂˣ) : ∃ w : ℂˣ, w ^ 3 = z := by
  obtain ⟨w, hw⟩ := complex_cube_root (z : ℂ)
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw
    exact z.ne_zero (hw.symm.trans (by norm_num))
  refine ⟨Units.mk0 w hw0, ?_⟩
  ext
  simp [hw]

/-- `(ℤ/3)/2(ℤ/3) = 0`: multiplication by two is surjective on `ℤ/3` (line 4969). -/
theorem zmod3_two_mul_surjective : ∀ x : ZMod 3, ∃ y : ZMod 3, x = 2 * y := by
  decide

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.rank6_center_count
#print axioms HaagerupIzumi.C8.Fusion.haagerup_center_dims
#print axioms HaagerupIzumi.C8.Fusion.sum_sq_pairs
#print axioms HaagerupIzumi.C8.Fusion.units_cube_surjective
#print axioms HaagerupIzumi.C8.Fusion.zmod3_two_mul_surjective
