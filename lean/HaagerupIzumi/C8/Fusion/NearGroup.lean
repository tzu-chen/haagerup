module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Arithmetic of the rank-four (near-group) exclusion

Appendix G of `c8_expanded_20260929/haagerup_c8_expanded.tex`, subsection
"Excluding rank four" (lines 3356–3790).  This file proves the purely
arithmetic steps; the categorical inputs are *not* proved and enter only as
explicit hypotheses of the theorems below.

* `nearGroup_dim_sq`: `ρ² = 1 + a + a² + mρ` and `d(a) = d(a²) = 1` give
  `d² = 3 + m d` for any dimension character (line 3358).
* `nearGroup_length`: the center-dimension count, eq:near-group-length
  (line 3409): from
  `9s² = 1 + (1+kd)² + 3s² + 2(1+pd)² + 2(1+qd)² + d² ∑ n_j²`,
  `d² = 3 + 3kd`, `s = 2 + kd`, `p + q = k` one gets
  `∑ n_j² = 6 + 3k² + 4pq`.  The displayed identity is the global-dimension
  formula `Dim Z(𝓕) = (Dim 𝓕)²` applied to the forgetful images listed in
  Lemma `lem:near-group-induction`, whose determination uses Ostrik's
  induction/formal-codegree correspondence and the Ng–Schauenburg twist
  formula (external; supplied as the hypothesis `hcenter`).  `CenterDimension.nearGroup_length_of_center`
  derives it from `Dim Z(𝓕) = (Dim 𝓕)²` stated for the list of center simples.
* `nearGroup_m0`: `m = 0` gives `s = 2`, hence `d_X = s - 1 = 1` (line 3366).
* `m6_balanced_*`: Lemma `lem:m6-balanced` (lines 3516–3548).  With
  `u = (2-√3)/12`, `v = (2+√3)/12` one has `u+v = 1/3`, `uv = 1/144`, and the
  Verlinde sum for `N_{XX}^X` along the rows forced by signed Galois symmetry
  equals `v³/u + u³/v + 3/9 + 4/36 - 22/48 = 4/3`, which is not an integer.
  The Galois symmetry of the `S`-matrix (Dong–Lin–Ng, Theorem II(iii)) and the
  Verlinde formula are external and enter as the hypothesis `hVerlinde`;
  `Fusion.m6_balanced_impossible_of_modular` (`Fusion/M6BalancedModular.lean`) derives the
  forced rows and the value from the Verlinde formula, `S_{𝟏j} = d_j/Dim 𝓕` and DLN II(iii)
  stated generally.
* `current_obstruction_*`: the final arithmetic of Proposition
  `prop:near-group-current-obstructions` (lines 3614–3770).  The theta-series
  identities themselves (pole cancellation, Weil representations) are
  external; only the vacuum-coefficient arithmetic is proved here.
-/

namespace HaagerupIzumi.C8.Fusion

/-! ### (i) Near-group dimensions and the center-dimension count -/

/-- For the near-group rule `ρ² = 1 + a + a² + mρ`, any dimension function with
`d(a) = d(a²) = 1` satisfies `d(ρ)² = 3 + m d(ρ)`. -/
theorem nearGroup_dim_sq (d m da db : ℝ) (ha : da = 1) (hb : db = 1)
    (hrho : d * d = 1 + da + db + m * d) : d ^ 2 = 3 + m * d := by
  rw [ha, hb] at hrho
  linear_combination hrho

/-- eq:near-group-length (line 3409).  The center-dimension identity
`Dim Z(𝓕) = (Dim 𝓕)² = 9 s²`, written out for the known simples
`1, X, Y, Y', C, D, D', E, E'` and the residual simples `Z_j` with forgetful
images `n_j ρ`, forces `∑ n_j² = 6 + 3k² + 4pq`. -/
theorem nearGroup_length (k p q d s S : ℝ) (hd : d ^ 2 = 3 + 3 * k * d)
    (hs : s = 2 + k * d) (hpq : p + q = k) (hd0 : d ≠ 0)
    (hcenter : 9 * s ^ 2 = 1 + (1 + k * d) ^ 2 + 3 * s ^ 2 + 2 * (1 + p * d) ^ 2 +
      2 * (1 + q * d) ^ 2 + d ^ 2 * S) :
    S = 6 + 3 * k ^ 2 + 4 * p * q := by
  have h1 : d ^ 2 * (S - (6 + 3 * k ^ 2 + 4 * p * q)) = 0 := by
    subst hs
    subst hpq
    linear_combination (-1 : ℝ) * hcenter + (-6 : ℝ) * hd
  have hd2 : d ^ 2 ≠ 0 := pow_ne_zero 2 hd0
  have h3 := (mul_eq_zero.mp h1).resolve_left hd2
  linarith

/-- For `m = 0` (that is, `k = 0`), `s = 2 + 0·d = 2` and `d_X = s - 1 = 1`,
contradicting Lemma `lem:no-sign-extension` (line 3366). -/
theorem nearGroup_m0 (d s dX : ℝ) (hs : s = 2 + 0 * d) (hX : dX = s - 1) :
    s = 2 ∧ dX = 1 := by
  refine ⟨by rw [hs]; ring, by rw [hX, hs]; ring⟩

/-! ### (ii) Lemma `lem:m6-balanced` -/

/-- `u = (2 - √3)/12`. -/
noncomputable def m6u : ℝ := (2 - Real.sqrt 3) / 12

/-- `v = (2 + √3)/12`. -/
noncomputable def m6v : ℝ := (2 + Real.sqrt 3) / 12

theorem sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem m6u_add_m6v : m6u + m6v = 1 / 3 := by
  unfold m6u m6v; ring

theorem m6u_mul_m6v : m6u * m6v = 1 / 144 := by
  unfold m6u m6v
  linear_combination (-1 / 144 : ℝ) * sqrt3_sq

theorem m6u_ne_zero : m6u ≠ 0 := by
  unfold m6u
  intro h
  have hs : Real.sqrt 3 = 2 := by linarith
  have h3 := sqrt3_sq
  rw [hs] at h3
  norm_num at h3

theorem m6v_ne_zero : m6v ≠ 0 := by
  unfold m6v
  have := Real.sqrt_nonneg 3
  positivity

/-- The Galois-symmetric part of the Verlinde sum (line 3541):
`v³/u + u³/v + 3/9 + 4/36 - 22/48 = 4/3`. -/
theorem m6_balanced_value :
    m6v ^ 3 / m6u + m6u ^ 3 / m6v + 3 / 9 + 4 / 36 - 22 / 48 = 4 / 3 := by
  have h1 : m6v ^ 3 / m6u = 144 * m6v ^ 4 := by
    rw [div_eq_iff m6u_ne_zero]
    linear_combination (-144 * m6v ^ 3) * m6u_mul_m6v
  have h2 : m6u ^ 3 / m6v = 144 * m6u ^ 4 := by
    rw [div_eq_iff m6v_ne_zero]
    linear_combination (-144 * m6u ^ 3) * m6u_mul_m6v
  rw [h1, h2]
  unfold m6u m6v
  linear_combination (Real.sqrt 3 ^ 2 + 27) / 72 * sqrt3_sq

/-- The residual columns of the vacuum and `X` rows, `n_j √3/12` and
`-n_j √3/12`, contribute `-∑ n_j² · 3/144 = -22/48` when `∑ n_j² = 22`. -/
theorem m6_balanced_residual_sum {J : Type*} [Fintype J] (n : J → ℕ) (hn : ∀ j, n j ≠ 0)
    (hsum : ∑ j, (n j : ℝ) ^ 2 = 22) :
    ∑ j, (-(n j : ℝ) * Real.sqrt 3 / 12) ^ 3 / ((n j : ℝ) * Real.sqrt 3 / 12) =
      -22 / 48 := by
  have hs : Real.sqrt 3 ≠ 0 := by
    intro h
    have h3 := sqrt3_sq
    rw [h] at h3
    norm_num at h3
  have hterm : ∀ j, (-(n j : ℝ) * Real.sqrt 3 / 12) ^ 3 / ((n j : ℝ) * Real.sqrt 3 / 12) =
      -(3 / 144) * (n j : ℝ) ^ 2 := by
    intro j
    have hnj : (n j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hn j)
    rw [div_eq_iff (div_ne_zero (mul_ne_zero hnj hs) (by norm_num))]
    linear_combination (-(n j : ℝ) ^ 3 * Real.sqrt 3 / 1728) * sqrt3_sq
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, hsum]
  norm_num

/-- The full Verlinde expression for `N_{XX}^X` along the vacuum row
`(u, v, 1/3, 1/3, 1/3, 1/6, 1/6, 1/6, 1/6, n_j √3/12)` and the `X` row
`(v, u, 1/3, 1/3, 1/3, 1/6, 1/6, 1/6, 1/6, -n_j √3/12)` equals `4/3`. -/
theorem m6_balanced_verlinde {J : Type*} [Fintype J] (n : J → ℕ) (hn : ∀ j, n j ≠ 0)
    (hsum : ∑ j, (n j : ℝ) ^ 2 = 22) :
    m6v ^ 3 / m6u + m6u ^ 3 / m6v + 3 * ((1 / 3 : ℝ) ^ 3 / (1 / 3)) +
      4 * ((1 / 6 : ℝ) ^ 3 / (1 / 6)) +
      ∑ j, (-(n j : ℝ) * Real.sqrt 3 / 12) ^ 3 / ((n j : ℝ) * Real.sqrt 3 / 12) = 4 / 3 := by
  rw [m6_balanced_residual_sum n hn hsum]
  have e1 : (3 : ℝ) * ((1 / 3 : ℝ) ^ 3 / (1 / 3)) = 3 / 9 := by norm_num
  have e2 : (4 : ℝ) * ((1 / 6 : ℝ) ^ 3 / (1 / 6)) = 4 / 36 := by norm_num
  rw [e1, e2]
  linarith [m6_balanced_value]

theorem four_thirds_ne_int (N : ℤ) : (N : ℝ) ≠ 4 / 3 := by
  intro h
  have h3 : ((3 * N : ℤ) : ℝ) = 4 := by push_cast; rw [h]; norm_num
  have h4 : 3 * N = 4 := by exact_mod_cast h3
  omega

/-- Lemma `lem:m6-balanced`: the balanced pattern `p = q = 1` is impossible.
`hVerlinde` is the Verlinde formula for the fusion coefficient `N_{XX}^X`
evaluated on the rows forced by signed Galois symmetry (DLN, Theorem II(iii));
it is an external input here.  `m6_balanced_impossible_of_modular` replaces it by the cited
statements themselves. -/
theorem m6_balanced_impossible {J : Type*} [Fintype J] (n : J → ℕ) (hn : ∀ j, n j ≠ 0)
    (hsum : ∑ j, (n j : ℝ) ^ 2 = 22) (NXXX : ℕ)
    (hVerlinde : (NXXX : ℝ) = m6v ^ 3 / m6u + m6u ^ 3 / m6v + 3 * ((1 / 3 : ℝ) ^ 3 / (1 / 3)) +
      4 * ((1 / 6 : ℝ) ^ 3 / (1 / 6)) +
      ∑ j, (-(n j : ℝ) * Real.sqrt 3 / 12) ^ 3 / ((n j : ℝ) * Real.sqrt 3 / 12)) :
    False := by
  rw [m6_balanced_verlinde n hn hsum] at hVerlinde
  exact four_thirds_ne_int (NXXX : ℤ) (by exact_mod_cast hVerlinde)

/-! ### (v) The current obstructions -/

/-- `m = 3`, first orientation: `2(D - 22) = 2λ - 4μ` with `λ = 7 - A + 4B`,
`μ = 7 - A - 3B` gives `D = 15 + A + 10B`. -/
theorem current_obstruction_m3a (D A B : ℤ)
    (h : 2 * (D - 22) = 2 * (7 - A + 4 * B) - 4 * (7 - A - 3 * B)) :
    D = 15 + A + 10 * B := by omega

/-- `m = 3`, reverse orientation: `2D - 94 = -84 + 6(3 + 14A)` gives `D = 14 + 42A`. -/
theorem current_obstruction_m3b (D A : ℤ) (h : 2 * D - 94 = -84 + 6 * (3 + 14 * A)) :
    D = 14 + 42 * A := by omega

/-- `m = 6`, first orientation: `2(D - 16) = -2(8 - A)` gives `D = 8 + A`. -/
theorem current_obstruction_m6a (D A : ℤ) (h : 2 * (D - 16) = -2 * (8 - A)) :
    D = 8 + A := by omega

/-- `m = 6`, reverse orientation: `2D - 94 = -84 + 24P` gives `D = 5 + 12P`. -/
theorem current_obstruction_m6b (D P : ℤ) (h : 2 * D - 94 = -84 + 24 * P) :
    D = 5 + 12 * P := by omega

/-- None of the four obstructions allows `dim U₁ = 6` for nonnegative `A, B, P`. -/
theorem current_obstructions_ne_six (A B P : ℤ) (hA : 0 ≤ A) (hB : 0 ≤ B) (_hP : 0 ≤ P) :
    15 + A + 10 * B ≠ 6 ∧ 14 + 42 * A ≠ 6 ∧ 8 + A ≠ 6 ∧ 5 + 12 * P ≠ 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- Proposition `prop:near-group-current-obstructions`, arithmetic part: each of the
four vacuum-coefficient identities is incompatible with `dim U₁ = 6`. -/
theorem current_obstruction_six (A B P : ℤ) (hA : 0 ≤ A) (hB : 0 ≤ B) (_hP : 0 ≤ P) :
    ¬ (2 * ((6 : ℤ) - 22) = 2 * (7 - A + 4 * B) - 4 * (7 - A - 3 * B)) ∧
    ¬ (2 * (6 : ℤ) - 94 = -84 + 6 * (3 + 14 * A)) ∧
    ¬ (2 * ((6 : ℤ) - 16) = -2 * (8 - A)) ∧
    ¬ (2 * (6 : ℤ) - 94 = -84 + 24 * P) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.nearGroup_length
#print axioms HaagerupIzumi.C8.Fusion.m6_balanced_value
#print axioms HaagerupIzumi.C8.Fusion.m6_balanced_impossible
#print axioms HaagerupIzumi.C8.Fusion.current_obstruction_six
