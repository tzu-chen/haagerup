module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The weight-two spectra and the positive-stress arithmetic

Finite data of `c8_expanded_20260929/haagerup_c8_expanded.tex`:

* Certificate `cert:initial` and the table after `eq:two-coset-stresses`
  (lines 2021–2091): the eight charged current multiplets with current
  dimensions `(n,m)` (`leftDim`, `rightDim`) and their exact `e₁`, `f₁`
  eigenvalues (`eEigen`, `fEigen`).  Each row satisfies
  `(n²-1)/12 + (m²-1)/164 + h_e + h_f = 2` (`multiplet_weight_two`); the
  first two terms are the Sugawara weights of `A_{1,1}` and `A_{1,39}`
  (`sugawaraWeight_one_dim`, `sugawaraWeight_39_dim`).  The multiplet
  dimensions sum to `96` and `22 + 2 + 96 = 120`, with `22 = 4 + 9 + 3·3`.
* The positive-stress coefficient (lines 2688–2710 and 3134–3150):
  `(3/164)·(3403/4563) = 83/6084` (`stress_coefficient`), and for an
  irreducible `sl₂`-module of highest weight `r`,
  `∑_{k=0}^{r} (r-2k)² = r(r+1)(r+2)/3` (`sum_sq_weights`), hence
  `Tr H²/dim = r(r+2)/3` (`trace_H_sq_div_dim`) and the Sugawara energy
  `L₀^{A_{1,39}} = r(r+2)/164` (`sugawaraWeight_39`); the Sugawara trace is
  `3Q/164` (`sugawara_trace`) and the stress trace coefficient `83Q/6084`
  (`sugawara_trace_scaled`).  The independent check of line 3181 is
  `topW_check`.

All statements are hypothesis-free arithmetic.  The identification of these
numbers with eigenvalues of actual fields is the content of the exact
certificates cited in the manuscript and is not asserted here.
-/

namespace HaagerupIzumi.C8
namespace Spectra

open Finset

/-! ## The eight charged multiplets -/

/-- Left current dimension `n` of the eight primitive charged fields. -/
def leftDim : Fin 8 → ℕ := ![1, 1, 1, 1, 2, 2, 2, 2]

/-- Right current dimension `m` of the eight primitive charged fields. -/
def rightDim : Fin 8 → ℕ := ![5, 9, 9, 13, 2, 6, 8, 14]

/-- The `e₁` eigenvalues (line 2068). -/
def eEigen : Fin 8 → ℚ :=
  ![798 / 1271, 200 / 1271, 1512 / 1271, 420 / 1271, 192 / 1271, 1830 / 1271, 752 / 1271,
    180 / 1271]

/-- The `f₁` eigenvalues (line 2068). -/
def fEigen : Fin 8 → ℚ := ![38 / 31, 42 / 31, 10 / 31, 20 / 31, 49 / 31, 3 / 31, 24 / 31, 13 / 31]

/-- Sugawara weight `r(r+2)/(4(k+2))` of the irreducible of highest weight `r`
(spin `r/2`) at level `k`. -/
def sugawaraWeight (k r : ℚ) : ℚ := r * (r + 2) / (4 * (k + 2))

/-- For current dimension `n` (highest weight `n-1`) at level one. -/
theorem sugawaraWeight_one_dim (n : ℚ) : sugawaraWeight 1 (n - 1) = (n ^ 2 - 1) / 12 := by
  unfold sugawaraWeight; ring

/-- For current dimension `m` (highest weight `m-1`) at level thirty-nine. -/
theorem sugawaraWeight_39_dim (m : ℚ) : sugawaraWeight 39 (m - 1) = (m ^ 2 - 1) / 164 := by
  unfold sugawaraWeight; ring

/-- `L₀^{A_{1,39}} = r(r+2)/164` (line 3147). -/
theorem sugawaraWeight_39 (r : ℚ) : sugawaraWeight 39 r = r * (r + 2) / 164 := by
  unfold sugawaraWeight; ring

/-- Every row of the table obeys `(n²-1)/12 + (m²-1)/164 + h_e + h_f = 2`. -/
theorem multiplet_weight_two :
    ∀ i : Fin 8, ((leftDim i : ℚ) ^ 2 - 1) / 12 + ((rightDim i : ℚ) ^ 2 - 1) / 164
      + eEigen i + fEigen i = 2 := by
  intro i
  fin_cases i <;> norm_num [leftDim, rightDim, eEigen, fEigen]

/-- The same, with the affine contributions written as Sugawara weights. -/
theorem multiplet_weight_two_sugawara (i : Fin 8) :
    sugawaraWeight 1 ((leftDim i : ℚ) - 1) + sugawaraWeight 39 ((rightDim i : ℚ) - 1)
      + eEigen i + fEigen i = 2 := by
  rw [sugawaraWeight_one_dim, sugawaraWeight_39_dim]
  exact multiplet_weight_two i

/-- The current multiplets contribute `96` vectors. -/
theorem multiplet_dim_sum : ∑ i, leftDim i * rightDim i = 96 := by decide

/-- Weight-two states of the universal affine `sl₂` vacuum module:
`J^a_{-2}𝟙` (three) and `J^a_{-1}J^b_{-1}𝟙` (`Sym²` of three, six). -/
theorem universal_affine_weight_two : 3 + Nat.choose 4 2 = 9 := by decide

/-- At level one the null multiplet (dimension five) leaves four states. -/
theorem level_one_weight_two : 9 - 5 = 4 := by decide

/-- The affine vacuum space contributes `22 = 4 + 9 + 3·3` in weight two. -/
theorem affine_vacuum_weight_two : 4 + 9 + 3 * 3 = 22 := by decide

/-- `dim S₂ = 22 + 2 + 96 = 120`. -/
theorem initial_space_dim : (4 + 9 + 3 * 3) + 2 + ∑ i, leftDim i * rightDim i = 120 := by
  decide

/-- `dim S₃ = dim N₃ + dim (S₃/N₃)`: `956 = 634 + 322`. -/
theorem grade_three_dims : 634 + 322 = 956 := by decide

/-! ## The positive-stress arithmetic -/

/-- `(3/164)·(3403/4563) = 83/6084`. -/
theorem stress_coefficient : (3 / 164 : ℚ) * (3403 / 4563) = 83 / 6084 := by norm_num

/-- Auxiliary closed form for `∑_{k<n} (A - 2k)²`. -/
theorem sum_sq_shift (A : ℚ) (n : ℕ) :
    ∑ k ∈ range n, (A - 2 * k) ^ 2 =
      n * A ^ 2 - 2 * A * n * (n - 1) + 2 * (n - 1) * n * (2 * n - 1) / 3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- The weights of the irreducible `sl₂`-module of highest weight `r` are
`r - 2k`, `0 ≤ k ≤ r`, and `∑_{k=0}^{r} (r-2k)² = r(r+1)(r+2)/3`. -/
theorem sum_sq_weights (r : ℕ) :
    ∑ k ∈ range (r + 1), ((r : ℚ) - 2 * k) ^ 2 = (r : ℚ) * (r + 1) * (r + 2) / 3 := by
  rw [sum_sq_shift]
  push_cast
  ring

/-- `Tr H²/dim = r(r+2)/3` (line 3146). -/
theorem trace_H_sq_div_dim (r : ℕ) :
    (∑ k ∈ range (r + 1), ((r : ℚ) - 2 * k) ^ 2) / ((r : ℚ) + 1) = (r : ℚ) * (r + 2) / 3 := by
  have hr : (r : ℚ) + 1 ≠ 0 := by positivity
  rw [sum_sq_weights, div_eq_iff hr]
  ring

/-- The Sugawara trace on an irreducible right module is `3Q/164`, where
`Q = Tr H_R(0)²`. -/
theorem sugawara_trace (r : ℕ) :
    ((r : ℚ) + 1) * sugawaraWeight 39 r =
      3 / 164 * ∑ k ∈ range (r + 1), ((r : ℚ) - 2 * k) ^ 2 := by
  rw [sum_sq_weights, sugawaraWeight_39]
  ring

/-- Multiplying by `3403/4563` gives `83Q/6084` (line 3150). -/
theorem sugawara_trace_scaled (r : ℕ) :
    3403 / 4563 * (((r : ℚ) + 1) * sugawaraWeight 39 r) =
      83 / 6084 * ∑ k ∈ range (r + 1), ((r : ℚ) - 2 * k) ^ 2 := by
  rw [sugawara_trace]
  ring

/-- The independent check of line 3181: if `Z = h d - L - Q/156 - P`, then
`L + 83Q/6084 + 25P/6 + 25Z/26 = L/26 + 7Q/936 + 125P/39 + (25/26) h d`. -/
theorem topW_check (L Q P h d : ℚ) :
    L + 83 / 6084 * Q + 25 / 6 * P + 25 / 26 * (h * d - L - Q / 156 - P) =
      L / 26 + 7 * Q / 936 + 125 * P / 39 + 25 / 26 * (h * d) := by
  ring

#print axioms multiplet_weight_two
#print axioms multiplet_weight_two_sugawara
#print axioms multiplet_dim_sum
#print axioms initial_space_dim
#print axioms stress_coefficient
#print axioms sum_sq_weights
#print axioms trace_H_sq_div_dim
#print axioms sugawaraWeight_39
#print axioms sugawara_trace
#print axioms sugawara_trace_scaled
#print axioms topW_check

end Spectra
end HaagerupIzumi.C8
