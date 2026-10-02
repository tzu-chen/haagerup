module

public import HaagerupIzumi.C8.Fusion.NearGroup
public import HaagerupIzumi.C8.CenterDimension
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Lemma `lem:m6-balanced` from the Verlinde formula and signed Galois symmetry

Lemma `lem:m6-balanced` (lines 3516–3548 of `c8_expanded_20260929/haagerup_c8_expanded.tex`):
*in Lemma `lem:near-group-induction` with `k = 2`, the balanced pattern `p = q = 1` is
impossible.*  `Fusion.m6_balanced_impossible` proves this from the hypothesis `hVerlinde`, the
Verlinde formula already evaluated on the rows forced by Galois symmetry.  This file replaces that
hypothesis by the cited statements themselves, for an abstract `S`-matrix:

* `VerlindeFormula S 𝟏 N`: `N_{ij}^k = ∑_m S_{im} S_{jm} \overline{S_{km}} / S_{𝟏m}` (Verlinde's
  formula for the modular data of `Z(𝓕)`; external);
* `hS0`: the vacuum row is `S_{𝟏j} = d_j / Dim 𝓕` with `Dim 𝓕 = ∑_x d_x²` over the simples of
  `𝓕` (normalized `S`-matrix of the center, positive dimensions; external);
* `hZ`: `Dim Z(𝓕) = (Dim 𝓕)²` (Müger; `CenterDimension.CenterDimensionFormula`, external), which
  gives `∑ n_j² = 22` (`CenterDimension.nearGroup_length_of_center` at `k = 2`, `p = q = 1`);
* `SignedGaloisSymmetry S 𝟏`: **Dong–Lin–Ng, Theorem II(iii)** for the vacuum row and a Galois
  automorphism `σ` with `σ(√3) = -√3`: if every entry of the vacuum row lies in `ℚ(√3)`,
  `S_{𝟏j} = a_j + b_j √3`, then some row is `±σ` of it, `S_{Xj} = ε (a_j - b_j √3)`, `ε = ±1`
  (external);
* the dimensions of the balanced pattern: `1`, `1+2d`, three copies of `2r`, four copies of `r`,
  and `n_j d`, where `d = 3+2√3`, `r = 1+d` (the center simples of `lem:near-group-induction`
  at `k = 2`, `p = q = 1`, i.e. `CenterDimension.nearGroupCenterDim 2 1 1 d n`; manuscript
  lines 3522–3525).

Proved here: `Dim 𝓕 = 12(2+√3)` (`m6_DimF`) and the vacuum row is
`(u, v, 1/3, 1/3, 1/3, 1/6, 1/6, 1/6, 1/6, n_j√3/12)` (`m6_vacuum_row`); the forced row is
`ε (v, u, 1/3, …, 1/6, -n_j√3/12)`; Verlinde gives `N_{XX}^X = ε · 4/3`
(`verlinde_real_row`, `m6_balanced_verlinde`), which is not a natural number
(`m6_balanced_impossible_of_modular`).  The sign `ε` need not be determined, and self-duality of
`X` is not needed: the forced row is real.
-/

namespace HaagerupIzumi.C8.Fusion

open scoped ComplexConjugate

section General

variable {I : Type*} [Fintype I]

/-- **The Verlinde formula** for an `S`-matrix with unit `𝟏` and fusion coefficients `N`:
`N_{ij}^k = ∑_m S_{im} S_{jm} \overline{S_{km}} / S_{𝟏m}`. -/
def VerlindeFormula (S : I → I → ℂ) (unit : I) (N : I → I → I → ℕ) : Prop :=
  ∀ i j k, (N i j k : ℂ) = ∑ m, S i m * S j m * conj (S k m) / S unit m

/-- **Signed Galois symmetry of the vacuum row** (Dong–Lin–Ng, Theorem II(iii)), for a Galois
automorphism `σ` with `σ(√3) = -√3`: if the vacuum row lies in `ℚ(√3)`, `S_{𝟏j} = a_j + b_j√3`,
then for some simple `X` and sign `ε`, `S_{Xj} = ε σ(S_{𝟏j}) = ε (a_j - b_j√3)` for all `j`. -/
def SignedGaloisSymmetry (S : I → I → ℂ) (unit : I) : Prop :=
  ∀ a b : I → ℚ, (∀ j, S unit j = (((a j : ℝ) + (b j : ℝ) * Real.sqrt 3 : ℝ) : ℂ)) →
    ∃ (X : I) (ε : ℤ), (ε = 1 ∨ ε = -1) ∧
      ∀ j, S X j = (ε : ℂ) * (((a j : ℝ) - (b j : ℝ) * Real.sqrt 3 : ℝ) : ℂ)

/-- Verlinde's formula for `N_{XX}^X` along a real row: if `S_{𝟏m} = y_m` and
`S_{Xm} = ε x_m` with `x, y` real and `ε = ±1`, then `N_{XX}^X = ε ∑_m x_m³ / y_m`. -/
theorem verlinde_real_row (S : I → I → ℂ) (unit : I) (N : I → I → I → ℕ)
    (hV : VerlindeFormula S unit N) (x y : I → ℝ) (hrow : ∀ m, S unit m = (y m : ℂ))
    {X : I} {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (hX : ∀ m, S X m = (ε : ℂ) * (x m : ℂ)) :
    (N X X X : ℝ) = ε * ∑ m, x m ^ 3 / y m := by
  have hε3 : (ε : ℂ) ^ 3 = ε := by rcases hε with h | h <;> subst h <;> norm_num
  have key : (N X X X : ℂ) = ((ε * ∑ m, x m ^ 3 / y m : ℝ) : ℂ) := by
    rw [hV X X X]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hX m, hrow m, map_mul, map_intCast, Complex.conj_ofReal]
    linear_combination ((x m : ℂ) ^ 3 / (y m : ℂ)) * hε3
  exact_mod_cast key

end General

/-! ### The balanced multiplicity-six pattern -/

section M6

variable {J : Type*} [Fintype J]

/-- `d = 3 + 2√3`. -/
noncomputable def m6d : ℝ := 3 + 2 * Real.sqrt 3

/-- `d² = 3 + 3kd` with `k = 2`. -/
theorem m6d_sq : m6d ^ 2 = 3 + 3 * ((2 : ℕ) : ℝ) * m6d := by
  unfold m6d
  push_cast
  linear_combination 4 * sqrt3_sq

/-- `Dim 𝓕 = 3 + d² = 12 (2 + √3)`. -/
theorem m6_DimF :
    ∑ x, CenterDimension.nearGroupFusionDim m6d x ^ 2 = 12 * (2 + Real.sqrt 3) := by
  rw [CenterDimension.nearGroup_DimF 2 m6d m6d_sq]
  unfold m6d
  push_cast
  ring

/-- Rational parts of the normalized vacuum row. -/
def m6a : Fin 9 ⊕ J → ℚ :=
  Sum.elim ![1 / 6, 1 / 6, 1 / 3, 1 / 3, 1 / 3, 1 / 6, 1 / 6, 1 / 6, 1 / 6] (fun _ => 0)

/-- `√3`-parts of the normalized vacuum row. -/
def m6b (n : J → ℕ) : Fin 9 ⊕ J → ℚ :=
  Sum.elim ![-1 / 12, 1 / 12, 0, 0, 0, 0, 0, 0, 0] (fun j => (n j : ℚ) / 12)

omit [Fintype J] in
/-- **The normalized vacuum row** (lines 3527–3530): `d_j / Dim 𝓕 = a_j + b_j √3`, i.e.
`(u, v, 1/3, 1/3, 1/3, 1/6, 1/6, 1/6, 1/6, n_j√3/12)`. -/
theorem m6_vacuum_row (n : J → ℕ) (j : Fin 9 ⊕ J) :
    CenterDimension.nearGroupCenterDim 2 1 1 m6d n j / (12 * (2 + Real.sqrt 3)) =
      ((m6a j : ℚ) : ℝ) + ((m6b n j : ℚ) : ℝ) * Real.sqrt 3 := by
  have hD : (12 * (2 + Real.sqrt 3)) ≠ 0 := by positivity
  rw [div_eq_iff hD]
  rcases j with i | j
  · fin_cases i <;> simp [CenterDimension.nearGroupCenterDim, m6a, m6b, m6d] <;>
      first
        | linear_combination (0 : ℝ) * sqrt3_sq
        | linear_combination sqrt3_sq
        | linear_combination -sqrt3_sq
  · simp only [CenterDimension.nearGroupCenterDim, m6a, m6b, Sum.elim_inr, m6d]
    push_cast
    linear_combination -(n j : ℝ) * sqrt3_sq

/-- The Verlinde sum along the vacuum row and its `√3`-conjugate is `4/3`
(lines 3539–3545). -/
theorem m6_conjugate_sum (n : J → ℕ) (hn : ∀ j, n j ≠ 0) (hsum : ∑ j, (n j : ℝ) ^ 2 = 22) :
    ∑ m, ((((m6a m : ℚ) : ℝ) - ((m6b n m : ℚ) : ℝ) * Real.sqrt 3) ^ 3 /
      (((m6a m : ℚ) : ℝ) + ((m6b n m : ℚ) : ℝ) * Real.sqrt 3)) = 4 / 3 := by
  rw [← m6_balanced_verlinde n hn hsum, Fintype.sum_sum_type]
  simp only [m6a, m6b, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  have hJ : ∀ j, ((((0 : ℚ) : ℝ) - (((n j : ℚ) / 12 : ℚ) : ℝ) * Real.sqrt 3) ^ 3 /
      (((0 : ℚ) : ℝ) + (((n j : ℚ) / 12 : ℚ) : ℝ) * Real.sqrt 3)) =
      (-(n j : ℝ) * Real.sqrt 3 / 12) ^ 3 / ((n j : ℝ) * Real.sqrt 3 / 12) := by
    intro j
    push_cast
    congr 1 <;> ring
  rw [Finset.sum_congr rfl fun j _ => hJ j]
  have hu : ((1 / 6 : ℚ) : ℝ) + ((-1 / 12 : ℚ) : ℝ) * Real.sqrt 3 = m6u := by
    unfold m6u; push_cast; ring
  have hu' : ((1 / 6 : ℚ) : ℝ) - ((1 / 12 : ℚ) : ℝ) * Real.sqrt 3 = m6u := by
    unfold m6u; push_cast; ring
  have hv : ((1 / 6 : ℚ) : ℝ) + ((1 / 12 : ℚ) : ℝ) * Real.sqrt 3 = m6v := by
    unfold m6v; push_cast; ring
  have hv' : ((1 / 6 : ℚ) : ℝ) - ((-1 / 12 : ℚ) : ℝ) * Real.sqrt 3 = m6v := by
    unfold m6v; push_cast; ring
  rw [hu, hu', hv, hv']
  push_cast
  ring

/-- **Lemma `lem:m6-balanced`** (lines 3516–3548), from the cited statements.  Let `S` be an
`S`-matrix on the center simples `Fin 9 ⊕ J` of the balanced pattern (unit `inl 0`, dimensions
`CenterDimension.nearGroupCenterDim 2 1 1 d n`, all `n_j ≠ 0`) whose fusion coefficients obey the
Verlinde formula, with `Dim Z(𝓕) = (Dim 𝓕)²`, vacuum row `d_j / Dim 𝓕`, and signed Galois
symmetry (DLN II(iii)).  Then `False`: `∑ n_j² = 22`, and the conjugate row forces
`N_{XX}^X = ±4/3`. -/
theorem m6_balanced_impossible_of_modular (n : J → ℕ) (hn : ∀ j, n j ≠ 0)
    (S : Fin 9 ⊕ J → Fin 9 ⊕ J → ℂ) (N : Fin 9 ⊕ J → Fin 9 ⊕ J → Fin 9 ⊕ J → ℕ)
    (hV : VerlindeFormula S (Sum.inl 0) N)
    (hZ : CenterDimension.CenterDimensionFormula (CenterDimension.nearGroupCenterDim 2 1 1 m6d n)
      (∑ x, CenterDimension.nearGroupFusionDim m6d x ^ 2))
    (hS0 : ∀ j, S (Sum.inl 0) j = ((CenterDimension.nearGroupCenterDim 2 1 1 m6d n j /
      ∑ x, CenterDimension.nearGroupFusionDim m6d x ^ 2 : ℝ) : ℂ))
    (hDLN : SignedGaloisSymmetry S (Sum.inl 0)) : False := by
  have hsum : ∑ j, (n j : ℝ) ^ 2 = 22 := by
    rw [CenterDimension.nearGroup_length_of_center 2 1 1 rfl m6d m6d_sq n hZ]
    norm_num
  have hrow : ∀ j, S (Sum.inl 0) j =
      ((((m6a j : ℚ) : ℝ) + ((m6b n j : ℚ) : ℝ) * Real.sqrt 3 : ℝ) : ℂ) := by
    intro j
    rw [hS0 j, m6_DimF, m6_vacuum_row n j]
  obtain ⟨X, ε, hε, hX⟩ := hDLN m6a (m6b n) hrow
  have h := verlinde_real_row S (Sum.inl 0) N hV
    (fun m => ((m6a m : ℚ) : ℝ) - ((m6b n m : ℚ) : ℝ) * Real.sqrt 3)
    (fun m => ((m6a m : ℚ) : ℝ) + ((m6b n m : ℚ) : ℝ) * Real.sqrt 3) hrow hε hX
  rw [m6_conjugate_sum n hn hsum] at h
  rcases hε with rfl | rfl
  · exact four_thirds_ne_int (N X X X : ℤ) (by push_cast at h ⊢; linarith)
  · have h0 : (0 : ℝ) ≤ (N X X X : ℝ) := Nat.cast_nonneg _
    push_cast at h
    linarith

end M6

#print axioms verlinde_real_row
#print axioms m6_vacuum_row
#print axioms m6_conjugate_sum
#print axioms m6_balanced_impossible_of_modular

end HaagerupIzumi.C8.Fusion
