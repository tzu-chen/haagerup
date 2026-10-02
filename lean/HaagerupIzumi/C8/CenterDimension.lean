module

public import HaagerupIzumi.C8.Fusion.Center
public import HaagerupIzumi.C8.Fusion.NearGroup
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The center-dimension counts from `Dim Z(𝓕) = (Dim 𝓕)²`

`Fusion.rank6_center_count` (lemma `lem:rank6-induction`, line 3900 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) and `Fusion.nearGroup_length`
(eq:near-group-length, line 3409) take the center-dimension identity already written out for
the known center simples (`hcenter`).  This file states the identity itself, for an arbitrary
index set of center simples, and proves the expansion:

* `CenterDimensionFormula dim Dim`: `∑_Z d_Z² = (Dim 𝓕)²` over the simples of `Z(𝓕)`
  (Müger: `Dim Z(𝓕) = (Dim 𝓕)²`; external);
* `Dim 𝓕 = ∑_x d_x²` over the simples of `𝓕`: `1, a, a², ρ, aρ, a²ρ` of dimensions
  `1, 1, 1, d, d, d` for eq:rank6-ring, `1, a, a², ρ` of dimensions `1, 1, 1, d` for the
  near-group ring; `rank6_DimF`, `nearGroup_DimF` evaluate it to `3s`;
* `rank6_length_of_center`: with center simples `𝟏, X, Y, C₀, C₁, C₂, Z_j` of dimensions
  `1, d², s, s, s, s, 3n_j d` (`s = 1 + d²`; lines 3838–3843, 3900–3903) one gets
  `∑ n_j² = 4m² + 2`;
* `nearGroup_length_of_center`: with center simples `𝟏, X, Y, Y', C, D, D', E, E', Z_j` of
  dimensions `1, 1+kd, s, s, s, 1+pd, 1+pd, 1+qd, 1+qd, n_j d` (`s = 2 + kd`; lines 3392–3409)
  one gets `∑ n_j² = 6 + 3k² + 4pq`.

The lists of center simples and their dimensions are the forgetful images of
`lem:rank6-induction` / `lem:near-group-induction` (Ostrik's induction–codegree correspondence;
external); that the list is complete except for the `Z_j` is part of that input.
-/

namespace HaagerupIzumi.C8.CenterDimension

/-- **`Dim Z(𝓕) = (Dim 𝓕)²`** (Müger), summed over the simple objects of the center. -/
def CenterDimensionFormula {ι : Type*} [Fintype ι] (dim : ι → ℝ) (DimF : ℝ) : Prop :=
  ∑ Z, dim Z ^ 2 = DimF ^ 2

/-- Dimensions of the simples `1, a, a², ρ, aρ, a²ρ` of eq:rank6-ring. -/
noncomputable def rank6FusionDim (d : ℝ) : Fin 6 → ℝ := ![1, 1, 1, d, d, d]

/-- `Dim 𝓕 = 3 + 3d² = 3s` for eq:rank6-ring. -/
theorem rank6_DimF (d : ℝ) : ∑ x, rank6FusionDim d x ^ 2 = 3 * (1 + d ^ 2) := by
  simp only [rank6FusionDim, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  ring

/-- Dimensions of the simples `1, a, a², ρ` of the near-group ring. -/
noncomputable def nearGroupFusionDim (d : ℝ) : Fin 4 → ℝ := ![1, 1, 1, d]

/-- `Dim 𝓕 = 3 + d² = 3(2 + kd) = 3s` for the near-group ring with `d² = 3 + 3kd`. -/
theorem nearGroup_DimF (k : ℕ) (d : ℝ) (hd : d ^ 2 = 3 + 3 * k * d) :
    ∑ x, nearGroupFusionDim d x ^ 2 = 3 * (2 + k * d) := by
  simp only [nearGroupFusionDim, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  linear_combination hd

variable {J : Type*} [Fintype J]

/-- Center dimensions for the rank-six ring: `1, d², s, s, s, s, 3 n_j d`. -/
noncomputable def rank6CenterDim (d : ℝ) (n : J → ℕ) : Fin 6 ⊕ J → ℝ :=
  Sum.elim ![1, d ^ 2, 1 + d ^ 2, 1 + d ^ 2, 1 + d ^ 2, 1 + d ^ 2] (fun j => 3 * (n j : ℝ) * d)

/-- **Lemma `lem:rank6-induction`, first equation** (lines 3846, 3900–3903), from `Dim Z(𝓕) = (Dim 𝓕)²`:
`∑ n_j² = 4m² + 2`. -/
theorem rank6_length_of_center (m : ℕ) (d : ℝ) (hd : d ^ 2 = 3 * m * d + 1) (n : J → ℕ)
    (hZ : CenterDimensionFormula (rank6CenterDim d n) (∑ x, rank6FusionDim d x ^ 2)) :
    ∑ j, (n j : ℝ) ^ 2 = 4 * m ^ 2 + 2 := by
  unfold CenterDimensionFormula at hZ
  rw [rank6_DimF] at hZ
  rw [Fintype.sum_sum_type] at hZ
  simp only [rank6CenterDim, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ] at hZ
  have hJ : ∑ j, (3 * (n j : ℝ) * d) ^ 2 = 9 * d ^ 2 * ∑ j, (n j : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hJ] at hZ
  exact (Fusion.rank6_center_count (m : ℝ) d _ hd).1 (by linear_combination -hZ)

/-- Center dimensions for the near-group ring:
`1, 1+kd, s, s, s, 1+pd, 1+pd, 1+qd, 1+qd, n_j d` with `s = 2 + kd`. -/
noncomputable def nearGroupCenterDim (k p q : ℕ) (d : ℝ) (n : J → ℕ) : Fin 9 ⊕ J → ℝ :=
  Sum.elim ![1, 1 + k * d, 2 + k * d, 2 + k * d, 2 + k * d, 1 + p * d, 1 + p * d, 1 + q * d,
    1 + q * d] (fun j => (n j : ℝ) * d)

/-- **eq:near-group-length** (line 3409), from `Dim Z(𝓕) = (Dim 𝓕)²`:
`∑ n_j² = 6 + 3k² + 4pq`. -/
theorem nearGroup_length_of_center (k p q : ℕ) (hpq : p + q = k) (d : ℝ)
    (hd : d ^ 2 = 3 + 3 * k * d) (n : J → ℕ)
    (hZ : CenterDimensionFormula (nearGroupCenterDim k p q d n)
      (∑ x, nearGroupFusionDim d x ^ 2)) :
    ∑ j, (n j : ℝ) ^ 2 = 6 + 3 * k ^ 2 + 4 * p * q := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    norm_num at hd
  unfold CenterDimensionFormula at hZ
  rw [nearGroup_DimF k d hd] at hZ
  rw [Fintype.sum_sum_type] at hZ
  simp only [nearGroupCenterDim, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ] at hZ
  have hJ : ∑ j, ((n j : ℝ) * d) ^ 2 = d ^ 2 * ∑ j, (n j : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hJ] at hZ
  have hpq' : (p : ℝ) + q = k := by exact_mod_cast hpq
  exact Fusion.nearGroup_length k p q d (2 + k * d) _ hd rfl hpq' hd0
    (by linear_combination -hZ)

#print axioms rank6_length_of_center
#print axioms nearGroup_length_of_center

end HaagerupIzumi.C8.CenterDimension
