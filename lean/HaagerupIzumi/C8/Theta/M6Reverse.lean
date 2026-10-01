module

public import HaagerupIzumi.C8.Theta.Basic

@[expose] public section

/-!
# Table 4: `m = 6`, reverse orientation, the lattice `G₆⁻`

Kernel-checked coefficient table of lines 3742–3766 of
`c8_expanded_20260929/haagerup_c8_expanded.tex` and the arithmetic of lines
3767–3777, giving `dim U₁ = 5 + 12P`; and the final remark that none of the
four formulas allows `dim U₁ = 6`.

Conventions fixed here: basis `a, b, c, e` as printed; vacuum coordinate = the
coset `L`, polar coordinate = `-w/3 + L` (`polarG6m`); the projection is the
*average* over `x ↦ -x` (`avgNeg`), the interchange `b ↔ c` fixing both
representatives; `F = -6 D₂ Θ` as in Table 2.

External hypotheses (only in `m6_reverse_obstruction`): `hcancel` (pole
cancellation, `η⁸ v = φ F + κ Θ_H`) and the character values `1`,
`2 dim U₁ - 94`, `-P`.
-/

namespace HaagerupIzumi.C8
namespace Theta

/-! ## `m = 6`, reverse orientation: the lattice `G₆⁻` (lines 3742–3769) -/

/-- `w = e + a + (b + c)/2` in the basis `a, b, c, e`. -/
def wG6m : Fin 4 → ℚ := ![1, 1/2, 1/2, 1]

/-- The polar representative `-w/3`. -/
def polarG6m : Fin 4 → ℚ := ![-1/3, -1/6, -1/6, -1/3]

/-- Discriminant generators `(b+e)/2`, `(c+e)/2`, `2w/3`. -/
def d1G6m : Fin 4 → ℚ := ![0, 1/2, 0, 1/2]
def d2G6m : Fin 4 → ℚ := ![0, 0, 1/2, 1/2]
def d3G6m : Fin 4 → ℚ := ![2/3, 1/3, 1/3, 2/3]

/-- `H = ‖x_{A₃}‖² - 3 ‖x_{A₃^⊥}‖²` for `G₆⁻` (`A₃^⊥ = ℚ w`). -/
def HG6m (x : Fin 4 → ℚ) : ℚ := harmA3 gramG6m wG6m x

/-- Discriminant data for `G₆⁻` (lines 3753–3758): `w` is `e + a + (b+c)/2`,
orthogonal to `a, b, c` (pairings `(0,0,0,3)`), of norm `3`; the generators lie
in `L*` (pairings `(-1,1,0,2)`, `(-1,0,1,2)`, `(0,0,0,2)`), have quadratic values
`3/4, 3/4, 2/3` and mutual pairings `1`; `2·d₁, 2·d₂, 3·d₃ ∈ L`; the polar
representative is `-w/3 ≡ d₁ + d₂ + d₃` (difference `(-1,-1,-1,-2)`), of energy
`1/6`; and the interchange `b ↔ c` fixes `-w/3`. -/
theorem m6Reverse_discriminant :
    wG6m = (fun i => basisVec 3 i + basisVec 0 i + (basisVec 1 i + basisVec 2 i) / 2) ∧
    (fun i => gramBil gramG6m wG6m (basisVec i)) = ![0, 0, 0, 3] ∧
    gramNorm gramG6m wG6m = 3 ∧
    (fun i => gramBil gramG6m d1G6m (basisVec i)) = ![-1, 1, 0, 2] ∧
    (fun i => gramBil gramG6m d2G6m (basisVec i)) = ![-1, 0, 1, 2] ∧
    (fun i => gramBil gramG6m d3G6m (basisVec i)) = ![0, 0, 0, 2] ∧
    energy gramG6m d1G6m = 3 / 4 ∧ energy gramG6m d2G6m = 3 / 4 ∧
    energy gramG6m d3G6m = 2 / 3 ∧
    gramBil gramG6m d1G6m d2G6m = 1 ∧ gramBil gramG6m d1G6m d3G6m = 1 ∧
    gramBil gramG6m d2G6m d3G6m = 1 ∧
    (fun i => 2 * d1G6m i) = ![0, 1, 0, 1] ∧ (fun i => 2 * d2G6m i) = ![0, 0, 1, 1] ∧
    (fun i => 3 * d3G6m i) = ![2, 1, 1, 2] ∧
    d3G6m = (fun i => 2 / 3 * wG6m i) ∧
    polarG6m = (fun i => -(1 / 3) * wG6m i) ∧
    (fun i => polarG6m i - (d1G6m i + d2G6m i + d3G6m i)) = ![-1, -1, -1, -2] ∧
    energy gramG6m polarG6m = 1 / 6 ∧
    (∀ i : Fin 4, polarG6m (Equiv.swap (1 : Fin 4) 2 i) = polarG6m i) := by
  decide +kernel

/-- The inverse Gram matrix of `G₆⁻`. -/
def invG6m : Matrix (Fin 4) (Fin 4) ℚ :=
  !![4/3, 2/3, 2/3, 1/3; 2/3, 5/6, 1/3, 1/6; 2/3, 1/3, 5/6, 1/6; 1/3, 1/6, 1/6, 1/3]

/-- `L* = G⁻¹ ℤ⁴ = ⟨d₁, d₂, d₃⟩ + L`: the columns of `G⁻¹` are `2d₃`, `d₁ + d₃`,
`d₂ + d₃`, `-(-w/3)` modulo `ℤ⁴`.  With `2d₁, 2d₂, 3d₃ ∈ L` and
`d₁, d₂, d₁ + d₂ ∉ L` this gives `L*/L ≅ (ℤ/2)² × ℤ/3`. -/
theorem m6Reverse_dual_generated :
    (∀ i j : Fin 4, ∑ k : Fin 4, (gramG6m i k : ℚ) * invG6m k j = if i = j then 1 else 0) ∧
    (fun i => invG6m i 0 - 2 * d3G6m i) = ![0, 0, 0, -1] ∧
    (fun i => invG6m i 1 - (d1G6m i + d3G6m i)) = ![0, 0, 0, -1] ∧
    (fun i => invG6m i 2 - (d2G6m i + d3G6m i)) = ![0, 0, 0, -1] ∧
    (fun i => invG6m i 3 + polarG6m i) = ![0, 0, 0, 0] := by
  decide +kernel

/-- Which coset is which: every vector of `-w/3 + L` has energy `1/6` modulo `1`;
in particular `1/6` is the minimal energy of the coset. -/
theorem energy_cosetPt_polarG6m (n : Fin 4 → ℤ) :
    energy gramG6m (cosetPt polarG6m n) =
      1 / 6 + ((-n 3 + n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 + 2 * n 3 ^ 2 - n 0 * n 1 - n 0 * n 2
        - n 0 * n 3 : ℤ) : ℚ) := by
  rw [energy, gramNorm_G6m]
  first
  | (simp [cosetPt, polarG6m] <;> ring1)
  | (norm_num [cosetPt, polarG6m] <;> ring1)

def shG6m_zero : List (Fin 4 → ℤ) := [![0, 0, 0, 0]]

/-- The twelve roots of `G₆⁻` (those of `A₃ = ⟨a, b, c⟩`). -/
def shG6m_roots : List (Fin 4 → ℤ) :=
  [![1, 0, 0, 0], ![-1, 0, 0, 0], ![0, 1, 0, 0], ![0, -1, 0, 0], ![0, 0, 1, 0],
    ![0, 0, -1, 0], ![1, 1, 0, 0], ![-1, -1, 0, 0], ![1, 0, 1, 0], ![-1, 0, -1, 0],
    ![1, 1, 1, 0], ![-1, -1, -1, 0]]

theorem shell_G6m_vac0 : shell gramG6m 0 0 = {n | n ∈ shG6m_zero} :=
  shell_eq_of_box coord_G6m ![0, 0, 0, 0] ![0, 0, 0, 0] (by decide +kernel) shG6m_zero
    (by decide +kernel) (by decide +kernel)

theorem shell_G6m_vac1 : shell gramG6m 0 1 = {n | n ∈ shG6m_roots} :=
  shell_eq_of_box coord_G6m ![-1, -1, -1, 0] ![1, 1, 1, 0] (by decide +kernel) shG6m_roots
    (by decide +kernel) (by decide +kernel)

/-- The shortest vector `-w/3` of the polar coset is unique. -/
theorem shell_G6m_polar : shell gramG6m polarG6m (1 / 6) = {n | n ∈ shG6m_zero} :=
  shell_eq_of_box coord_G6m ![0, 0, 0, 0] ![1, 0, 0, 0] (by decide +kernel) shG6m_zero
    (by decide +kernel) (by decide +kernel)

theorem shell_G6m_polarNeg : shell gramG6m (-polarG6m) (1 / 6) = {n | n ∈ shG6m_zero} :=
  shell_eq_of_box coord_G6m ![-1, 0, 0, 0] ![0, 0, 0, 0] (by decide +kernel) shG6m_zero
    (by decide +kernel) (by decide +kernel)

/-- Provenance: twelve roots, all in `A₃` (last coordinate zero). -/
theorem m6Reverse_roots_in_A3 :
    shG6m_roots.length = 12 ∧ ∀ n ∈ shG6m_roots, n 3 = 0 := by
  decide +kernel

theorem count_G6m_vac0 : thetaCount gramG6m 0 0 = 1 := by
  unfold thetaCount
  rw [thetaCoeff_eq_list_sum shell_G6m_vac0 (by decide +kernel)]
  decide +kernel

theorem count_G6m_vac1 : thetaCount gramG6m 0 1 = 12 := by
  unfold thetaCount
  rw [thetaCoeff_eq_list_sum shell_G6m_vac1 (by decide +kernel)]
  decide +kernel

theorem count_G6m_polar : thetaCount gramG6m polarG6m (1 / 6) = 1 := by
  unfold thetaCount
  rw [thetaCoeff_eq_list_sum shell_G6m_polar (by decide +kernel)]
  decide +kernel

theorem count_G6m_polarNeg : thetaCount gramG6m (-polarG6m) (1 / 6) = 1 := by
  unfold thetaCount
  rw [thetaCoeff_eq_list_sum shell_G6m_polarNeg (by decide +kernel)]
  decide +kernel

theorem H_G6m_vac0 : thetaCoeff gramG6m 0 HG6m 0 = 0 := by
  rw [thetaCoeff_eq_list_sum shell_G6m_vac0 (by decide +kernel)]
  decide +kernel

theorem H_G6m_vac1 : thetaCoeff gramG6m 0 HG6m 1 = 24 := by
  rw [thetaCoeff_eq_list_sum shell_G6m_vac1 (by decide +kernel)]
  decide +kernel

theorem H_G6m_polar : thetaCoeff gramG6m polarG6m HG6m (1 / 6) = -1 := by
  rw [thetaCoeff_eq_list_sum shell_G6m_polar (by decide +kernel)]
  decide +kernel

theorem H_G6m_polarNeg : thetaCoeff gramG6m (-polarG6m) HG6m (1 / 6) = -1 := by
  rw [thetaCoeff_eq_list_sum shell_G6m_polarNeg (by decide +kernel)]
  decide +kernel

/-- Projected `[q^e] Θ_H` at the coset `g + L`. -/
noncomputable def PThetaG6m (g : Fin 4 → ℚ) (e : ℚ) : ℚ :=
  avgNeg (fun g => thetaCoeff gramG6m g HG6m e) g

/-- Projected `[q^e] F`, `F = -6 D₂ Θ`, at the coset `g + L`. -/
noncomputable def PFG6m (g : Fin 4 → ℚ) (e : ℚ) : ℚ :=
  avgNeg (fun g => minusSixD2Coeff (thetaCount gramG6m g) e) g

theorem m6Reverse_F_vac0 : PFG6m 0 0 = 1 := by
  simp only [PFG6m, avgNeg, neg_zero]
  rw [minusSixD2Coeff_of_lt_one _ (by norm_num : (0 : ℚ) < 1), count_G6m_vac0]
  norm_num

theorem m6Reverse_H_vac0 : PThetaG6m 0 0 = 0 := by
  simp only [PThetaG6m, avgNeg, neg_zero]
  rw [H_G6m_vac0]
  norm_num

theorem m6Reverse_F_vac1 : PFG6m 0 1 = -84 := by
  simp only [PFG6m, avgNeg, neg_zero]
  rw [minusSixD2Coeff_one, count_G6m_vac1, count_G6m_vac0]
  norm_num

theorem m6Reverse_H_vac1 : PThetaG6m 0 1 = 24 := by
  simp only [PThetaG6m, avgNeg, neg_zero]
  rw [H_G6m_vac1]
  norm_num

theorem m6Reverse_F_polar : PFG6m polarG6m (1 / 6) = 0 := by
  have h : (1 / 6 : ℚ) < 1 := by norm_num
  simp only [PFG6m, avgNeg]
  rw [minusSixD2Coeff_of_lt_one _ h, minusSixD2Coeff_of_lt_one _ h, count_G6m_polar,
    count_G6m_polarNeg]
  norm_num

theorem m6Reverse_H_polar : PThetaG6m polarG6m (1 / 6) = -1 := by
  simp only [PThetaG6m, avgNeg]
  rw [H_G6m_polar, H_G6m_polarNeg]
  norm_num

/-- **Table 4** (lines 3760–3766), all six entries, after projection. -/
theorem m6Reverse_table :
    PFG6m 0 0 = 1 ∧ PThetaG6m 0 0 = 0 ∧ PFG6m 0 1 = -84 ∧ PThetaG6m 0 1 = 24 ∧
    PFG6m polarG6m (1 / 6) = 0 ∧ PThetaG6m polarG6m (1 / 6) = -1 :=
  ⟨m6Reverse_F_vac0, m6Reverse_H_vac0, m6Reverse_F_vac1, m6Reverse_H_vac1,
    m6Reverse_F_polar, m6Reverse_H_polar⟩

/-- **`m = 6`, reverse orientation** (lines 3767–3777).  `c g e` is the
coefficient of `q^e` in the projected coordinate of the coset `g + L` of `η⁸ v`.

External hypotheses: `hcancel` (pole cancellation: `η⁸ v = φ F + κ Θ_H`);
`hvac0`, `hvac1` as for `m = 3`; `hpolar`: the polar coefficient is `-P`.
Conclusion: `φ = 1`, `κ = P`, `dim U₁ = 5 + 12P`. -/
theorem m6_reverse_obstruction (c : (Fin 4 → ℚ) → ℚ → ℚ) (P d : ℕ) (φ κ : ℚ)
    (hcancel : ∀ g e, c g e = φ * PFG6m g e + κ * PThetaG6m g e)
    (hvac0 : c 0 0 = 1) (hvac1 : c 0 1 = 2 * (d : ℚ) - 94)
    (hpolar : c polarG6m (1 / 6) = -(P : ℚ)) :
    φ = 1 ∧ κ = P ∧ d = 5 + 12 * P := by
  rw [hcancel, m6Reverse_F_vac0, m6Reverse_H_vac0] at hvac0
  rw [hcancel, m6Reverse_F_vac1, m6Reverse_H_vac1] at hvac1
  rw [hcancel, m6Reverse_F_polar, m6Reverse_H_polar] at hpolar
  have hφ : φ = 1 := by linarith
  have hκ : κ = P := by linarith
  refine ⟨hφ, hκ, ?_⟩
  have hd : (d : ℚ) = 5 + 12 * P := by linarith
  exact_mod_cast hd

/-- "In particular none allows `dim U₁ = 6`" (line 3627). -/
theorem near_group_formulas_ne_six (A B P : ℕ) :
    15 + A + 10 * B ≠ 6 ∧ 14 + 42 * A ≠ 6 ∧ 8 + A ≠ 6 ∧ 5 + 12 * P ≠ 6 := by
  omega

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.m6Reverse_table
#print axioms HaagerupIzumi.C8.Theta.m6_reverse_obstruction
#print axioms HaagerupIzumi.C8.Theta.m6Reverse_discriminant
#print axioms HaagerupIzumi.C8.Theta.m6Reverse_dual_generated
#print axioms HaagerupIzumi.C8.Theta.energy_cosetPt_polarG6m
#print axioms HaagerupIzumi.C8.Theta.m6Reverse_roots_in_A3
#print axioms HaagerupIzumi.C8.Theta.near_group_formulas_ne_six
