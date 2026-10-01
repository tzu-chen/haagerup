module

public import HaagerupIzumi.C8.Theta.M3First
public import HaagerupIzumi.C8.Theta.M3Reverse
public import HaagerupIzumi.C8.Theta.M6First
public import HaagerupIzumi.C8.Theta.M6Reverse

@[expose] public section

/-!
# Harmonicity of the quadratics `H` of the four theta tables

The proof of Proposition `prop:near-group-current-obstructions` (lines 3653, 3697,
3722, 3759 of `c8_expanded_20260929/haagerup_c8_expanded.tex`) uses that the
quadratics `H₁, H₂` and the three `H` are harmonic.  Each is written as
`xᵀ M x` and `∑ᵢⱼ (G⁻¹)ᵢⱼ Mᵢⱼ = 0` is checked (this is `Δ_G H / 2`).  Fully
proved; that harmonicity makes `Θ_H` modular is external and not used here.
-/

namespace HaagerupIzumi.C8
namespace Theta

/-! ## Harmonicity of the quadratics `H`

For `H(x) = ∑ᵢⱼ xᵢ Mᵢⱼ xⱼ` with `M` symmetric, the Laplacian of the metric `G`
in lattice coordinates is `Δ_G H = ∑ᵢⱼ (G⁻¹)ᵢⱼ ∂ᵢ∂ⱼ H = 2 ∑ᵢⱼ (G⁻¹)ᵢⱼ Mᵢⱼ`
(pass to orthonormal coordinates `y = P x`, `PᵀP = G`).  We exhibit `M` for each
`H` and check that this trace vanishes; the inverse Gram matrices are verified
by `G G⁻¹ = 1`.  (That harmonicity makes `Θ_H` modular is external.) -/

/-- The quadratic form `∑ᵢⱼ xᵢ Mᵢⱼ xⱼ`. -/
def quadOf (M : Matrix (Fin 4) (Fin 4) ℚ) (x : Fin 4 → ℚ) : ℚ := ∑ i, ∑ j, x i * M i j * x j

/-- `∑ᵢⱼ Kᵢⱼ Mᵢⱼ`.  For symmetric `K = G⁻¹` (any `M`),
`Δ_G (quadOf M) = ∑ᵢⱼ (G⁻¹)ᵢⱼ (Mᵢⱼ + Mⱼᵢ) = 2 ∑ᵢⱼ (G⁻¹)ᵢⱼ Mᵢⱼ`. -/
def pairTrace (K M : Matrix (Fin 4) (Fin 4) ℚ) : ℚ := ∑ i, ∑ j, K i j * M i j

def MH1 : Matrix (Fin 4) (Fin 4) ℚ := !![1, 1/2, 0, 0; 1/2, -3/2, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]
def MH2 : Matrix (Fin 4) (Fin 4) ℚ := !![1, 1/2, 0, 0; 1/2, 2, 0, 0; 0, 0, -1, 1/2; 0, 0, 1/2, -1]
def MHG7m : Matrix (Fin 4) (Fin 4) ℚ :=
  !![2, -1, 0, 0; -1, 2, -1, 0; 0, -1, 2, -1; 0, 0, -1, -15]
def MHA1A1A2 : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 1/2; 0, 0, 1/2, -1]
def MHG6m : Matrix (Fin 4) (Fin 4) ℚ :=
  !![2, -1, -1, -1; -1, 2, 0, 0; -1, 0, 2, 0; -1, 0, 0, -8]

/-- The inverse Gram matrix of `A₁ ⊕ A₁ ⊕ A₂`. -/
def invA1A1A2 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![1/2, 0, 0, 0; 0, 1/2, 0, 0; 0, 0, 2/3, 1/3; 0, 0, 1/3, 2/3]

theorem H1_eq_quad (x : Fin 4 → ℚ) : H1 x = quadOf MH1 x := by
  simp only [H1, aL7, bL7, quadOf, Fin.sum_univ_four]
  first
  | (simp [MH1] <;> ring1)
  | (norm_num [MH1] <;> ring1)

theorem H2_eq_quad (x : Fin 4 → ℚ) : H2 x = quadOf MH2 x := by
  simp only [H2, aL7, bL7, cA2, quadOf, Fin.sum_univ_four]
  first
  | (simp [MH2] <;> ring1)
  | (norm_num [MH2] <;> ring1)

theorem gramBil_zG7m (x : Fin 4 → ℚ) : gramBil gramG7m x zG7m = 21 * x 3 := by
  simp only [gramBil, Fin.sum_univ_four]
  first
  | (simp [gramG7m, zG7m] <;> ring1)
  | (norm_num [gramG7m, zG7m] <;> ring1)

/-- `x_{A₃^⊥} = (x₃/4) z`. -/
theorem projLine_G7m (x : Fin 4 → ℚ) : projLine gramG7m zG7m x = fun i => x 3 / 4 * zG7m i := by
  funext i
  have h84 : gramNorm gramG7m zG7m = 84 := by decide +kernel
  simp only [projLine, gramBil_zG7m, h84]
  ring

/-- `H = (x, x) - 21 x₃²` for `G₇⁻`. -/
theorem HG7m_eq (x : Fin 4 → ℚ) : HG7m x = gramNorm gramG7m x - 21 * x 3 ^ 2 := by
  simp only [HG7m, harmA3, projLine_G7m, gramNorm_G7m]
  first
  | (simp [zG7m] <;> ring1)
  | (norm_num [zG7m] <;> ring1)

theorem HG7m_eq_quad (x : Fin 4 → ℚ) : HG7m x = quadOf MHG7m x := by
  rw [HG7m_eq, gramNorm_G7m]
  simp only [quadOf, Fin.sum_univ_four]
  first
  | (simp [MHG7m] <;> ring1)
  | (norm_num [MHG7m] <;> ring1)

theorem HA1A1A2_eq_quad (x : Fin 4 → ℚ) : HA1A1A2 x = quadOf MHA1A1A2 x := by
  simp only [HA1A1A2, quadOf, Fin.sum_univ_four]
  first
  | (simp [MHA1A1A2] <;> ring1)
  | (norm_num [MHA1A1A2] <;> ring1)

theorem gramBil_wG6m (x : Fin 4 → ℚ) : gramBil gramG6m x wG6m = 3 * x 3 := by
  simp only [gramBil, Fin.sum_univ_four]
  first
  | (simp [gramG6m, wG6m] <;> ring1)
  | (norm_num [gramG6m, wG6m] <;> ring1)

/-- `x_{A₃^⊥} = x₃ w`. -/
theorem projLine_G6m (x : Fin 4 → ℚ) : projLine gramG6m wG6m x = fun i => x 3 * wG6m i := by
  funext i
  have h3 : gramNorm gramG6m wG6m = 3 := by decide +kernel
  simp only [projLine, gramBil_wG6m, h3]
  ring

/-- `H = (x, x) - 12 x₃²` for `G₆⁻`. -/
theorem HG6m_eq (x : Fin 4 → ℚ) : HG6m x = gramNorm gramG6m x - 12 * x 3 ^ 2 := by
  simp only [HG6m, harmA3, projLine_G6m, gramNorm_G6m]
  first
  | (simp [wG6m] <;> ring1)
  | (norm_num [wG6m] <;> ring1)

theorem HG6m_eq_quad (x : Fin 4 → ℚ) : HG6m x = quadOf MHG6m x := by
  rw [HG6m_eq, gramNorm_G6m]
  simp only [quadOf, Fin.sum_univ_four]
  first
  | (simp [MHG6m] <;> ring1)
  | (norm_num [MHG6m] <;> ring1)

/-- **Harmonicity** of `H₁, H₂` (line 3653), of `H` for `G₇⁻` (line 3697), for
`A₁ ⊕ A₁ ⊕ A₂` (line 3722) and for `G₆⁻` (line 3759): `G G⁻¹ = 1` and
`∑ᵢⱼ (G⁻¹)ᵢⱼ Mᵢⱼ = 0` for the matrices `M` of the quadratics
(`H1_eq_quad`, …). -/
theorem harmonic_quadratics :
    (∀ i j : Fin 4, ∑ k : Fin 4, (gramA1A1A2 i k : ℚ) * invA1A1A2 k j =
      if i = j then 1 else 0) ∧
    pairTrace invL7A2 MH1 = 0 ∧ pairTrace invL7A2 MH2 = 0 ∧
    pairTrace invG7m MHG7m = 0 ∧ pairTrace invA1A1A2 MHA1A1A2 = 0 ∧
    pairTrace invG6m MHG6m = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end Theta
end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.Theta.harmonic_quadratics
#print axioms HaagerupIzumi.C8.Theta.HG7m_eq_quad
#print axioms HaagerupIzumi.C8.Theta.HG6m_eq_quad
#print axioms HaagerupIzumi.C8.Theta.H2_eq_quad
