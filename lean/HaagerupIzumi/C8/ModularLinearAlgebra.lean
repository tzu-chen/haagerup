module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Linear algebra in the multiplicity-three and multiplicity-six exclusions

Two linear-algebra steps of Appendix G:

* Lemma `lem:m6-projection` (lines 3584–3594): from the vacuum/`X` row difference
  `S v₀ = -v₀/2 - v_A - v_B/2`, the relations `S² = 1` and `STS = i T⁻¹ S T⁻¹` applied to
  `v₀`, and the twists `T = diag(1, -i, -1)` on `(v₀, v_A, v_B)`, the manuscript deduces
  `S v_A = -v₀/2 + v_B/2` and `S v_B = -v₀/2 + v_A - v_B/2` (eq:m6-projection).
  `m6_projection` proves exactly this deduction in any complex vector space.
* Proposition `prop:m3-modular` (lines 3503–3509): for the remaining real block `K`,
  `∑_j K_ij = d` and `∑_j K_ij z_j = d + i√3 s z_i⁻¹` "determine each real row: three
  distinct points on a circle are not collinear".  `row_unique` proves that a real row
  `(K₁, K₂, K₃)` is determined by `∑ K_j` and `∑ K_j z_j` when the `z_j` are three distinct
  unit complex numbers.

The modular relations themselves (`S² = 1` on these self-dual combinations, `STS = iT⁻¹ST⁻¹`
for the projected representation, the Verlinde/Galois facts) are external inputs.
-/

namespace HaagerupIzumi.C8.ModularLinearAlgebra

open Complex

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- **Lemma `lem:m6-projection`, the matrix derivation.**  In any complex vector space, if
`T v₀ = v₀`, `T v_A = -i v_A`, `T v_B = -v_B` (and `T⁻¹` acts by the inverse eigenvalues),
`S v₀ = -v₀/2 - v_A - v_B/2`, `S² v₀ = v₀` and `S T S v₀ = i T⁻¹ S T⁻¹ v₀`, then
`S v_A = -v₀/2 + v_B/2` and `S v_B = -v₀/2 + v_A - v_B/2`. -/
theorem m6_projection (S T Tinv : M →ₗ[ℂ] M) (v₀ vA vB : M)
    (hT0 : T v₀ = v₀) (hTA : T vA = (-I) • vA) (hTB : T vB = (-1 : ℂ) • vB)
    (hTi0 : Tinv v₀ = v₀) (hTiA : Tinv vA = I • vA) (hTiB : Tinv vB = (-1 : ℂ) • vB)
    (hS0 : S v₀ = (-1 / 2 : ℂ) • v₀ - vA - (1 / 2 : ℂ) • vB)
    (hSS : S (S v₀) = v₀)
    (hSTS : S (T (S v₀)) = I • Tinv (S (Tinv v₀))) :
    S vA = (-1 / 2 : ℂ) • v₀ + (1 / 2 : ℂ) • vB ∧
      S vB = (-1 / 2 : ℂ) • v₀ + vA - (1 / 2 : ℂ) • vB := by
  have hII : I * I = -1 := Complex.I_mul_I
  -- `S² v₀ = v₀`
  have eA : (-1 / 2 : ℂ) • S v₀ - S vA - (1 / 2 : ℂ) • S vB = v₀ := by
    calc (-1 / 2 : ℂ) • S v₀ - S vA - (1 / 2 : ℂ) • S vB
        = S ((-1 / 2 : ℂ) • v₀ - vA - (1 / 2 : ℂ) • vB) := by
          rw [map_sub, map_sub, map_smul, map_smul]
      _ = S (S v₀) := by rw [hS0]
      _ = v₀ := hSS
  -- `S T S v₀`
  have hTs : T (S v₀) = (-1 / 2 : ℂ) • v₀ + I • vA + (1 / 2 : ℂ) • vB := by
    rw [hS0, map_sub, map_sub, map_smul, map_smul, hT0, hTA, hTB]
    module
  have hL : S (T (S v₀)) = (-1 / 2 : ℂ) • S v₀ + I • S vA + (1 / 2 : ℂ) • S vB := by
    rw [hTs, map_add, map_add, map_smul, map_smul, map_smul]
  -- `i T⁻¹ S T⁻¹ v₀`
  have hR : I • Tinv (S (Tinv v₀)) = (-1 / 2 * I : ℂ) • v₀ + vA + (1 / 2 * I : ℂ) • vB := by
    rw [hTi0, hS0, map_sub, map_sub, map_smul, map_smul, hTi0, hTiA, hTiB]
    rw [smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, hII]
    module
  have eB : (-1 / 2 : ℂ) • S v₀ + I • S vA + (1 / 2 : ℂ) • S vB =
      (-1 / 2 * I : ℂ) • v₀ + vA + (1 / 2 * I : ℂ) • vB := by
    rw [← hL, hSTS, hR]
  rw [hS0] at eA eB
  have hne : (I - 1 : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  -- `(i - 1) x = (i - 1)(-v₀/2 + v_B/2)`
  have kx : (I - 1 : ℂ) • S vA = (I - 1 : ℂ) • ((-1 / 2 : ℂ) • v₀ + (1 / 2 : ℂ) • vB) := by
    linear_combination (norm := module) eB + eA
  have hx : S vA = (-1 / 2 : ℂ) • v₀ + (1 / 2 : ℂ) • vB := by
    have := congrArg (fun z : M => (I - 1 : ℂ)⁻¹ • z) kx
    simpa [smul_add, smul_smul, inv_mul_cancel_left₀ hne, inv_mul_cancel₀ hne] using this
  refine ⟨hx, ?_⟩
  rw [hx] at eA
  linear_combination (norm := module) (-2 : ℂ) • eA

/-- Three distinct points of the unit circle are not collinear: if `z₁ - z₃` is a real
multiple of `z₂ - z₃` then `z₁ ∈ {z₂, z₃}`. -/
theorem not_collinear (z₁ z₂ z₃ : ℂ) (h₁ : normSq z₁ = 1) (h₂ : normSq z₂ = 1)
    (h₃ : normSq z₃ = 1) (s : ℝ) (hs : z₁ - z₃ = (s : ℂ) * (z₂ - z₃)) : z₁ = z₂ ∨ z₁ = z₃ := by
  set w := z₂ - z₃
  have hz₁ : z₁ = z₃ + (s : ℂ) * w := by rw [← hs]; ring
  have hz₂ : z₂ = z₃ + w := by simp [w]
  -- `|z₃ + t w|² = |z₃|² + 2 t Re(conj z₃ w) + t² |w|²`
  have expand : ∀ t : ℝ, normSq (z₃ + (t : ℂ) * w) =
      normSq z₃ + 2 * t * (z₃.re * w.re + z₃.im * w.im) + t ^ 2 * normSq w := by
    intro t
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im]
    ring
  have e1 := expand s
  have e2 := expand 1
  rw [← hz₁, h₁, h₃] at e1
  rw [Complex.ofReal_one, one_mul, ← hz₂, h₂, h₃] at e2
  have key : s * (s - 1) * normSq w = 0 := by linear_combination s * e2 - e1
  rcases mul_eq_zero.1 key with h | h
  · rcases mul_eq_zero.1 h with h | h
    · right; rw [hz₁, h]; simp
    · left; have : s = 1 := by linarith
      rw [hz₁, this, hz₂]; simp
  · left
    have : w = 0 := normSq_eq_zero.1 h
    rw [hz₁, hz₂, this]; simp

/-- **Proposition `prop:m3-modular`, row determination.**  For three distinct unit complex
numbers `z_j`, a real row `K` is determined by `∑ K_j` and `∑ K_j z_j`. -/
theorem row_unique (z : Fin 3 → ℂ) (hz : ∀ j, normSq (z j) = 1) (hinj : Function.Injective z)
    (K K' : Fin 3 → ℝ) (hsum : ∑ j, K j = ∑ j, K' j)
    (hzsum : ∑ j, (K j : ℂ) * z j = ∑ j, (K' j : ℂ) * z j) : K = K' := by
  set D : Fin 3 → ℝ := fun j => K j - K' j
  have hD : D 0 + D 1 + D 2 = 0 := by
    simp only [D, Fin.sum_univ_three] at hsum ⊢; linarith
  have hDz : (D 0 : ℂ) * z 0 + (D 1 : ℂ) * z 1 + (D 2 : ℂ) * z 2 = 0 := by
    simp only [D, Fin.sum_univ_three] at hzsum ⊢
    push_cast
    linear_combination hzsum
  have h2 : (D 2 : ℂ) = -(D 0 : ℂ) - (D 1 : ℂ) := by
    have : (D 2 : ℝ) = -D 0 - D 1 := by linarith
    rw [this]; push_cast; ring
  rw [h2] at hDz
  have hlin : (D 0 : ℂ) * (z 0 - z 2) + (D 1 : ℂ) * (z 1 - z 2) = 0 := by
    linear_combination hDz
  have h01 : z 0 ≠ z 1 := fun h => by have := hinj h; exact absurd this (by decide)
  have h02 : z 0 ≠ z 2 := fun h => by have := hinj h; exact absurd this (by decide)
  have h12 : z 1 ≠ z 2 := fun h => by have := hinj h; exact absurd this (by decide)
  have hD0 : D 0 = 0 := by
    by_contra hne
    have hne' : (D 0 : ℂ) ≠ 0 := by exact_mod_cast hne
    have hs : z 0 - z 2 = ((-(D 1 / D 0) : ℝ) : ℂ) * (z 1 - z 2) := by
      push_cast
      field_simp
      linear_combination hlin
    rcases not_collinear (z 0) (z 1) (z 2) (hz 0) (hz 1) (hz 2) _ hs with h | h
    · exact h01 h
    · exact h02 h
  have hD1 : D 1 = 0 := by
    rw [hD0] at hlin
    simp only [Complex.ofReal_zero, zero_mul, zero_add] at hlin
    rcases mul_eq_zero.1 hlin with h | h
    · exact_mod_cast h
    · exact absurd (sub_eq_zero.1 h) h12
  have hD2 : D 2 = 0 := by linarith
  funext j
  fin_cases j
  · simpa [D, sub_eq_zero] using hD0
  · simpa [D, sub_eq_zero] using hD1
  · simpa [D, sub_eq_zero] using hD2

#print axioms m6_projection
#print axioms row_unique

end HaagerupIzumi.C8.ModularLinearAlgebra
