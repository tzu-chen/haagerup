module

public import HaagerupIzumi.C8.Theta.ObstructionsOfVoa
public import Mathlib.Geometry.Manifold.Notation

@[expose] public section

/-!
# The VOA-side data of the near-group current obstructions

Proposition `prop:near-group-current-obstructions` (lines 3614–3770 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) excludes the near-group cases `m = 3, 6` of rank
four.  The obstruction theorems `Theta.m3_first_obstruction_of_voa`,
`Theta.m3_reverse_obstruction_of_voa`, `Theta.m6_first_obstruction_of_voa`,
`Theta.m6_reverse_obstruction_of_voa` (Theta/ObstructionsOfVoa) derive the four formulas for
`d = dim U₁` from the VOA-side data on the even block, with the pole-cancellation identity
(`hcancel`) **proved**.  This file bundles those data, one structure per table:

* a homomorphism `σ : SL(2, ℤ) → GL(E, ℂ)` with `σ(S)`, `σ(T)` the explicit Weil-type matrices
  of the table ([external] Zhu modularity of the character vector, Huang's identification of `S`,
  and the comparison with the categorical modular data) and with finite image (`hfin`,
  [certificate]/[standard]: a property of the explicit matrices alone, since the image is the
  group they generate, a Weil-type representation factoring through a finite quotient
  `SL(2, ℤ/N)`, lines 3772–3774; the `SL₂` relations of the matrices are proved in
  `Theta.WeilSanityST3`, `sl2_relations_*`, the finiteness of the generated group is not
  formalized);
* the weight-zero vector-valued function `V` (holomorphic, `σ`-covariant: [external] Zhu, Huang),
  its `η⁸`-multiplied `q`-expansion `δc` (support in `λ + ℕ`, absolute convergence), and the
  values of `δc` below `q^{1/3}` (vacuum, polar coefficients `A, B, P`, vanishing elsewhere) and at
  `q¹` (`d = dim U₁`) ([manuscript step]: the even-block reading of the characters, lines
  3700–3770).

`M3FirstVoa.dim`, `M3ReverseVoa.dim`, `M6FirstVoa.dim`, `M6ReverseVoa.dim` are the four
obstruction formulas.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Theta
open Complex Matrix ModularGroup
open UpperHalfPlane hiding I
open scoped MatrixGroups Real Manifold

/-- The VOA-side data for `m = 3`, first orientation (Table 1), with `d = dim U₁`. -/
structure M3FirstVoa (d : ℕ) where
  σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ
  hfin : (Set.range σ).Finite
  hσS : (σ S : Matrix _ _ ℂ) = SθEL7A2
  hσT : (σ T : Matrix _ _ ℂ) = TθEL7A2
  V : ℍ → Fin 4 × Fin 2 → ℂ
  hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e)
  hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ
  δc : Fin 4 × Fin 2 → ℚ → ℚ
  hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
    ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ)
  hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramL7A2 (cosetEL7A2 e)
  hsum : ∀ e (y : ℝ), 0 < y →
    Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y)
  A : ℕ
  B : ℕ
  hvac0 : δc (0, 0) 0 = 0
  hpolarB : δc (1, 0) (1 / 7) = -(B : ℚ) - 0
  hpolarA : δc (3, 0) (2 / 7) = -(A : ℚ) - (-7)
  hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 →
    (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 7) ∨ (e = (3, 0) ∧ x = 2 / 7)
  hvac : δc (0, 0) 1 = 2 * ((d : ℚ) - 22)

theorem M3FirstVoa.dim {d : ℕ} (X : M3FirstVoa d) : d = 15 + X.A + 10 * X.B :=
  m3_first_obstruction_of_voa X.σ X.hfin X.hσS X.hσT X.V X.hVhol X.hVcov X.δc X.hVq X.hsupp
    X.hsum X.A X.B d X.hvac0 X.hpolarB X.hpolarA X.hother X.hvac

/-- The VOA-side data for `m = 3`, reverse orientation (Table 2), with `d = dim U₁`. -/
structure M3ReverseVoa (d : ℕ) where
  σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 4 × Fin 2) ℂ
  hfin : (Set.range σ).Finite
  hσS : (σ S : Matrix _ _ ℂ) = SθEG7m
  hσT : (σ T : Matrix _ _ ℂ) = TθEG7m
  V : ℍ → Fin 4 × Fin 2 → ℂ
  hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e)
  hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ
  δc : Fin 4 × Fin 2 → ℚ → ℚ
  hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
    ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ)
  hsupp : ∀ e x, δc e x ≠ 0 →
    ∃ n : ℕ, x = (n : ℚ) + lamOf gramG7m (repG7m (((ιG7m e : Fin 21) : ℕ) : ℤ))
  hsum : ∀ e (y : ℝ), 0 < y →
    Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y)
  A : ℕ
  hvac0 : δc (0, 0) 0 = 1
  hpolar : δc (2, 1) (2 / 21) = -(A : ℚ)
  hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 →
    (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 2 / 21)
  hvac1 : δc (0, 0) 1 = 2 * (d : ℚ) - 94

theorem M3ReverseVoa.dim {d : ℕ} (X : M3ReverseVoa d) : d = 14 + 42 * X.A :=
  m3_reverse_obstruction_of_voa X.σ X.hfin X.hσS X.hσT X.V X.hVhol X.hVcov X.δc X.hVq X.hsupp
    X.hsum X.A d X.hvac0 X.hpolar X.hother X.hvac1

/-- The VOA-side data for `m = 6`, first orientation (Table 3), with `d = dim U₁`. -/
structure M6FirstVoa (d : ℕ) where
  σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ
  hfin : (Set.range σ).Finite
  hσS : (σ S : Matrix _ _ ℂ) = SθEA1A1A2
  hσT : (σ T : Matrix _ _ ℂ) = TθEA1A1A2
  V : ℍ → Fin 3 × Fin 2 → ℂ
  hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e)
  hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ
  δc : Fin 3 × Fin 2 → ℚ → ℚ
  hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
    ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ)
  hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramA1A1A2 (cosetEA1A1A2 e)
  hsum : ∀ e (y : ℝ), 0 < y →
    Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y)
  A : ℕ
  hvac0 : δc (0, 0) 0 = 0
  hpolar : δc (1, 0) (1 / 4) = -(A : ℚ) / 2 - (-(8 : ℚ) / 2)
  hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 → (e = (0, 0) ∧ x = 0) ∨ (e = (1, 0) ∧ x = 1 / 4)
  hvac : δc (0, 0) 1 = 2 * ((d : ℚ) - 16)

theorem M6FirstVoa.dim {d : ℕ} (X : M6FirstVoa d) : d = 8 + X.A :=
  m6_first_obstruction_of_voa X.σ X.hfin X.hσS X.hσT X.V X.hVhol X.hVcov X.δc X.hVq X.hsupp
    X.hsum X.A d X.hvac0 X.hpolar X.hother X.hvac

/-- The VOA-side data for `m = 6`, reverse orientation (Table 4), with `d = dim U₁`. -/
structure M6ReverseVoa (d : ℕ) where
  σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup (Fin 3 × Fin 2) ℂ
  hfin : (Set.range σ).Finite
  hσS : (σ S : Matrix _ _ ℂ) = SθE6G6m
  hσT : (σ T : Matrix _ _ ℂ) = TθE6G6m
  V : ℍ → Fin 3 × Fin 2 → ℂ
  hVhol : ∀ e, MDiff (fun τ : ℍ => V τ e)
  hVcov : ∀ (γ : SL(2, ℤ)) (τ : ℍ), V (γ • τ) = (σ γ : Matrix _ _ ℂ) *ᵥ V τ
  δc : Fin 3 × Fin 2 → ℚ → ℚ
  hVq : ∀ e (τ : ℍ), eta8 τ * V τ e =
    ∑' x : ℚ, ((δc e x : ℚ) : ℂ) * cexp (2 * π * I * (x : ℂ) * τ)
  hsupp : ∀ e x, δc e x ≠ 0 → ∃ n : ℕ, x = (n : ℚ) + lamOf gramG6m (cosetE6G6m e)
  hsum : ∀ e (y : ℝ), 0 < y →
    Summable fun x : ℚ => ‖((δc e x : ℚ) : ℂ)‖ * Real.exp (-2 * π * (x : ℝ) * y)
  P : ℕ
  hvac0 : δc (0, 0) 0 = 1
  hpolar : δc (2, 1) (1 / 6) = -(P : ℚ)
  hother : ∀ e x, x < 1 / 3 → δc e x ≠ 0 → (e = (0, 0) ∧ x = 0) ∨ (e = (2, 1) ∧ x = 1 / 6)
  hvac1 : δc (0, 0) 1 = 2 * (d : ℚ) - 94

theorem M6ReverseVoa.dim {d : ℕ} (X : M6ReverseVoa d) : d = 5 + 12 * X.P :=
  m6_reverse_obstruction_of_voa X.σ X.hfin X.hσS X.hσT X.V X.hVhol X.hVcov X.δc X.hVq X.hsupp
    X.hsum X.P d X.hvac0 X.hpolar X.hother X.hvac1

/-- **Case `m = 3`**: either orientation gives `d = 15 + A + 10B` or `d = 14 + 42A`. -/
theorem case3_of_voa {d : ℕ} (h : Nonempty (M3FirstVoa d) ∨ Nonempty (M3ReverseVoa d)) :
    ∃ a b : ℕ, d = 15 + a + 10 * b ∨ d = 14 + 42 * a := by
  rcases h with h | h
  · obtain ⟨X⟩ := h
    exact ⟨X.A, X.B, Or.inl X.dim⟩
  · obtain ⟨X⟩ := h
    exact ⟨X.A, 0, Or.inr X.dim⟩

/-- **Case `m = 6`**: either orientation gives `d = 8 + A` or `d = 5 + 12P`. -/
theorem case6_of_voa {d : ℕ} (h : Nonempty (M6FirstVoa d) ∨ Nonempty (M6ReverseVoa d)) :
    ∃ a p : ℕ, d = 8 + a ∨ d = 5 + 12 * p := by
  rcases h with h | h
  · obtain ⟨X⟩ := h
    exact ⟨X.A, 0, Or.inl X.dim⟩
  · obtain ⟨X⟩ := h
    exact ⟨0, X.P, Or.inr X.dim⟩

#print axioms M3FirstVoa.dim
#print axioms M3ReverseVoa.dim
#print axioms M6FirstVoa.dim
#print axioms M6ReverseVoa.dim
#print axioms case3_of_voa
#print axioms case6_of_voa

end HaagerupIzumi.C8.ProofMap
