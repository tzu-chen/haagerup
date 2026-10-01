module

public import HaagerupIzumi.C8.Analytic.PoleCancellation
public import HaagerupIzumi.C8.Characters
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Geometry.Manifold.Notation

@[expose] public section

/-!
# Lemma `lem:haagerup-character-unique` (lines 4147–4159)

"Two character vectors for this modular representation with the same `γ` coincide in every
weight.  *Proof.*  The modular representation has finite image by the congruence theorem
[DLN, Theorem I].  A constant vector must be fixed by both `S` and the character `T` matrix,
which includes `e^{-2πi/3}`.  The only `T`-fixed coordinate is the object of categorical twist
`e^{2πi/3}`.  Its `S` image has a nonzero vacuum component, so it cannot span an invariant line.
There are therefore no invariant constants, and Lemma `lem:pole-cancellation` applies."

`no_invariant_vector` proves the middle part from the twist table (`Characters`): the character
`T` matrix is `diag(exp(2πi(t_l - 1/3)))`, whose only eigenvalue `1` is at `c₁`
(`Characters.character_T_fixed_iff`), and `S_{0,c₁} ≠ 0`.  `character_vector_unique` then applies
the fully proved `pole_cancellation`.  Inputs: finite image (DLN Theorem I, external); the
diagonal form of `T` (from the twist list of `lem:six-residual-twists`, `c = 8` and
`θ = e^{2πi L(0)}`); and `S_{0,c₁} = d_{c₁}/D ≠ 0`, which needs Huang's identification of Zhu's
`S` with the categorical `S` (then `d_j ≠ 0` for every label).

The manuscript's hypothesis "the same `γ`" enters `character_vector_unique` as `hpp` (`F - G`
bounded at `i∞`).  `character_vector_unique_of_qexp` derives `hpp` from `q`-expansions
`∑ₙ aₗ(n) q^{n+λₗ}` whose coefficients agree at negative exponents (`isBoundedAtImInfty_qseries`),
and `haagerup_character_unique` is the lemma as stated: with `λₗ = tₗ - 1/3`, the negative
exponents are exactly `n = 0` at `o, b, a, c₀, d₃` (`polar_cases`), so the same vacuum
coefficient, no weight-zero vectors in the nonvacuum twist-zero modules (strict positivity)
and the same `γ` give `F = G`.
-/

namespace HaagerupIzumi.C8.CharacterUniqueness

open HaagerupIzumi.C8 HaagerupIzumi.C8.Characters Complex
open scoped MatrixGroups Manifold Matrix

/-- The character `T` eigenvalue `exp(2πi(t_l - 1/3))` (central charge `8`). -/
noncomputable def tEigen (l : Label) : ℂ :=
  Complex.exp (2 * Real.pi * I * (((twistExp l - 1 / 3 : ℚ) : ℝ) : ℂ))

theorem tEigen_eq_one_iff (l : Label) : tEigen l = 1 ↔ l = .c1 := by
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [tEigen, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hq : ((((twistExp l - 1 / 3 : ℚ) : ℝ) : ℂ)) = ((n : ℝ) : ℂ) := by
      apply mul_left_cancel₀ h2pi
      rw [hn]
      push_cast
      ring
    have hq' : ((twistExp l - 1 / 3 : ℚ) : ℝ) = (n : ℝ) := by exact_mod_cast hq
    have hq'' : (twistExp l - 1 / 3 : ℚ) = n := by exact_mod_cast hq'
    exact (character_T_fixed_iff l).1 ⟨n, hq''⟩
  · rintro rfl
    exact ⟨0, by simp [twistExp]⟩

/-- **No invariant vector.**  If the character `T` acts by `diag(tEigen)` and `S_{0,c₁} ≠ 0`,
the representation has no nonzero invariant vector. -/
theorem no_invariant_vector (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup Label ℂ)
    (hT : (σ ModularGroup.T : Matrix Label Label ℂ) = Matrix.diagonal tEigen)
    (hS : (σ ModularGroup.S : Matrix Label Label ℂ) .o .c1 ≠ 0) :
    ∀ v : Label → ℂ, (∀ γ, (σ γ : Matrix Label Label ℂ) *ᵥ v = v) → v = 0 := by
  intro v hv
  have hsupp : ∀ l, l ≠ .c1 → v l = 0 := by
    intro l hl
    have h := congrFun (hv ModularGroup.T) l
    rw [hT, Matrix.mulVec_diagonal] at h
    have hne : tEigen l ≠ 1 := fun h' => hl ((tEigen_eq_one_iff l).1 h')
    have h2 : (tEigen l - 1) * v l = 0 := by rw [sub_mul, one_mul, h, sub_self]
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd (sub_eq_zero.1 h3) hne
    · exact h3
  have hS0 : ∑ j, (σ ModularGroup.S : Matrix Label Label ℂ) .o j * v j = v .o := by
    simpa [Matrix.mulVec, dotProduct] using congrFun (hv ModularGroup.S) .o
  rw [Finset.sum_eq_single (Label.c1)] at hS0
  · have hv0 : v .o = 0 := hsupp .o (by decide)
    rw [hv0] at hS0
    have hc1 : v .c1 = 0 := by
      rcases mul_eq_zero.1 hS0 with h | h
      · exact absurd h hS
      · exact h
    funext l
    by_cases hl : l = .c1
    · rw [hl, hc1]; rfl
    · rw [hsupp l hl]; rfl
  · intro l _ hl
    rw [hsupp l hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Lemma `lem:haagerup-character-unique`.**  Two weight-zero vector-valued modular functions
for the Haagerup character representation (finite image, character `T = diag(tEigen)`,
`S_{0,c₁} ≠ 0`), holomorphic on the upper half-plane, with equal principal parts at infinity,
coincide. -/
theorem character_vector_unique (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup Label ℂ)
    (hfin : (Set.range σ).Finite)
    (hT : (σ ModularGroup.T : Matrix Label Label ℂ) = Matrix.diagonal tEigen)
    (hS : (σ ModularGroup.S : Matrix Label Label ℂ) .o .c1 ≠ 0)
    (F G : UpperHalfPlane → Label → ℂ) (hF : ∀ i, MDiff (fun τ => F τ i))
    (hG : ∀ i, MDiff (fun τ => G τ i))
    (hFcov : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (γ • τ) = (σ γ : Matrix Label Label ℂ) *ᵥ F τ)
    (hGcov : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), G (γ • τ) = (σ γ : Matrix Label Label ℂ) *ᵥ G τ)
    (hpp : ∀ i, UpperHalfPlane.IsBoundedAtImInfty (fun τ => F τ i - G τ i)) : F = G :=
  pole_cancellation σ hfin (no_invariant_vector σ hT hS) F G hF hG hFcov hGcov hpp

/-- `‖c q^e‖ = ‖c‖ exp(-2π e Im τ)` for `q^e = exp(2πi e τ)`. -/
theorem norm_qterm (c : ℂ) (e : ℝ) (z : UpperHalfPlane) :
    ‖c * Complex.exp (2 * Real.pi * I * e * z)‖ = ‖c‖ * Real.exp (-2 * Real.pi * e * z.im) := by
  have hre : ((2 * Real.pi * I * e * z : ℂ)).re = -2 * Real.pi * e * z.im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [norm_mul, Complex.norm_exp, hre]

/-- A `q`-series `∑ₙ cₙ q^{eₙ}` (`q^e = exp(2πi e τ)`) whose nonzero terms have nonnegative
exponents and which converges absolutely at height `y₀` is bounded at `i∞`. -/
theorem isBoundedAtImInfty_qseries (e : ℕ → ℝ) (c : ℕ → ℂ) (he : ∀ n, c n ≠ 0 → 0 ≤ e n)
    (y₀ : ℝ) (hsum : Summable fun n => ‖c n‖ * Real.exp (-2 * Real.pi * e n * y₀)) :
    UpperHalfPlane.IsBoundedAtImInfty
      (fun τ : UpperHalfPlane => ∑' n, c n * Complex.exp (2 * Real.pi * I * e n * τ)) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨∑' n, ‖c n‖ * Real.exp (-2 * Real.pi * e n * y₀), y₀, fun z hz => ?_⟩
  have hle : ∀ n, ‖c n‖ * Real.exp (-2 * Real.pi * e n * z.im) ≤
      ‖c n‖ * Real.exp (-2 * Real.pi * e n * y₀) := by
    intro n
    by_cases hc : c n = 0
    · simp [hc]
    · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.2
      have h0 := he n hc
      have hpi := Real.pi_pos
      nlinarith [mul_nonneg (mul_nonneg hpi.le h0) (sub_nonneg.2 hz)]
  have hs : Summable fun n => ‖c n‖ * Real.exp (-2 * Real.pi * e n * z.im) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hle hsum
  have hs' : Summable fun n => ‖c n * Complex.exp (2 * Real.pi * I * e n * z)‖ := by
    simpa only [norm_qterm] using hs
  calc ‖∑' n, c n * Complex.exp (2 * Real.pi * I * e n * z)‖
      ≤ ∑' n, ‖c n * Complex.exp (2 * Real.pi * I * e n * z)‖ := norm_tsum_le_tsum_norm hs'
    _ = ∑' n, ‖c n‖ * Real.exp (-2 * Real.pi * e n * z.im) := by simp only [norm_qterm]
    _ ≤ ∑' n, ‖c n‖ * Real.exp (-2 * Real.pi * e n * y₀) := hs.tsum_le_tsum hle hsum

/-- **"The same `γ`" suffices** (the step from equal principal parts to `hpp`).  If every
coordinate of `F` and `G` is a `q`-series `∑ₙ aₗ(n) q^{n + λₗ}`, `∑ₙ bₗ(n) q^{n + λₗ}`, absolutely
convergent at every height, and the coefficients agree whenever the exponent `n + λₗ` is negative
(equal principal parts: the vacuum coefficient `1` and `γ`, by `Characters.pole_iff` and strict
positivity of the nonvacuum lowest weights), then `F = G`. -/
theorem character_vector_unique_of_qexp (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup Label ℂ)
    (hfin : (Set.range σ).Finite)
    (hT : (σ ModularGroup.T : Matrix Label Label ℂ) = Matrix.diagonal tEigen)
    (hS : (σ ModularGroup.S : Matrix Label Label ℂ) .o .c1 ≠ 0)
    (F G : UpperHalfPlane → Label → ℂ) (hF : ∀ i, MDiff (fun τ => F τ i))
    (hG : ∀ i, MDiff (fun τ => G τ i))
    (hFcov : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (γ • τ) = (σ γ : Matrix Label Label ℂ) *ᵥ F τ)
    (hGcov : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), G (γ • τ) = (σ γ : Matrix Label Label ℂ) *ᵥ G τ)
    (lam : Label → ℝ) (a b : Label → ℕ → ℂ)
    (hFq : ∀ τ l, F τ l =
      ∑' n : ℕ, a l n * Complex.exp (2 * Real.pi * I * (((n : ℝ) + lam l : ℝ) : ℂ) * τ))
    (hGq : ∀ τ l, G τ l =
      ∑' n : ℕ, b l n * Complex.exp (2 * Real.pi * I * (((n : ℝ) + lam l : ℝ) : ℂ) * τ))
    (ha : ∀ l (y : ℝ), 0 < y →
      Summable fun n : ℕ => ‖a l n‖ * Real.exp (-2 * Real.pi * ((n : ℝ) + lam l) * y))
    (hb : ∀ l (y : ℝ), 0 < y →
      Summable fun n : ℕ => ‖b l n‖ * Real.exp (-2 * Real.pi * ((n : ℝ) + lam l) * y))
    (hpolar : ∀ l (n : ℕ), (n : ℝ) + lam l < 0 → a l n = b l n) : F = G := by
  refine character_vector_unique σ hfin hT hS F G hF hG hFcov hGcov fun l => ?_
  have hsumτ : ∀ (c : ℕ → ℂ) (τ : UpperHalfPlane),
      (∀ y : ℝ, 0 < y →
        Summable fun n : ℕ => ‖c n‖ * Real.exp (-2 * Real.pi * ((n : ℝ) + lam l) * y)) →
      Summable fun n : ℕ => c n * Complex.exp (2 * Real.pi * I * (((n : ℝ) + lam l : ℝ) : ℂ) * τ) := by
    intro c τ h
    refine Summable.of_norm ?_
    simpa only [norm_qterm] using h τ.im τ.im_pos
  have hdiff : (fun τ => F τ l - G τ l) = fun τ : UpperHalfPlane => ∑' n : ℕ,
      (a l n - b l n) * Complex.exp (2 * Real.pi * I * (((n : ℝ) + lam l : ℝ) : ℂ) * τ) := by
    funext τ
    rw [hFq, hGq, ← Summable.tsum_sub (hsumτ _ τ (ha l)) (hsumτ _ τ (hb l))]
    congr 1
    funext n
    ring
  rw [hdiff]
  refine isBoundedAtImInfty_qseries (fun n => (n : ℝ) + lam l) (fun n => a l n - b l n)
    (fun n hn => ?_) 1 ?_
  · by_contra hneg
    exact hn (sub_eq_zero.2 (hpolar l n (lt_of_not_ge hneg)))
  · refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((ha l 1 one_pos).add (hb l 1 one_pos))
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le

/-- In a character vector written as `∑ₙ aₗ(n) q^{n + tₗ - 1/3}` (`tₗ = twistExp l`, `c/24 = 1/3`),
an exponent is negative only for `n = 0` at the twist-zero labels `o, b, a, c₀` and at the
twist-`2/13` label `d₃` (where it is `-7/39`). -/
theorem polar_cases (l : Label) (n : ℕ)
    (h : (n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3) < 0) :
    n = 0 ∧ (l = .o ∨ l = .b ∨ l = .a ∨ l = .c0 ∨ l = .d3) := by
  have ht : (0 : ℝ) ≤ ((twistExp l : ℚ) : ℝ) := by
    cases l <;> norm_num [twistExp]
  have hn : n = 0 := by
    by_contra hn
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    linarith
  subst hn
  refine ⟨rfl, ?_⟩
  cases l <;> first
    | (exfalso; norm_num [twistExp] at h; done)
    | decide
    | simp

/-- **Lemma `lem:haagerup-character-unique`, as stated.**  Two character vectors
`Fₗ = ∑ₙ aₗ(n) q^{n + tₗ - 1/3}`, `Gₗ = ∑ₙ bₗ(n) q^{n + tₗ - 1/3}` for this modular representation
(absolutely convergent on `ℍ`) with the same vacuum coefficient, no weight-zero vectors in the
nonvacuum twist-zero modules (strict positivity of nonvacuum lowest weights), and the same `γ`
(the coefficient of `q^{-7/39}` in the twist-`2/13` coordinate) coincide. -/
theorem haagerup_character_unique (σ : SL(2, ℤ) →* Matrix.GeneralLinearGroup Label ℂ)
    (hfin : (Set.range σ).Finite)
    (hT : (σ ModularGroup.T : Matrix Label Label ℂ) = Matrix.diagonal tEigen)
    (hS : (σ ModularGroup.S : Matrix Label Label ℂ) .o .c1 ≠ 0)
    (F G : UpperHalfPlane → Label → ℂ) (hF : ∀ i, MDiff (fun τ => F τ i))
    (hG : ∀ i, MDiff (fun τ => G τ i))
    (hFcov : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), F (γ • τ) = (σ γ : Matrix Label Label ℂ) *ᵥ F τ)
    (hGcov : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane), G (γ • τ) = (σ γ : Matrix Label Label ℂ) *ᵥ G τ)
    (a b : Label → ℕ → ℂ)
    (hFq : ∀ τ l, F τ l = ∑' n : ℕ, a l n *
      Complex.exp (2 * Real.pi * I * (((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3) : ℝ) : ℂ) * τ))
    (hGq : ∀ τ l, G τ l = ∑' n : ℕ, b l n *
      Complex.exp (2 * Real.pi * I * (((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3) : ℝ) : ℂ) * τ))
    (ha : ∀ l (y : ℝ), 0 < y → Summable fun n : ℕ =>
      ‖a l n‖ * Real.exp (-2 * Real.pi * ((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3)) * y))
    (hb : ∀ l (y : ℝ), 0 < y → Summable fun n : ℕ =>
      ‖b l n‖ * Real.exp (-2 * Real.pi * ((n : ℝ) + (((twistExp l : ℚ) : ℝ) - 1 / 3)) * y))
    (hvac : a .o 0 = b .o 0)
    (hpos : ∀ l, (l = .b ∨ l = .a ∨ l = .c0) → a l 0 = 0 ∧ b l 0 = 0)
    (hγ : a .d3 0 = b .d3 0) : F = G := by
  refine character_vector_unique_of_qexp σ hfin hT hS F G hF hG hFcov hGcov
    (fun l => ((twistExp l : ℚ) : ℝ) - 1 / 3) a b hFq hGq ha hb fun l n hn => ?_
  obtain ⟨rfl, hl⟩ := polar_cases l n hn
  rcases hl with rfl | rfl | rfl | rfl | rfl
  · exact hvac
  · rw [(hpos .b (Or.inl rfl)).1, (hpos .b (Or.inl rfl)).2]
  · rw [(hpos .a (Or.inr (Or.inl rfl))).1, (hpos .a (Or.inr (Or.inl rfl))).2]
  · rw [(hpos .c0 (Or.inr (Or.inr rfl))).1, (hpos .c0 (Or.inr (Or.inr rfl))).2]
  · exact hγ

#print axioms isBoundedAtImInfty_qseries
#print axioms haagerup_character_unique
#print axioms character_vector_unique
#print axioms character_vector_unique_of_qexp

end HaagerupIzumi.C8.CharacterUniqueness
