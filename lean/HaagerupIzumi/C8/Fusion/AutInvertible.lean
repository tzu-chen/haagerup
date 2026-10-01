module

public import HaagerupIzumi.C8.Fusion.BasedRing
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

@[expose] public section

/-!
# Automorphisms give invertible boundary objects: the based-ring core

Lemma `lem:automorphisms-invertibles` of
`c8_expanded_20260929/haagerup_c8_expanded.tex` (lines 3273–3293).

Categorical input (not proved here): under the two-product description of the
canonical Lagrangian algebra `I(𝟙)` (Bischoff–Jones, \[BJ, Lemma 3.1 and
Cor. 3.4\]), composition of endomorphisms is fusion-ring multiplication and the
primitive convolution idempotents are `d_a [a]`; an algebra automorphism `f` and
its inverse are convolution idempotents, hence have expansions with coefficients
`0` or `d_a`, and `f ∘ f⁻¹ = id` reads `x · y = [𝟙]` in the fusion ring.

Proved here (`aut_invertible`): if `x = ∑ x_a [a]`, `y = ∑ y_a [a]` have
coefficients `x_a, y_a ∈ {0, d_a}` with `d_a > 0` and `d_{a*} = d_a`, and
`x · y = [𝟙]`, then `x = [a]`, `y = [a*]` for a single invertible simple `a` with
`d_a = 1`.  Nonnegativity of the fusion coefficients rules out cancellation;
rigidity forces each pair in the two supports to be inverse invertibles.
-/

namespace HaagerupIzumi.C8.Fusion

open Finset BasedRing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lemma `lem:automorphisms-invertibles`, fusion-ring part.  `d` is the
(positive, duality-invariant) dimension function; `hxy` says
`(∑ x_i [i]) · (∑ y_j [j]) = [𝟙]` in the fusion ring. -/
theorem aut_invertible (R : BasedRing ι) (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (hdual : ∀ i, d (R.dual i) = d i)
    (x y : ι → ℝ) (hx : ∀ i, x i = 0 ∨ x i = d i) (hy : ∀ i, y i = 0 ∨ y i = d i)
    (hxy : ∀ l, ∑ i, ∑ j, x i * y j * (R.N i j l : ℝ) = if l = R.unit then 1 else 0) :
    ∃ a, R.IsInvertible a ∧ d a = 1 ∧ (∀ i, x i = if i = a then 1 else 0) ∧
      (∀ i, y i = if i = R.dual a then 1 else 0) := by
  have hx0 : ∀ i, 0 ≤ x i := fun i => by
    rcases hx i with h | h <;> simp [h, (hd i).le]
  have hy0 : ∀ i, 0 ≤ y i := fun i => by
    rcases hy i with h | h <;> simp [h, (hd i).le]
  -- products of supported simples have no non-unit constituent
  have hterm : ∀ l, l ≠ R.unit → ∀ i j, x i ≠ 0 → y j ≠ 0 → R.N i j l = 0 := by
    intro l hl i j hxi hyj
    have h := hxy l
    rw [if_neg hl] at h
    have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ ∑ j, x i * y j * (R.N i j l : ℝ) :=
      fun i _ => Finset.sum_nonneg (fun j _ =>
        mul_nonneg (mul_nonneg (hx0 i) (hy0 j)) (Nat.cast_nonneg _))
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (hx0 i) (hy0 j)) (Nat.cast_nonneg (R.N i j l)))).mp h1 j
      (Finset.mem_univ j)
    rcases mul_eq_zero.mp h2 with h3 | h3
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 hxi
      · exact absurd h4 hyj
    · exact_mod_cast h3
  -- rigidity: supported pairs are dual
  have hpair : ∀ i j, x i ≠ 0 → y j ≠ 0 → j = R.dual i := by
    intro i j hxi hyj
    obtain ⟨l, hl⟩ := R.exists_N_ne_zero i j
    by_cases hlu : l = R.unit
    · rw [hlu, R.N_unit_right] at hl
      by_contra hne
      exact hl (if_neg hne)
    · exact absurd (hterm l hlu i j hxi hyj) hl
  have hU := hxy R.unit
  rw [if_pos rfl] at hU
  obtain ⟨a, ha⟩ : ∃ a, x a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at hU
  obtain ⟨c, hc⟩ : ∃ c, y c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    simp [hcon] at hU
  have hca : c = R.dual a := hpair a c ha hc
  have hxsupp : ∀ i, x i ≠ 0 → i = a := fun i hi => by
    have h := hpair i c hi hc
    rw [hca] at h
    exact (R.dual_injective h).symm
  have hysupp : ∀ j, y j ≠ 0 → j = R.dual a := fun j hj => hpair a j ha hj
  have hxa : x a = d a := (hx a).resolve_left ha
  have hyc : y (R.dual a) ≠ 0 := by rw [← hca]; exact hc
  have hyd : y (R.dual a) = d a := by rw [(hy (R.dual a)).resolve_left hyc, hdual]
  have hsum : ∑ i, ∑ j, x i * y j * (R.N i j R.unit : ℝ) =
      x a * y (R.dual a) * (R.N a (R.dual a) R.unit : ℝ) := by
    rw [Fintype.sum_eq_single a]
    · rw [Fintype.sum_eq_single (R.dual a)]
      intro j hj
      have : y j = 0 := by
        by_contra h
        exact hj (hysupp j h)
      rw [this]
      ring
    · intro i hi
      have : x i = 0 := by
        by_contra h
        exact hi (hxsupp i h)
      simp [this]
  rw [hsum, hxa, hyd, R.N_unit_right, if_pos rfl] at hU
  have hda : d a = 1 := by
    have h1 : d a * d a = 1 := by simpa using hU
    nlinarith [hd a]
  refine ⟨a, ?_, hda, ?_, ?_⟩
  · intro l
    by_cases hl : l = R.unit
    · rw [hl, R.N_unit_right, if_pos rfl, if_pos rfl]
    · rw [if_neg hl]
      exact hterm l hl a (R.dual a) ha hyc
  · intro i
    by_cases hi : i = a
    · rw [if_pos hi, hi, hxa, hda]
    · rw [if_neg hi]
      by_contra h
      exact hi (hxsupp i h)
  · intro j
    by_cases hj : j = R.dual a
    · rw [if_pos hj, hj, hyd, hda]
    · rw [if_neg hj]
      by_contra h
      exact hj (hysupp j h)

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.aut_invertible
