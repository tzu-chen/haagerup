module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The `E₈` fixed-point bound in the rank-four (`m = 2`) case

Appendix G of `c8_expanded_20260929/haagerup_c8_expanded.tex`, lines 3367–3387.

* `average_trace_eq_finrank_invariants` — for a finite group acting linearly on a
  finite-dimensional complex vector space, `dim V^G = |G|⁻¹ ∑_g tr ρ(g)`
  (proved from Mathlib's averaging projection).
* `e8_A4_invariants_ge` — if `A₄` (order 12, three involutions, all other
  nonidentity elements of order three) acts on a `248`-dimensional space with
  real parts of traces `≥ -8` on involutions and `≥ -4` on elements of order three,
  then `dim V^{A₄} ≥ (248 - 24 - 32)/12 = 16 > 6 = dim U₁`.
* `order3_trace` — `tr g = (3 dim 𝔤^g - 248)/2` for an order-three automorphism whose
  two nontrivial eigenspaces have equal dimension (they are dual under the Killing
  form); `order2_trace` likewise `tr g = 2 dim 𝔤^g - 248`.
* `e8_order2_traces`, `e8_order3_traces` — the trace values `-8, 24` and
  `-4, 5, 14, 77` for the fixed subalgebras of dimensions `120, 136` and
  `80, 86, 92, 134`.

External inputs (not proved): Kac's classification of finite-order automorphisms
of `E₈` (the lists of fixed subalgebras, via Kac coordinates of total mark two or
three), the twisted `A₄` double from Etingof–Gelaki–Ostrik, the extension
correspondence and Dong–Mason's uniqueness of `V_{E₈}`.  They enter only as the
trace hypotheses `htr2`, `htr3` of `e8_A4_invariants_ge`.
-/

namespace HaagerupIzumi.C8.Fusion

/-- Averaging the character: `|G|⁻¹ ∑_g tr ρ(g) = dim V^G`. -/
theorem average_trace_eq_finrank_invariants {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, LinearMap.trace ℂ V (ρ g) =
      Module.finrank ℂ (Representation.invariants ρ) := by
  have : Invertible (Fintype.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [← (Representation.isProj_averageMap ρ).trace]
  simp [GroupAlgebra.average, map_sum]

/-- The `A₄` average (lines 3383–3387): `dim (E₈)^{A₄} ≥ (248 + 3(-8) + 8(-4))/12 = 16`. -/
theorem e8_A4_invariants_ge {G V : Type*} [Group G] [Fintype G] [DecidableEq G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
    (hdim : Module.finrank ℂ V = 248) (hcard : Fintype.card G = 12)
    (hord : ∀ g : G, g ≠ 1 → orderOf g = 2 ∨ orderOf g = 3)
    (hinv : (Finset.univ.filter fun g : G => orderOf g = 2).card = 3)
    (htr2 : ∀ g : G, orderOf g = 2 → -8 ≤ (LinearMap.trace ℂ V (ρ g)).re)
    (htr3 : ∀ g : G, orderOf g = 3 → -4 ≤ (LinearMap.trace ℂ V (ρ g)).re) :
    16 ≤ Module.finrank ℂ (Representation.invariants ρ) := by
  have havg := average_trace_eq_finrank_invariants ρ
  rw [hcard] at havg
  push_cast at havg
  have hsum : ∑ g : G, LinearMap.trace ℂ V (ρ g) =
      12 * (Module.finrank ℂ (Representation.invariants ρ) : ℂ) := by
    rw [← havg, ← mul_assoc, mul_inv_cancel₀ (by norm_num : (12 : ℂ) ≠ 0), one_mul]
  have hre : ∑ g : G, (LinearMap.trace ℂ V (ρ g)).re =
      12 * (Module.finrank ℂ (Representation.invariants ρ) : ℝ) := by
    have h := congrArg Complex.re hsum
    rw [Complex.re_sum] at h
    rw [h]
    simp
  have hle : ∑ g : G, (-4 + (if g = 1 then (252 : ℝ) else 0) +
      (if orderOf g = 2 then (-4 : ℝ) else 0)) ≤
      ∑ g : G, (LinearMap.trace ℂ V (ρ g)).re := by
    apply Finset.sum_le_sum
    intro g _
    by_cases h1 : g = 1
    · have h2 : orderOf g ≠ 2 := by rw [h1, orderOf_one]; norm_num
      rw [if_pos h1, if_neg h2, h1, map_one, LinearMap.trace_one, hdim]
      norm_num
    · by_cases h2 : orderOf g = 2
      · rw [if_neg h1, if_pos h2]
        linarith [htr2 g h2]
      · rw [if_neg h1, if_neg h2]
        have h3 : orderOf g = 3 := (hord g h1).resolve_left h2
        linarith [htr3 g h3]
  have hval : ∑ g : G, (-4 + (if g = 1 then (252 : ℝ) else 0) +
      (if orderOf g = 2 then (-4 : ℝ) else 0)) = 192 := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      hcard, Finset.sum_ite_eq', ← Finset.sum_filter, Finset.sum_const, hinv]
    simp
    norm_num
  have h192 : (192 : ℝ) ≤ 12 * (Module.finrank ℂ (Representation.invariants ρ) : ℝ) := by
    rw [← hre, ← hval]
    exact hle
  have h16 : (16 : ℝ) ≤ (Module.finrank ℂ (Representation.invariants ρ) : ℝ) := by linarith
  exact_mod_cast h16

/-- `16 > 6 = dim U₁`: the `m = 2` case is impossible. -/
theorem e8_A4_contradiction (n : ℕ) (h16 : 16 ≤ n) : n ≠ 6 := by omega

/-- Order-three trace formula: if the two nontrivial eigenspaces have the same dimension `e`
and `dim 𝔤^g = f`, then `tr g = f + eω + eω² = (3f - 248)/2`. -/
theorem order3_trace (f e : ℝ) (ω : ℂ) (hω : ω ^ 2 + ω + 1 = 0) (hdim : f + 2 * e = 248) :
    (f : ℂ) + e * ω + e * ω ^ 2 = (((3 * f - 248) / 2 : ℝ) : ℂ) := by
  have hdim' : (f : ℂ) + 2 * e = 248 := by exact_mod_cast hdim
  push_cast
  linear_combination (e : ℂ) * hω - (1 / 2 : ℂ) * hdim'

/-- Order-two trace formula: `tr g = dim 𝔤^g - (248 - dim 𝔤^g) = 2 dim 𝔤^g - 248`. -/
theorem order2_trace (f : ℝ) : f - (248 - f) = 2 * f - 248 := by ring

/-- `D₈` (dim 120) and `E₇ + A₁` (dim 136): traces `-8` and `24`. -/
theorem e8_order2_traces : (2 * 120 - 248 : ℤ) = -8 ∧ (2 * 136 - 248 : ℤ) = 24 := by
  norm_num

/-- `A₈, E₆ + A₂, D₇ + ℂ, E₇ + ℂ` (dims 80, 86, 92, 134): traces `-4, 5, 14, 77`. -/
theorem e8_order3_traces :
    ((3 * 80 - 248) / 2 : ℚ) = -4 ∧ ((3 * 86 - 248) / 2 : ℚ) = 5 ∧
      ((3 * 92 - 248) / 2 : ℚ) = 14 ∧ ((3 * 134 - 248) / 2 : ℚ) = 77 := by
  norm_num

/-- The numerical average `(248 + 3·(-8) + 8·(-4))/12 = 16`. -/
theorem e8_A4_average_value : ((248 : ℚ) + 3 * (-8) + 8 * (-4)) / 12 = 16 := by norm_num

end HaagerupIzumi.C8.Fusion

#print axioms HaagerupIzumi.C8.Fusion.average_trace_eq_finrank_invariants
#print axioms HaagerupIzumi.C8.Fusion.e8_A4_invariants_ge
#print axioms HaagerupIzumi.C8.Fusion.order3_trace
