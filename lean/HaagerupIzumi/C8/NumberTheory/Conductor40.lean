module

public import HaagerupIzumi.C8.NumberTheory.MultiplicityOne
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.Group.Multiset

@[expose] public section

/-!
# Finite facts behind Lemma `lem:conductor40` (manuscript lines 3949–3988)

**Lemma `lem:conductor40` itself is not proved here**; it remains the hypothesis
`Conductor40Bound` of `MultiplicityOne.lean`.  Its proof averages a multiset of roots of unity
over the Galois group of a cyclotomic field fixing `√10` and evaluates every orbit sum through
Ramanujan sums and imprimitive Gauss sums of the conductor-40 character; that general orbit
analysis is not formalized.

This file proves the explicit facts about primitive fortieth roots used in the equality case,
with `ω = exp(2πi/40)` and `χ₄₀(u) = (2/u)(u/5)` (the primitive real character of conductor
`40`, i.e. of `ℚ(√10)`):

* `zeta40_cyclotomic`: `Φ₄₀(ω) = ω¹⁶ - ω¹² + ω⁸ - ω⁴ + 1 = 0`;
* `plus40_spec`, `minus40_spec`: the two classes `O₊ = {1,3,9,13,27,31,37,39}` and
  `O₋ = {7,11,17,19,21,23,29,33}` of units mod 40 with `χ₄₀ = ±1`; `O₊` is closed under
  multiplication and `O₊ · O₋ ⊆ O₋` (`plus40_mul`, `plus40_mul_minus40`), so `u ↦ ωᵘ` for
  `u ∈ O₊` permutes each orbit; and `x ↦ x + 20` swaps them (`χ₄₀(x+20) = -χ₄₀(x)`);
* `orbitPlus40_eq`, `orbitMinus40_eq`: the orbit sums are `+√10` and `-√10`
  (eight roots each, so a nonzero `√10`-contribution costs eight roots);
* `orbitMinus40_sq_sum`, `orbitPlus40_sq_sum`: each orbit has squared sum `0`; indeed
  `minus40_mod20` shows that reduction modulo `20` gives every unit mod 20 once;
* `conductor40_sharp`: the bound of `Conductor40Bound` is attained, with the stated equality
  clause, by `a` copies of `-1` and `b` copies of `O₋`.
-/

namespace HaagerupIzumi.C8.NumberTheory

/-- `ω₄₀ = exp(2πi/40)`. -/
noncomputable def zeta40 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 40)

theorem zeta40_isPrimitiveRoot : IsPrimitiveRoot zeta40 40 := by
  have h := Complex.isPrimitiveRoot_exp 40 (by norm_num)
  simpa [zeta40] using h

theorem zeta40_pow_forty : zeta40 ^ 40 = 1 := zeta40_isPrimitiveRoot.pow_eq_one

/-- `Φ₄₀(ω) = 0`, from `ω²⁰ = -1` and `ω⁴ ≠ -1`. -/
theorem zeta40_cyclotomic :
    zeta40 ^ 16 - zeta40 ^ 12 + zeta40 ^ 8 - zeta40 ^ 4 + 1 = 0 := by
  have hp := zeta40_isPrimitiveRoot
  have h20 : zeta40 ^ 20 ≠ 1 := hp.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h8 : zeta40 ^ 8 ≠ 1 := hp.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hm20 : zeta40 ^ 20 = -1 := by
    have h : (zeta40 ^ 20 - 1) * (zeta40 ^ 20 + 1) = 0 := by
      linear_combination zeta40_pow_forty
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) h20
    · linear_combination h
  have h4 : zeta40 ^ 4 + 1 ≠ 0 := by
    intro h
    apply h8
    have h' : zeta40 ^ 4 = -1 := by linear_combination h
    calc zeta40 ^ 8 = (zeta40 ^ 4) ^ 2 := by ring
      _ = 1 := by rw [h']; norm_num
  have h : (zeta40 ^ 4 + 1) * (zeta40 ^ 16 - zeta40 ^ 12 + zeta40 ^ 8 - zeta40 ^ 4 + 1) = 0 := by
    linear_combination hm20
  rcases mul_eq_zero.mp h with h | h
  · exact absurd h h4
  · exact h

theorem zeta40_pow_re (k : ℕ) : (zeta40 ^ k).re = Real.cos (2 * Real.pi * k / 40) := by
  rw [zeta40, ← Complex.exp_nat_mul]
  have h : (k : ℂ) * (2 * Real.pi * Complex.I / 40) =
      ((2 * Real.pi * k / 40 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_re]

/-! ### The conductor-40 character and its two classes of units -/

/-- `χ₄₀(u) = (2/u)(u/5)`: `(2/u) = 1` iff `u ≡ ±1 (mod 8)`, `(u/5) = 1` iff `u ≡ ±1 (mod 5)`
(meaningful for `u` prime to `10`). -/
def chi40 (u : ℕ) : ℤ :=
  (if u % 8 = 1 ∨ u % 8 = 7 then 1 else -1) * (if u % 5 = 1 ∨ u % 5 = 4 then 1 else -1)

/-- Units mod 40 with `χ₄₀ = 1` (the subgroup fixing `√10`). -/
def plus40 : Finset ℕ := {1, 3, 9, 13, 27, 31, 37, 39}

/-- Units mod 40 with `χ₄₀ = -1`. -/
def minus40 : Finset ℕ := {7, 11, 17, 19, 21, 23, 29, 33}

theorem plus40_spec : ∀ u < 40, u ∈ plus40 ↔ (u % 2 = 1 ∧ u % 5 ≠ 0 ∧ chi40 u = 1) := by
  decide

theorem minus40_spec : ∀ u < 40, u ∈ minus40 ↔ (u % 2 = 1 ∧ u % 5 ≠ 0 ∧ chi40 u = -1) := by
  decide

theorem plus40_mul : ∀ u ∈ plus40, ∀ v ∈ plus40, u * v % 40 ∈ plus40 := by
  decide

theorem plus40_mul_minus40 : ∀ u ∈ plus40, ∀ v ∈ minus40, u * v % 40 ∈ minus40 := by
  decide

/-- `χ₄₀(x + 20) = -χ₄₀(x)`. -/
theorem add_twenty_swap :
    (∀ u ∈ plus40, (u + 20) % 40 ∈ minus40) ∧ (∀ u ∈ minus40, (u + 20) % 40 ∈ plus40) := by
  decide

/-- Reduction modulo `20` maps `O₋` onto the eight units modulo `20`. -/
theorem minus40_mod20 : minus40.image (· % 20) = {1, 3, 7, 9, 11, 13, 17, 19} := by
  decide

theorem minus40_card : minus40.card = 8 := by
  decide

/-! ### Orbit sums -/

/-- The orbit sum over `O₊`. -/
noncomputable def orbitPlus40 : ℂ :=
  zeta40 ^ 1 + zeta40 ^ 3 + zeta40 ^ 9 + zeta40 ^ 13 + zeta40 ^ 27 + zeta40 ^ 31 +
    zeta40 ^ 37 + zeta40 ^ 39

/-- The orbit sum over `O₋`. -/
noncomputable def orbitMinus40 : ℂ :=
  zeta40 ^ 7 + zeta40 ^ 11 + zeta40 ^ 17 + zeta40 ^ 19 + zeta40 ^ 21 + zeta40 ^ 23 +
    zeta40 ^ 29 + zeta40 ^ 33

/-- The primitive fortieth roots sum to `μ(40) = 0`. -/
theorem orbit40_add : orbitPlus40 + orbitMinus40 = 0 := by
  unfold orbitPlus40 orbitMinus40
  linear_combination (zeta40 ^ 23 + zeta40 ^ 21 + zeta40 ^ 19 + 2 * zeta40 ^ 17 +
    zeta40 ^ 15 + 2 * zeta40 ^ 13 + 2 * zeta40 ^ 11 + zeta40 ^ 9 + 2 * zeta40 ^ 7 +
    zeta40 ^ 5 + zeta40 ^ 3 + zeta40) * zeta40_cyclotomic

/-- The Gauss sum of `χ₄₀` squares to `40`. -/
theorem orbit40_sub_sq : (orbitPlus40 - orbitMinus40) ^ 2 = 40 := by
  unfold orbitPlus40 orbitMinus40
  linear_combination (zeta40 ^ 62 + 2 * zeta40 ^ 60 + 2 * zeta40 ^ 58 + zeta40 ^ 54 -
    2 * zeta40 ^ 52 + zeta40 ^ 50 + 2 * zeta40 ^ 46 - 8 * zeta40 ^ 44 - zeta40 ^ 42 -
    14 * zeta40 ^ 40 - 4 * zeta40 ^ 38 - 2 * zeta40 ^ 34 + 4 * zeta40 ^ 32 -
    2 * zeta40 ^ 30 - 4 * zeta40 ^ 26 + 26 * zeta40 ^ 24 - zeta40 ^ 22 + 32 * zeta40 ^ 20 +
    2 * zeta40 ^ 18 + zeta40 ^ 14 - 2 * zeta40 ^ 12 + zeta40 ^ 10 + 2 * zeta40 ^ 6 -
    38 * zeta40 ^ 4 + zeta40 ^ 2 - 40) * zeta40_cyclotomic

/-- `Re(∑_{O₊} ωᵘ) = 2(cos(π/20) - cos(7π/20) + cos(3π/20) + cos(9π/20)) > 0`. -/
theorem orbitPlus40_re_pos : 0 < orbitPlus40.re := by
  unfold orbitPlus40
  simp only [Complex.add_re, zeta40_pow_re]
  have hπ := Real.pi_pos
  have e1 : Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 40) = Real.cos (Real.pi / 20) := by
    congr 1; push_cast; ring
  have e3 : Real.cos (2 * Real.pi * ((3 : ℕ) : ℝ) / 40) = Real.cos (3 * Real.pi / 20) := by
    congr 1; push_cast; ring
  have e9 : Real.cos (2 * Real.pi * ((9 : ℕ) : ℝ) / 40) = Real.cos (9 * Real.pi / 20) := by
    congr 1; push_cast; ring
  have e13 : Real.cos (2 * Real.pi * ((13 : ℕ) : ℝ) / 40) = -Real.cos (7 * Real.pi / 20) := by
    rw [← Real.cos_pi_sub]; congr 1; push_cast; ring
  have e27 : Real.cos (2 * Real.pi * ((27 : ℕ) : ℝ) / 40) = -Real.cos (7 * Real.pi / 20) := by
    rw [← Real.cos_add_pi]; congr 1; push_cast; ring
  have e31 : Real.cos (2 * Real.pi * ((31 : ℕ) : ℝ) / 40) = Real.cos (9 * Real.pi / 20) := by
    rw [← Real.cos_two_pi_sub]; congr 1; push_cast; ring
  have e37 : Real.cos (2 * Real.pi * ((37 : ℕ) : ℝ) / 40) = Real.cos (3 * Real.pi / 20) := by
    rw [← Real.cos_two_pi_sub]; congr 1; push_cast; ring
  have e39 : Real.cos (2 * Real.pi * ((39 : ℕ) : ℝ) / 40) = Real.cos (Real.pi / 20) := by
    rw [← Real.cos_two_pi_sub]; congr 1; push_cast; ring
  have b17 : Real.cos (7 * Real.pi / 20) < Real.cos (Real.pi / 20) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have b3 : 0 < Real.cos (3 * Real.pi / 20) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have b9 : 0 < Real.cos (9 * Real.pi / 20) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  linarith

/-- The `χ₄₀ = 1` orbit of primitive fortieth roots sums to `+√10`. -/
theorem orbitPlus40_eq : orbitPlus40 = (Real.sqrt 10 : ℂ) := by
  have hs : ((Real.sqrt 10 : ℝ) : ℂ) ^ 2 = 10 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  have hadd := orbit40_add
  have hsq := orbit40_sub_sq
  have hP : orbitPlus40 ^ 2 = 10 := by
    linear_combination (1 / 4) * hsq + (3 * orbitPlus40 - orbitMinus40) / 4 * hadd
  have hprod : (orbitPlus40 - Real.sqrt 10) * (orbitPlus40 + Real.sqrt 10) = 0 := by
    linear_combination hP - hs
  rcases mul_eq_zero.mp hprod with h | h
  · linear_combination h
  · exfalso
    have hN : orbitPlus40 = ((-Real.sqrt 10 : ℝ) : ℂ) := by
      push_cast
      linear_combination h
    have hre : orbitPlus40.re = -Real.sqrt 10 := by
      rw [hN, Complex.ofReal_re]
    have := orbitPlus40_re_pos
    have h10 := Real.sqrt_nonneg 10
    linarith

/-- The `χ₄₀ = -1` orbit of primitive fortieth roots sums to `-√10`. -/
theorem orbitMinus40_eq : orbitMinus40 = -(Real.sqrt 10 : ℂ) := by
  linear_combination orbit40_add - orbitPlus40_eq

/-- The squared roots of the negative orbit sum to `μ(20) = 0`. -/
theorem orbitMinus40_sq_sum :
    (zeta40 ^ 7) ^ 2 + (zeta40 ^ 11) ^ 2 + (zeta40 ^ 17) ^ 2 + (zeta40 ^ 19) ^ 2 +
      (zeta40 ^ 21) ^ 2 + (zeta40 ^ 23) ^ 2 + (zeta40 ^ 29) ^ 2 + (zeta40 ^ 33) ^ 2 = 0 := by
  linear_combination (zeta40 ^ 50 + zeta40 ^ 46 + zeta40 ^ 42 + zeta40 ^ 38 + zeta40 ^ 26 +
    zeta40 ^ 22 + zeta40 ^ 18 + zeta40 ^ 14) * zeta40_cyclotomic

/-- The squared roots of the positive orbit also sum to `0`. -/
theorem orbitPlus40_sq_sum :
    (zeta40 ^ 1) ^ 2 + (zeta40 ^ 3) ^ 2 + (zeta40 ^ 9) ^ 2 + (zeta40 ^ 13) ^ 2 +
      (zeta40 ^ 27) ^ 2 + (zeta40 ^ 31) ^ 2 + (zeta40 ^ 37) ^ 2 + (zeta40 ^ 39) ^ 2 = 0 := by
  linear_combination (zeta40 ^ 62 + 2 * zeta40 ^ 58 + zeta40 ^ 54 + zeta40 ^ 46 -
    zeta40 ^ 38 - zeta40 ^ 26 + zeta40 ^ 18 + zeta40 ^ 10 + 2 * zeta40 ^ 6 + zeta40 ^ 2) *
    zeta40_cyclotomic

/-! ### Sharpness of `Conductor40Bound` -/

/-- The negative orbit as a multiset of roots. -/
noncomputable def minusOrbit : Multiset ℂ := minus40.val.map (fun u => zeta40 ^ u)

theorem minusOrbit_card : Multiset.card minusOrbit = 8 := by
  rw [minusOrbit, Multiset.card_map]
  exact minus40_card

theorem minusOrbit_sum : minusOrbit.sum = -(Real.sqrt 10 : ℂ) := by
  rw [← orbitMinus40_eq, minusOrbit, orbitMinus40]
  simp [minus40, add_assoc]

theorem minusOrbit_sq_sum : (minusOrbit.map (fun z => z ^ 2)).sum = 0 := by
  rw [← orbitMinus40_sq_sum, minusOrbit, Multiset.map_map]
  simp [minus40, add_assoc]

theorem minusOrbit_roots : ∀ z ∈ minusOrbit, IsRootOfUnity z := by
  intro z hz
  obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp hz
  refine ⟨40, by norm_num, ?_⟩
  show (zeta40 ^ u) ^ 40 = 1
  rw [← pow_mul, mul_comm, pow_mul, zeta40_pow_forty, one_pow]

theorem nsmul_map {s : Multiset ℂ} (f : ℂ → ℂ) (k : ℕ) : (k • s).map f = k • s.map f := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, Multiset.map_add, ih, succ_nsmul]

/-- `a` copies of `-1` together with `b` copies of the negative orbit `O₋`. -/
noncomputable def sharpMultiset (a b : ℕ) : Multiset ℂ :=
  Multiset.replicate a (-1 : ℂ) + b • minusOrbit

/-- **The equality case of `lem:conductor40` is attained**: `sharpMultiset a b` consists of
`a + 8b` roots of unity with sum `-a - b√10` and squared sum `a`.  (So `Conductor40Bound` is
sharp and its equality clause is consistent.) -/
theorem conductor40_sharp (a b : ℕ) :
    (∀ z ∈ sharpMultiset a b, IsRootOfUnity z) ∧
      Multiset.card (sharpMultiset a b) = a + 8 * b ∧
      (sharpMultiset a b).sum = -(a : ℂ) - (b : ℂ) * (Real.sqrt 10 : ℂ) ∧
      ((sharpMultiset a b).map (fun z => z ^ 2)).sum = (a : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    rw [sharpMultiset] at hz
    rcases Multiset.mem_add.mp hz with h | h
    · rw [Multiset.eq_of_mem_replicate h]
      exact ⟨2, by norm_num, by norm_num⟩
    · exact minusOrbit_roots z (Multiset.mem_of_mem_nsmul h)
  · rw [sharpMultiset, Multiset.card_add, Multiset.card_replicate, Multiset.card_nsmul,
      minusOrbit_card]
    ring
  · rw [sharpMultiset, Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_nsmul,
      minusOrbit_sum]
    simp only [nsmul_eq_mul]
    ring
  · rw [sharpMultiset, Multiset.map_add, Multiset.map_replicate, nsmul_map, Multiset.sum_add,
      Multiset.sum_replicate, Multiset.sum_nsmul, minusOrbit_sq_sum]
    simp

#print axioms zeta40_cyclotomic
#print axioms plus40_spec
#print axioms minus40_mod20
#print axioms orbitPlus40_eq
#print axioms orbitMinus40_eq
#print axioms orbitMinus40_sq_sum
#print axioms conductor40_sharp

end HaagerupIzumi.C8.NumberTheory
