module

public import HaagerupIzumi.C8.NumberTheory.MultiplicityOne
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# The six residual twists (Lemma `lem:six-residual-twists`, lines 4019–4051)

Let `ζ = exp(2πi/13)`, `N = {2,5,6,7,8,11}` (the quadratic nonresidues mod 13) and
`R = {1,3,4,9,10,12}` (the residues).  This file proves:

* (a) `nonresidue_linear_independent`, `nonresidue_powers_linearIndependent`: the six roots
  `ζⁿ`, `n ∈ N`, are linearly independent over `ℚ` (a rational relation is a polynomial of
  degree `≤ 11` vanishing at `ζ`, hence divisible by `Φ₁₃`, hence zero);
* (b) `periodN_eq`, `periodR_eq`: the Gauss periods `∑_{n∈N} ζⁿ = (-1-√13)/2` and
  `∑_{n∈R} ζⁿ = (-1+√13)/2` (from `(S_R - S_N)² = 13`, `S_R + S_N = -1` and the sign of
  `Re S_N`);
* (c) `two_mul_nonresidues13`, `sum_sq_nonresidues13_eq`: multiplication by two sends
  nonresidues to residues, so `∑_{n∈N} ζ²ⁿ = (-1+√13)/2`;
* `six_residual_twists`: Lemma `lem:six-residual-twists` — six residual central simples,
  each with `n_j = 1`, twists exactly the six nonresidue thirteenth roots, and `ε = ν₂(ρ) = 1` —
  given `NonresidueOrbitStep` (proved in `ThirteenOrbit.lean`; unconditional version
  `six_residual_twists_proved`);
* `epsilon_eq_one_of_larson`: independently, `ε = 1` follows from Larson's Theorem 1.3 alone
  (if `ε = -1`, twelve roots would sum to `-1 - 3√13`, needing `3 φ(26) = 36` roots).

## Hypotheses of the theorems in this file (both proved elsewhere)

* `NonresidueOrbitStep` — **the manuscript's own Galois-averaging step** in the proof of
  Lemma `lem:six-residual-twists` (lines 4025–4039): a multiset of six roots of unity with
  sum `(-1-√13)/2` consists of nonresidue thirteenth roots.  Proved in `ThirteenOrbit.lean`
  (`nonresidueOrbitStep`).
* `LarsonRootCount` (Larson Theorem 1.3) — only in `epsilon_eq_one_of_larson`; proved in
  `LarsonProof.lean` (`larsonRootCount`).
-/

namespace HaagerupIzumi.C8.NumberTheory

open Polynomial

/-- `ζ₁₃ = exp(2πi/13)`. -/
noncomputable def zeta13 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 13)

theorem zeta13_isPrimitiveRoot : IsPrimitiveRoot zeta13 13 := by
  have h := Complex.isPrimitiveRoot_exp 13 (by norm_num)
  simpa [zeta13] using h

theorem zeta13_pow_thirteen : zeta13 ^ 13 = 1 := zeta13_isPrimitiveRoot.pow_eq_one

theorem zeta13_geom : 1 + zeta13 + zeta13 ^ 2 + zeta13 ^ 3 + zeta13 ^ 4 + zeta13 ^ 5 +
    zeta13 ^ 6 + zeta13 ^ 7 + zeta13 ^ 8 + zeta13 ^ 9 + zeta13 ^ 10 + zeta13 ^ 11 +
    zeta13 ^ 12 = 0 := by
  have h := zeta13_isPrimitiveRoot.geom_sum_eq_zero (by norm_num : 1 < 13)
  simpa [Finset.sum_range_succ] using h

/-! ### Residues and nonresidues modulo 13 -/

/-- The quadratic nonresidues modulo `13`, as exponents in `[1, 12]`. -/
def nonresidues13 : Finset ℕ := {2, 5, 6, 7, 8, 11}

/-- The nonzero quadratic residues modulo `13`, as exponents in `[1, 12]`. -/
def residues13 : Finset ℕ := {1, 3, 4, 9, 10, 12}

theorem nonresidues13_spec : ∀ e ∈ nonresidues13, ∀ x : ZMod 13, x ^ 2 ≠ (e : ZMod 13) := by
  decide

theorem residues13_spec : ∀ e ∈ residues13, ∃ x : ZMod 13, x ^ 2 = (e : ZMod 13) := by
  decide

/-- (c) Multiplication by two sends nonresidues modulo `13` to residues. -/
theorem two_mul_nonresidues13 : ∀ e ∈ nonresidues13, 2 * e % 13 ∈ residues13 := by
  decide

theorem sum_nonresidues13 {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ e ∈ nonresidues13, f e = f 2 + f 5 + f 6 + f 7 + f 8 + f 11 := by
  simp [nonresidues13, Finset.sum_insert, add_assoc]

/-! ### (b) The two Gauss periods -/

/-- The Gauss period over the nonresidues. -/
noncomputable def periodN : ℂ :=
  zeta13 ^ 2 + zeta13 ^ 5 + zeta13 ^ 6 + zeta13 ^ 7 + zeta13 ^ 8 + zeta13 ^ 11

/-- The Gauss period over the residues. -/
noncomputable def periodR : ℂ :=
  zeta13 + zeta13 ^ 3 + zeta13 ^ 4 + zeta13 ^ 9 + zeta13 ^ 10 + zeta13 ^ 12

theorem periodR_add_periodN : periodR + periodN = -1 := by
  unfold periodR periodN
  linear_combination zeta13_geom

/-- `(S_R - S_N)² = 13`: the quadratic Gauss sum identity, as an explicit multiple of
`Φ₁₃(ζ) = 0`. -/
theorem periodR_sub_periodN_sq : (periodR - periodN) ^ 2 = 13 := by
  unfold periodR periodN
  linear_combination (zeta13 ^ 12 - 3 * zeta13 ^ 11 + 5 * zeta13 ^ 10 - 3 * zeta13 ^ 9 -
    3 * zeta13 ^ 8 + 5 * zeta13 ^ 7 - 3 * zeta13 ^ 6 - 3 * zeta13 ^ 5 + 5 * zeta13 ^ 4 -
    3 * zeta13 ^ 3 + zeta13 ^ 2 + 13 * zeta13 - 13) * zeta13_geom

theorem zeta13_pow_re (k : ℕ) : (zeta13 ^ k).re = Real.cos (2 * Real.pi * k / 13) := by
  rw [zeta13, ← Complex.exp_nat_mul]
  have h : (k : ℂ) * (2 * Real.pi * Complex.I / 13) =
      ((2 * Real.pi * k / 13 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_re]

/-- The sign determination: `Re S_N < 1`, since
`Re S_N = cos(4π/13) + cos(10π/13) + cos(12π/13) + cos(14π/13) + cos(16π/13) + cos(22π/13)`
with `cos(10π/13), cos(16π/13) < 0` and `cos(12π/13) = cos(14π/13) = -cos(π/13) < -1/2`. -/
theorem periodN_re_lt_one : periodN.re < 1 := by
  unfold periodN
  simp only [Complex.add_re, zeta13_pow_re]
  push_cast
  have hπ := Real.pi_pos
  have c2 : Real.cos (2 * Real.pi * 2 / 13) ≤ 1 := Real.cos_le_one _
  have c11 : Real.cos (2 * Real.pi * 11 / 13) ≤ 1 := Real.cos_le_one _
  have c5 : Real.cos (2 * Real.pi * 5 / 13) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
  have c8 : Real.cos (2 * Real.pi * 8 / 13) < 0 :=
    Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
  have hc : 1 / 2 < Real.cos (Real.pi / 13) := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  have c6 : Real.cos (2 * Real.pi * 6 / 13) = -Real.cos (Real.pi / 13) := by
    rw [← Real.cos_pi_sub]
    congr 1
    ring
  have c7 : Real.cos (2 * Real.pi * 7 / 13) = -Real.cos (Real.pi / 13) := by
    rw [← Real.cos_add_pi]
    congr 1
    ring
  linarith

/-- (b) **The nonresidue Gauss period**: `∑_{n ∈ N} ζⁿ = (-1 - √13)/2`. -/
theorem periodN_eq : periodN = (-1 - (Real.sqrt 13 : ℂ)) / 2 := by
  have hs : ((Real.sqrt 13 : ℝ) : ℂ) ^ 2 = 13 := by
    exact_mod_cast Real.sq_sqrt (show (0 : ℝ) ≤ 13 by norm_num)
  have hsq := periodR_sub_periodN_sq
  have hsum := periodR_add_periodN
  have hprod : (periodR - periodN - Real.sqrt 13) * (periodR - periodN + Real.sqrt 13) = 0 := by
    linear_combination hsq - hs
  rcases mul_eq_zero.mp hprod with h | h
  · linear_combination (1 / 2) * hsum - (1 / 2) * h
  · exfalso
    have hN : periodN = (((-1 + Real.sqrt 13) / 2 : ℝ) : ℂ) := by
      push_cast
      linear_combination (1 / 2) * hsum - (1 / 2) * h
    have hre : periodN.re = (-1 + Real.sqrt 13) / 2 := by
      rw [hN, Complex.ofReal_re]
    have h3 : 3 < Real.sqrt 13 := by
      rw [Real.lt_sqrt (by norm_num)]
      norm_num
    have := periodN_re_lt_one
    linarith

/-- (b) **The residue Gauss period**: `∑_{n ∈ R} ζⁿ = (-1 + √13)/2`. -/
theorem periodR_eq : periodR = (-1 + (Real.sqrt 13 : ℂ)) / 2 := by
  linear_combination periodR_add_periodN - periodN_eq

theorem sum_nonresidues13_eq : ∑ e ∈ nonresidues13, zeta13 ^ e = (-1 - (Real.sqrt 13 : ℂ)) / 2 := by
  rw [sum_nonresidues13, ← periodN_eq]
  rfl

/-- (c) The squared nonresidue roots are the residue roots: `∑_{n∈N} ζ²ⁿ = S_R`. -/
theorem sum_sq_nonresidues13 : ∑ e ∈ nonresidues13, (zeta13 ^ e) ^ 2 = periodR := by
  rw [sum_nonresidues13]
  unfold periodR
  linear_combination (zeta13 + zeta13 ^ 3 + zeta13 ^ 9) * zeta13_pow_thirteen

theorem sum_sq_nonresidues13_eq :
    ∑ e ∈ nonresidues13, (zeta13 ^ e) ^ 2 = (-1 + (Real.sqrt 13 : ℂ)) / 2 := by
  rw [sum_sq_nonresidues13, periodR_eq]

/-! ### (a) Linear independence -/

/-- (a) The six nonresidue thirteenth roots are linearly independent over `ℚ`: a rational
relation gives a polynomial of degree at most `11` vanishing at `ζ`, which is divisible by
`Φ₁₃` (degree `12`) and hence zero. -/
theorem nonresidue_linear_independent (c₂ c₅ c₆ c₇ c₈ c₁₁ : ℚ)
    (h : (c₂ : ℂ) * zeta13 ^ 2 + (c₅ : ℂ) * zeta13 ^ 5 + (c₆ : ℂ) * zeta13 ^ 6 +
      (c₇ : ℂ) * zeta13 ^ 7 + (c₈ : ℂ) * zeta13 ^ 8 + (c₁₁ : ℂ) * zeta13 ^ 11 = 0) :
    c₂ = 0 ∧ c₅ = 0 ∧ c₆ = 0 ∧ c₇ = 0 ∧ c₈ = 0 ∧ c₁₁ = 0 := by
  let P : ℚ[X] := C c₂ * X ^ 2 + C c₅ * X ^ 5 + C c₆ * X ^ 6 + C c₇ * X ^ 7 + C c₈ * X ^ 8 +
    C c₁₁ * X ^ 11
  have haeval : aeval zeta13 P = 0 := by
    simp only [P, map_add, map_mul, aeval_C, aeval_X_pow, eq_ratCast]
    exact h
  have hdvd : minpoly ℚ zeta13 ∣ P := minpoly.dvd ℚ zeta13 haeval
  rw [← Polynomial.cyclotomic_eq_minpoly_rat zeta13_isPrimitiveRoot (by norm_num)] at hdvd
  have hdeg : P.natDegree < (cyclotomic 13 ℚ).natDegree := by
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime (by norm_num)]
    have : P.natDegree ≤ 11 := by
      simp only [P]
      compute_degree
    omega
  have hP0 : P = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg
  have hc : ∀ k, P.coeff k = 0 := fun k => by rw [hP0, Polynomial.coeff_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [P, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hc 2
  · simpa [P, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hc 5
  · simpa [P, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hc 6
  · simpa [P, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hc 7
  · simpa [P, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hc 8
  · simpa [P, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hc 11

/-- (a) in Mathlib's language. -/
theorem nonresidue_powers_linearIndependent :
    LinearIndependent ℚ
      ![zeta13 ^ 2, zeta13 ^ 5, zeta13 ^ 6, zeta13 ^ 7, zeta13 ^ 8, zeta13 ^ 11] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  simp [Fin.sum_univ_six, Rat.smul_def] at hg
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := nonresidue_linear_independent _ _ _ _ _ _ hg
  intro i
  fin_cases i <;> assumption

/-! ### Lemma `lem:six-residual-twists` -/

/-- **The Galois-averaging step** of the proof of Lemma `lem:six-residual-twists`
(manuscript lines 4025–4039), stated as a hypothesis: *every root in a multiset of six roots
of unity with sum `(-1-√13)/2` is one of the six nonresidue thirteenth roots.*  The
manuscript proves this by averaging over a cyclotomic Galois group fixing `√13` (as in Lemma
`lem:conductor40`, with the induced quadratic Gauss sum); proved in `ThirteenOrbit.lean`
(`nonresidueOrbitStep`). -/
def NonresidueOrbitStep : Prop :=
  ∀ s : Multiset ℂ, (∀ z ∈ s, IsRootOfUnity z) → Multiset.card s = 6 →
    s.sum = (-1 - (Real.sqrt 13 : ℂ)) / 2 → ∀ z ∈ s, ∃ e ∈ nonresidues13, z = zeta13 ^ e

/-- **Lemma `lem:six-residual-twists`** (manuscript line 4019), given the Galois-averaging
step `NonresidueOrbitStep`.  Input: the data of Lemma `lem:rank6-induction` at `m = 1`
(`Δ = 13`): residual central simples `j : ι` with `F(Z_j) = n_j R`, `n_j > 0`, twists `θ_j`
(roots of unity), `∑ n_j² = 6`, eq:indicator-first and eq:indicator-second.  Output: every
`n_j = 1`, the twists are distinct and are exactly the six nonresidue thirteenth roots, and
`ε = ν₂(ρ) = 1`. -/
theorem six_residual_twists (hOrbit : NonresidueOrbitStep)
    {ι : Type*} [Fintype ι] (n : ι → ℕ) (hn : ∀ j, 0 < n j) (θ : ι → ℂ)
    (hθ : ∀ j, IsRootOfUnity (θ j))
    (hdim : ∑ j, n j ^ 2 = 6)
    (hfirst : ∑ j, (n j : ℂ) ^ 2 * θ j = -((1 : ℂ) + (Real.sqrt 13 : ℂ)) / 2)
    {ε : ℤ} (hsecond : ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 =
      (-1 + (2 * (ε : ℂ) - 1) * (Real.sqrt 13 : ℂ)) / 2) :
    (∀ j, n j = 1) ∧ Function.Injective θ ∧
      (∀ e ∈ nonresidues13, ∃ j, θ j = zeta13 ^ e) ∧ ε = 1 := by
  classical
  have hmem : ∀ j, θ j ∈ rootMultiset n θ := fun j =>
    Multiset.mem_bind.mpr ⟨j, Finset.mem_univ _,
      Multiset.mem_replicate.mpr ⟨(pow_pos (hn j) 2).ne', rfl⟩⟩
  have hsum6 : (rootMultiset n θ).sum = (-1 - (Real.sqrt 13 : ℂ)) / 2 := by
    rw [rootMultiset_sum, hfirst]
    ring
  have hcard6 : Multiset.card (rootMultiset n θ) = 6 := by rw [rootMultiset_card, hdim]
  have horb := hOrbit _ (rootMultiset_roots hθ) hcard6 hsum6
  choose e he hθe using fun j => horb (θ j) (hmem j)
  have he_lt : ∀ j, e j < 13 := by
    intro j
    have h := he j
    simp only [nonresidues13, Finset.mem_insert, Finset.mem_singleton] at h
    omega
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℕ,
      ∀ a, F a = ∑ j ∈ Finset.univ.filter (fun j => e j = a), n j ^ 2 := ⟨_, fun a => rfl⟩
  -- regroup the moments along the fibres of `e`
  have hregroup : ∀ k : ℕ, ∑ j, (n j : ℂ) ^ 2 * θ j ^ k =
      ∑ a ∈ nonresidues13, (F a : ℂ) * (zeta13 ^ a) ^ k := by
    intro k
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := nonresidues13) (g := e)
      (fun j _ => he j)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hF a]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hθe j, (Finset.mem_filter.mp hj).2]
  -- comparison with the quadratic period: every fibre has weight one
  have h1 := hregroup 1
  simp only [pow_one] at h1
  rw [hfirst, sum_nonresidues13] at h1
  have hN := periodN_eq
  unfold periodN at hN
  obtain ⟨l2, l5, l6, l7, l8, l11⟩ := nonresidue_linear_independent ((F 2 : ℚ) - 1)
    ((F 5 : ℚ) - 1) ((F 6 : ℚ) - 1) ((F 7 : ℚ) - 1) ((F 8 : ℚ) - 1) ((F 11 : ℚ) - 1) (by
      push_cast
      linear_combination -h1 - hN)
  have hF1 : ∀ a ∈ nonresidues13, F a = 1 := by
    intro a ha
    simp only [nonresidues13, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · have h' : ((F 2 : ℕ) : ℚ) = 1 := by linarith
      exact_mod_cast h'
    · have h' : ((F 5 : ℕ) : ℚ) = 1 := by linarith
      exact_mod_cast h'
    · have h' : ((F 6 : ℕ) : ℚ) = 1 := by linarith
      exact_mod_cast h'
    · have h' : ((F 7 : ℕ) : ℚ) = 1 := by linarith
      exact_mod_cast h'
    · have h' : ((F 8 : ℕ) : ℚ) = 1 := by linarith
      exact_mod_cast h'
    · have h' : ((F 11 : ℕ) : ℚ) = 1 := by linarith
      exact_mod_cast h'
  -- `n_j = 1`
  have hn1 : ∀ j, n j = 1 := by
    intro j
    have hle : n j ^ 2 ≤ F (e j) := by
      rw [hF (e j)]
      exact Finset.single_le_sum (f := fun i => n i ^ 2) (fun i _ => Nat.zero_le _)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩)
    rw [hF1 (e j) (he j)] at hle
    have hpos := hn j
    have h2 : n j ≤ 1 := by nlinarith
    omega
  -- distinct twists
  have hinj : Function.Injective θ := by
    intro j j' hjj
    have hee : e j = e j' := by
      rw [hθe j, hθe j'] at hjj
      exact zeta13_isPrimitiveRoot.pow_inj (he_lt j) (he_lt j') hjj
    by_contra hne
    have hsub : ({j, j'} : Finset ι) ⊆ Finset.univ.filter (fun i => e i = e j) := by
      intro i hi
      rw [Finset.mem_insert, Finset.mem_singleton] at hi
      rw [Finset.mem_filter]
      rcases hi with rfl | rfl
      · exact ⟨Finset.mem_univ _, rfl⟩
      · exact ⟨Finset.mem_univ _, hee.symm⟩
    have hle : ∑ i ∈ ({j, j'} : Finset ι), n i ^ 2 ≤
        ∑ i ∈ Finset.univ.filter (fun i => e i = e j), n i ^ 2 :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_pair hne, ← hF (e j), hF1 (e j) (he j), hn1 j, hn1 j'] at hle
    norm_num at hle
  -- every nonresidue root occurs
  have hsurj : ∀ a ∈ nonresidues13, ∃ j, θ j = zeta13 ^ a := by
    intro a ha
    have hFa := hF1 a ha
    rw [hF a] at hFa
    have hne : (Finset.univ.filter (fun j => e j = a)).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty] at hFa
      exact absurd hFa (by norm_num)
    obtain ⟨j, hj⟩ := hne
    exact ⟨j, by rw [hθe j, (Finset.mem_filter.mp hj).2]⟩
  -- `ε = 1`: the squared twists are the residue roots
  have h2 := hregroup 2
  have hsq : ∑ a ∈ nonresidues13, (F a : ℂ) * (zeta13 ^ a) ^ 2 =
      ∑ a ∈ nonresidues13, (zeta13 ^ a) ^ 2 := by
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [hF1 a ha]
    simp
  rw [hsecond, hsq, sum_sq_nonresidues13_eq] at h2
  have hreal : (((2 * (ε : ℝ) - 2) * Real.sqrt 13 : ℝ) : ℂ) = 0 := by
    push_cast
    linear_combination 2 * h2
  have hreal' : (2 * (ε : ℝ) - 2) * Real.sqrt 13 = 0 := by exact_mod_cast hreal
  have hs13 : Real.sqrt 13 ≠ 0 := by positivity
  have hε : (ε : ℝ) = 1 := by
    rcases mul_eq_zero.mp hreal' with h | h
    · linarith
    · exact absurd h hs13
  exact ⟨hn1, hinj, hsurj, by exact_mod_cast hε⟩

/-- `ε = ν₂(ρ) = 1` from Larson's Theorem 1.3 alone, without `NonresidueOrbitStep`: if
`ε = -1`, eq:indicator-second at `m = 1` makes the twelve squared roots of two copies sum to
`-1 - 3√13`, which needs at least `3 φ(26) = 36` roots. -/
theorem epsilon_eq_one_of_larson (hLarson : LarsonRootCount) (s : Multiset ℂ)
    (hroots : ∀ z ∈ s, IsRootOfUnity z) (hcard : Multiset.card s = 6)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hsecond : (s.map (fun z => z ^ 2)).sum =
      (-1 + (2 * (ε : ℂ) - 1) * (Real.sqrt 13 : ℂ)) / 2) :
    ε = 1 := by
  rcases hε with h | h
  · exact h
  · exfalso
    subst h
    have hroots2 : ∀ z ∈ s.map (fun z => z ^ 2) + s.map (fun z => z ^ 2), IsRootOfUnity z := by
      intro z hz
      have hz' : z ∈ s.map (fun z => z ^ 2) := by
        rcases Multiset.mem_add.mp hz with h | h
        · exact h
        · exact h
      obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hz'
      obtain ⟨k, hk, hwk⟩ := hroots w hw
      refine ⟨k, hk, ?_⟩
      show (w ^ 2) ^ k = 1
      rw [← pow_mul, mul_comm, pow_mul, hwk, one_pow]
    have hsum : (s.map (fun z => z ^ 2) + s.map (fun z => z ^ 2)).sum =
        ((-1 : ℤ) : ℂ) + ((-3 : ℤ) : ℂ) * (Real.sqrt ((13 : ℕ) : ℝ) : ℂ) := by
      rw [Multiset.sum_add, hsecond]
      push_cast
      ring
    have h13 : Squarefree 13 := (Nat.prime_iff.mp (by norm_num)).squarefree
    have hL := hLarson 13 h13 (by norm_num) _ _ _ hroots2 hsum
    have hφ : Nat.totient (2 * 13) = 12 := by
      rw [Nat.totient_two_mul_of_odd ⟨6, by norm_num⟩, Nat.totient_prime (by norm_num)]
    rw [hφ, Multiset.card_add, Multiset.card_map, hcard] at hL
    norm_num at hL

/-! ### Assembly: `m = 1`, the Haagerup dimensions and the six twists -/

/-- eq:haagerup-dimensions (manuscript lines 4013–4017): at `m = 1`, `d = (3+√13)/2`,
`s = 1 + d² = (13+3√13)/2` and `d_X = d² = (11+3√13)/2`. -/
theorem haagerup_dimensions :
    (3 * (1 : ℝ) + Real.sqrt (9 * 1 ^ 2 + 4)) / 2 = (3 + Real.sqrt 13) / 2 ∧
    1 + ((3 + Real.sqrt 13) / 2) ^ 2 = (13 + 3 * Real.sqrt 13) / 2 ∧
    ((3 + Real.sqrt 13) / 2) ^ 2 = (11 + 3 * Real.sqrt 13) / 2 := by
  have h13 : Real.sqrt 13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  refine ⟨by norm_num, ?_, ?_⟩
  · linear_combination (1 / 4) * h13
  · linear_combination (1 / 4) * h13

/-- **Multiplicity one and the six residual twists, assembled** (manuscript lines 3926–4051).
From the data of Lemma `lem:rank6-induction` for an arbitrary `m ≥ 1`: Larson's Theorem 1.3
(`LarsonRootCount`, external), Lemma `lem:conductor40` (`Conductor40Bound`) and the
Galois-averaging step of Lemma `lem:six-residual-twists` (`NonresidueOrbitStep`) give `m = 1`,
all `n_j = 1`, the twists are exactly the six nonresidue thirteenth roots, each once, and
`ε = ν₂(ρ) = 1`. -/
theorem rank6_multiplicity_one_and_twists (hLarson : LarsonRootCount)
    (hC40 : Conductor40Bound) (hOrbit : NonresidueOrbitStep)
    {m : ℕ} (hm : 1 ≤ m) {ι : Type*} [Fintype ι] (n : ι → ℕ) (hn : ∀ j, 0 < n j)
    (θ : ι → ℂ) (hθ : ∀ j, IsRootOfUnity (θ j))
    (hdim : ∑ j, n j ^ 2 = 4 * m ^ 2 + 2)
    (hfirst : ∑ j, (n j : ℂ) ^ 2 * θ j =
      -((m : ℂ) ^ 2 + (m : ℂ) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hsecond : ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 =
      (-(m : ℂ) ^ 2 + (2 * (ε : ℂ) - m) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2) :
    m = 1 ∧ (∀ j, n j = 1) ∧ Function.Injective θ ∧
      (∀ e ∈ nonresidues13, ∃ j, θ j = zeta13 ^ e) ∧ ε = 1 := by
  have hm1 := multiplicity_eq_one_of_family hLarson hC40 hm n θ hθ hdim hfirst hε hsecond
  subst hm1
  have hdim' : ∑ j, n j ^ 2 = 6 := by omega
  have hfirst' : ∑ j, (n j : ℂ) ^ 2 * θ j = -((1 : ℂ) + (Real.sqrt 13 : ℂ)) / 2 := by
    rw [hfirst]
    norm_num
  have hsecond' : ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 =
      (-1 + (2 * (ε : ℂ) - 1) * (Real.sqrt 13 : ℂ)) / 2 := by
    rw [hsecond]
    norm_num
  exact ⟨rfl, six_residual_twists hOrbit n hn θ hθ hdim' hfirst' hsecond'⟩

#print axioms periodN_eq
#print axioms periodR_eq
#print axioms sum_sq_nonresidues13_eq
#print axioms nonresidue_linear_independent
#print axioms nonresidue_powers_linearIndependent
#print axioms two_mul_nonresidues13
#print axioms six_residual_twists
#print axioms epsilon_eq_one_of_larson
#print axioms haagerup_dimensions
#print axioms rank6_multiplicity_one_and_twists

end HaagerupIzumi.C8.NumberTheory
