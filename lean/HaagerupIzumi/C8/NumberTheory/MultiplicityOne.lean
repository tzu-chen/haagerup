module

public import HaagerupIzumi.C8.NumberTheory.Squareclass
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Multiplicity one in the rank-six ring (Appendix G, lines 3926–4007)

For the rank-six fusion ring `a³ = 1`, `ρa = a²ρ`, `ρ² = 1 + m(ρ + aρ + a²ρ)` (eq:rank6-ring),
Lemma `lem:rank6-induction` (lines 3834–3854) produces a multiset of `4m² + 2` roots of unity (the
residual twists `θ_j`, each repeated `n_j²` times) with
* eq:indicator-first:  `∑ θ = -(m² + m√Δ)/2`,
* eq:indicator-second: `∑ θ² = (-m² + (2ε - m)√Δ)/2`, `ε ∈ {1, -1}`,
where `Δ = 9m² + 4`.  The main theorem `multiplicity_eq_one` deduces `m = 1`
(manuscript lines 3926–4004).

## Hypotheses of the theorems in this file (both proved elsewhere)

* `LarsonRootCount` — H. Larson, arXiv:1401.1879, Theorem 1.3 (= Theorem 6.2), for squarefree
  `c > 1`.  Proved in `NumberTheory/LarsonProof.lean` (`larsonRootCount`).
* `Conductor40Bound` — **the manuscript's own Lemma `lem:conductor40`** (lines 3950–3995), stated
  exactly.  Proved in `NumberTheory/Conductor40Proof.lean` (`conductor40Bound`, Galois averaging
  in `NumberTheory/GaloisAverage.lean`).
  The unconditional statements are `multiplicity_eq_one_unconditional`,
  `multiplicity_eq_one_of_family_unconditional` (`LarsonProof.lean`).
* The data of Lemma `lem:rank6-induction` (the root multiset, its cardinality and the two
  moments) enter as hypotheses of `multiplicity_eq_one` / `multiplicity_eq_one_of_family`.
  No hypothesis mentions `m = 1`.

## Proved here

* `multiplicity_identity`: `36m²(9m²+4) − 13(4m²+2)² = 4(m²−1)(29m²+13)`;
* `le_one_of_root_count`: the `D ≠ 10` contradiction for `m > 1`
  (with eq:squareclass-bound from `Squareclass.lean`);
* the `D = 10` analysis: `m, t` even, `m ≥ 4` impossible since `t/m > 15/16`, and the
  equality case `m = t = 2` contradicted by eq:indicator-second;
* `multiplicity_eq_one`, `multiplicity_eq_one_of_family`.
-/

namespace HaagerupIzumi.C8.NumberTheory

/-- `z` is a root of unity. -/
def IsRootOfUnity (z : ℂ) : Prop := ∃ k : ℕ, 0 < k ∧ z ^ k = 1

/-- **Larson, Theorem 1.3** (arXiv:1401.1879, Theorem 1.3 = Theorem 6.2): *if `a, b, c ∈ ℤ`,
`c` squarefree, and `a + b√c` is a sum of `n` roots of unity, then `n ≥ |b| φ(2c)`.*
Larson's proof sums Galois orbits over `ℚ(√c)`, i.e. it treats irrational `√c`; the printed
statement is literally false for `c = 1` (e.g. `1 = 3 - 2√1` is one root of unity; Larson prints
"`c` nonnegative and squarefree").  We state it for squarefree `c > 1`, the only case used
(manuscript line 3936), in the wording of Theorem 6.2 ("at least `|b| φ(2c)` roots").  Proved in
`NumberTheory/LarsonProof.lean` (`larsonRootCount`). -/
def LarsonRootCount : Prop :=
  ∀ (c : ℕ), Squarefree c → 1 < c → ∀ (a b : ℤ) (s : Multiset ℂ),
    (∀ z ∈ s, IsRootOfUnity z) →
    s.sum = (a : ℂ) + (b : ℂ) * (Real.sqrt c : ℂ) →
    |b| * (Nat.totient (2 * c) : ℤ) ≤ (Multiset.card s : ℤ)

/-- **Lemma `lem:conductor40`** (manuscript lines 3950–3955; proof to 3995): *if a multiset of `N` roots of unity
has sum `-a - b√10` with `a, b ∈ ℤ_{≥0}`, then `N ≥ a + 8b`; if equality holds and the sum of
the squared roots lies in `ℚ(√10)`, that second sum is `a`.*  This is the manuscript's own
lemma; it is a hypothesis of the theorems here and is proved in `Conductor40Proof.lean`
(`conductor40Bound`). -/
def Conductor40Bound : Prop :=
  ∀ (a b : ℕ) (s : Multiset ℂ), (∀ z ∈ s, IsRootOfUnity z) →
    s.sum = -(a : ℂ) - (b : ℂ) * (Real.sqrt 10 : ℂ) →
    a + 8 * b ≤ Multiset.card s ∧
      (Multiset.card s = a + 8 * b →
        (∃ x y : ℚ, (s.map (fun z => z ^ 2)).sum = (x : ℂ) + (y : ℂ) * (Real.sqrt 10 : ℂ)) →
        (s.map (fun z => z ^ 2)).sum = (a : ℂ))

/-- The polynomial identity of manuscript line 3945. -/
theorem multiplicity_identity (m : ℤ) :
    36 * m ^ 2 * (9 * m ^ 2 + 4) - 13 * (4 * m ^ 2 + 2) ^ 2 =
      4 * (m ^ 2 - 1) * (29 * m ^ 2 + 13) := by
  ring

theorem multiplicity_ineq {m : ℕ} (hm : 1 < m) :
    13 * (4 * m ^ 2 + 2) ^ 2 < 36 * m ^ 2 * (9 * m ^ 2 + 4) := by
  have h := multiplicity_identity (m : ℤ)
  have hm2 : (2 : ℤ) ≤ m := by exact_mod_cast hm
  have h1 : (0 : ℤ) < (m : ℤ) ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℤ) < 29 * (m : ℤ) ^ 2 + 13 := by positivity
  have h3 := mul_pos (mul_pos (by norm_num : (0 : ℤ) < 4) h1) h2
  have h4 : (13 * (4 * (m : ℤ) ^ 2 + 2) ^ 2 : ℤ) < 36 * (m : ℤ) ^ 2 * (9 * (m : ℤ) ^ 2 + 4) := by
    linarith
  exact_mod_cast h4

/-- **The case `D ≠ 10`** (manuscript lines 3936–3946).  If `9m² + 4 = t²D`,
`144 D ≤ 13 f²` (eq:squareclass-bound with `f = φ(2D)`) and `m t f ≤ 2(4m² + 2)` (Larson's
bound for two copies of the root multiset), then `m ≤ 1`. -/
theorem le_one_of_root_count {m t D f : ℕ} (hΔ : t ^ 2 * D = 9 * m ^ 2 + 4)
    (hsq : 144 * D ≤ 13 * f ^ 2) (hcount : m * t * f ≤ 2 * (4 * m ^ 2 + 2)) : m ≤ 1 := by
  by_contra hm
  push Not at hm
  have hsq' : (m * t * f) ^ 2 ≤ (2 * (4 * m ^ 2 + 2)) ^ 2 := Nat.pow_le_pow_left hcount 2
  have key : 144 * m ^ 2 * (9 * m ^ 2 + 4) ≤ 13 * (2 * (4 * m ^ 2 + 2)) ^ 2 := by
    calc 144 * m ^ 2 * (9 * m ^ 2 + 4) = 144 * D * (m * t) ^ 2 := by rw [← hΔ]; ring
      _ ≤ 13 * f ^ 2 * (m * t) ^ 2 := Nat.mul_le_mul hsq le_rfl
      _ = 13 * (m * t * f) ^ 2 := by ring
      _ ≤ 13 * (2 * (4 * m ^ 2 + 2)) ^ 2 := Nat.mul_le_mul le_rfl hsq'
  have hlt := multiplicity_ineq hm
  have e1 : 13 * (2 * (4 * m ^ 2 + 2)) ^ 2 = 4 * (13 * (4 * m ^ 2 + 2) ^ 2) := by ring
  have e2 : 144 * m ^ 2 * (9 * m ^ 2 + 4) = 4 * (36 * m ^ 2 * (9 * m ^ 2 + 4)) := by ring
  rw [e1, e2] at key
  omega

/-- **Multiplicity one** (manuscript lines 3926–4004).  Let `m ≥ 1` and let `s` be a multiset
of `4m² + 2` roots of unity satisfying eq:indicator-first and eq:indicator-second (with
`ε = ±1`).  Assuming Larson's Theorem 1.3 and Lemma `lem:conductor40`, `m = 1`. -/
theorem multiplicity_eq_one (hLarson : LarsonRootCount) (hC40 : Conductor40Bound)
    {m : ℕ} (hm : 1 ≤ m) (s : Multiset ℂ) (hroots : ∀ z ∈ s, IsRootOfUnity z)
    (hcard : Multiset.card s = 4 * m ^ 2 + 2)
    (hfirst : s.sum = -((m : ℂ) ^ 2 + (m : ℂ) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hsecond : (s.map (fun z => z ^ 2)).sum =
      (-(m : ℂ) ^ 2 + (2 * (ε : ℂ) - m) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2) :
    m = 1 := by
  obtain ⟨D, t, hD0, ht0, hDt, hsf⟩ :=
    Nat.sq_mul_squarefree_of_pos (show 0 < 9 * m ^ 2 + 4 by positivity)
  obtain ⟨hD1, hD3, hD7⟩ := squareclass_props hm hDt
  have hΔ : (9 * (m : ℝ) ^ 2 + 4) = (t : ℝ) ^ 2 * (D : ℝ) := by exact_mod_cast hDt.symm
  have hsqrt : Real.sqrt (9 * (m : ℝ) ^ 2 + 4) = (t : ℝ) * Real.sqrt D := by
    rw [hΔ, Real.sqrt_mul (show (0 : ℝ) ≤ (t : ℝ) ^ 2 by positivity) (D : ℝ),
      Real.sqrt_sq (show (0 : ℝ) ≤ (t : ℝ) by positivity)]
  by_cases h10 : D = 10
  · -- The exceptional squareclass `D = 10` (manuscript lines 3997–4006).
    exfalso
    subst h10
    obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k := by
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' m
      · exact ⟨k, hk⟩
      · exfalso
        subst hk
        ring_nf at hDt
        omega
    obtain ⟨l, rfl⟩ : ∃ l, t = 2 * l := by
      obtain ⟨l, hl | hl⟩ := Nat.even_or_odd' t
      · exact ⟨l, hl⟩
      · exfalso
        subst hl
        ring_nf at hDt
        omega
    have hkl : 10 * l ^ 2 = 9 * k ^ 2 + 1 := by
      have h' := hDt
      ring_nf at h'
      omega
    have hk1 : 1 ≤ k := by omega
    -- `a = m²/2 = 2k²`, `b = mt/2 = 2kl`
    have hsum40 : s.sum = -((2 * k ^ 2 : ℕ) : ℂ) - ((2 * k * l : ℕ) : ℂ) * (Real.sqrt 10 : ℂ) := by
      rw [hfirst, hsqrt]
      push_cast
      ring
    obtain ⟨hineq, heq⟩ := hC40 (2 * k ^ 2) (2 * k * l) s hroots hsum40
    rw [hcard] at hineq heq
    -- `t/m > 15/16`
    have h1516 : 15 * k + 1 ≤ 16 * l := by
      by_contra h
      push Not at h
      have h' : 16 * l * (16 * l) ≤ 15 * k * (15 * k) := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    -- `m ≥ 4` is impossible, so `m = 2`
    have hk2 : k ≤ 1 := by nlinarith [Nat.mul_le_mul_left k h1516]
    obtain rfl : k = 1 := by omega
    have hl1 : l = 1 := by nlinarith
    subst hl1
    -- the equality case `m = t = 2`: the squared sum must be `a = 2`
    have hsq := heq (by norm_num) ⟨-2, 2 * (ε : ℚ) - 2, by
      rw [hsecond, hsqrt]
      push_cast
      ring⟩
    have e : ((-2 + (2 * (ε : ℝ) - 2) * Real.sqrt 10 : ℝ) : ℂ) =
        (s.map (fun z => z ^ 2)).sum := by
      rw [hsecond, hsqrt]
      push_cast
      ring
    rw [hsq] at e
    have e' : (-2 + (2 * (ε : ℝ) - 2) * Real.sqrt 10 : ℝ) = 2 := by exact_mod_cast e
    rcases hε with rfl | rfl
    · push_cast at e'
      linarith
    · push_cast at e'
      nlinarith [Real.sqrt_nonneg 10]
  · -- `D ≠ 10`: Larson's Theorem 1.3 on two copies of the multiset.
    have hroots2 : ∀ z ∈ s + s, IsRootOfUnity z := by
      intro z hz
      rcases Multiset.mem_add.mp hz with h | h
      · exact hroots z h
      · exact hroots z h
    have hsum2 : (s + s).sum =
        ((-((m : ℤ) ^ 2) : ℤ) : ℂ) + ((-((m : ℤ) * t) : ℤ) : ℂ) * (Real.sqrt D : ℂ) := by
      rw [Multiset.sum_add, hfirst, hsqrt]
      push_cast
      ring
    have hL := hLarson D hsf hD1 _ _ (s + s) hroots2 hsum2
    rw [Multiset.card_add, hcard, abs_neg,
      abs_of_nonneg (show (0 : ℤ) ≤ (m : ℤ) * t by positivity)] at hL
    push_cast at hL
    have hcount : m * t * Nat.totient (2 * D) ≤ 2 * (4 * m ^ 2 + 2) := by
      have h' : ((m * t * Nat.totient (2 * D) : ℕ) : ℤ) ≤ ((2 * (4 * m ^ 2 + 2) : ℕ) : ℤ) := by
        push_cast
        linarith
      exact_mod_cast h'
    have := le_one_of_root_count hDt (squareclass_bound_nat hsf hD1 hD3 hD7 h10) hcount
    omega

/-- The root multiset of Lemma `lem:rank6-induction`: each twist `θ j` repeated `n j ^ 2`
times. -/
noncomputable def rootMultiset {ι : Type*} [Fintype ι] (n : ι → ℕ) (θ : ι → ℂ) : Multiset ℂ :=
  (Finset.univ : Finset ι).val.bind fun j => Multiset.replicate (n j ^ 2) (θ j)

theorem rootMultiset_card {ι : Type*} [Fintype ι] (n : ι → ℕ) (θ : ι → ℂ) :
    Multiset.card (rootMultiset n θ) = ∑ j, n j ^ 2 := by
  simp [rootMultiset, Multiset.card_bind]

theorem rootMultiset_sum {ι : Type*} [Fintype ι] (n : ι → ℕ) (θ : ι → ℂ) :
    (rootMultiset n θ).sum = ∑ j, (n j : ℂ) ^ 2 * θ j := by
  simp [rootMultiset]

theorem rootMultiset_sum_sq {ι : Type*} [Fintype ι] (n : ι → ℕ) (θ : ι → ℂ) :
    ((rootMultiset n θ).map (fun z => z ^ 2)).sum = ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 := by
  simp [rootMultiset, Multiset.map_bind]

theorem rootMultiset_roots {ι : Type*} [Fintype ι] {n : ι → ℕ} {θ : ι → ℂ}
    (hθ : ∀ j, IsRootOfUnity (θ j)) : ∀ z ∈ rootMultiset n θ, IsRootOfUnity z := by
  intro z hz
  obtain ⟨j, -, hj⟩ := Multiset.mem_bind.mp hz
  rw [Multiset.eq_of_mem_replicate hj]
  exact hθ j

/-- **Multiplicity one, in the notation of Lemma `lem:rank6-induction`** (manuscript lines
3834–3854 and 3926–4004): residual central simples `Z_j` with `F(Z_j) = n_j R`, twists `θ_j`
(roots of unity), `∑ n_j² = 4m² + 2` and the two indicator moments eq:indicator-first and
eq:indicator-second.  Assuming Larson's Theorem 1.3 and Lemma `lem:conductor40`, `m = 1`. -/
theorem multiplicity_eq_one_of_family (hLarson : LarsonRootCount) (hC40 : Conductor40Bound)
    {m : ℕ} (hm : 1 ≤ m) {ι : Type*} [Fintype ι] (n : ι → ℕ) (θ : ι → ℂ)
    (hθ : ∀ j, IsRootOfUnity (θ j))
    (hdim : ∑ j, n j ^ 2 = 4 * m ^ 2 + 2)
    (hfirst : ∑ j, (n j : ℂ) ^ 2 * θ j =
      -((m : ℂ) ^ 2 + (m : ℂ) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2)
    {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hsecond : ∑ j, (n j : ℂ) ^ 2 * θ j ^ 2 =
      (-(m : ℂ) ^ 2 + (2 * (ε : ℂ) - m) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2) :
    m = 1 :=
  multiplicity_eq_one hLarson hC40 hm (rootMultiset n θ) (rootMultiset_roots hθ)
    (by rw [rootMultiset_card, hdim]) (by rw [rootMultiset_sum, hfirst]) hε
    (by rw [rootMultiset_sum_sq, hsecond])

#print axioms le_one_of_root_count
#print axioms multiplicity_eq_one
#print axioms multiplicity_eq_one_of_family

end HaagerupIzumi.C8.NumberTheory
