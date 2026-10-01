module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The squareclass of `Δ = 9m² + 4` (Appendix G, lines 3926–3946)

For the rank-six fusion ring `ρ² = 1 + m(ρ + aρ + a²ρ)` (eq:rank6-ring) the manuscript
puts `Δ = 9m² + 4` and writes `Δ = t²D` with `D` squarefree.  This file proves:

* `sq_lt_delta`, `delta_lt_sq`, `delta_not_square`: `(3m)² < Δ < (3m+1)²` for `m ≥ 1`,
  so `Δ` is not a square;
* `delta_mod_three`, `seven_not_dvd_delta`: `Δ ≡ 1 (mod 3)` and `7 ∤ Δ`
  (`m² ≡ 5 (mod 7)` has no solution);
* `squareclass_props`: if `Δ = t²D` then `D > 1`, `D ≡ 1 (mod 3)` and `7 ∤ D`;
* `squareclass_bound_nat`, `squareclass_bound`: the bound eq:squareclass-bound,
  `φ(2D)/√D ≥ 12/√13`, equivalently `144 D ≤ 13 φ(2D)²`, for every squarefree `D > 1`
  with `D ≡ 1 (mod 3)`, `7 ∤ D` and `D ≠ 10`;
* `squareclass_of_delta`: the combination used in the manuscript.

Everything here is elementary: there are no hypotheses beyond those displayed.
-/

namespace HaagerupIzumi.C8.NumberTheory

/-! ### `Δ = 9m² + 4` is not a square, `Δ ≡ 1 (mod 3)`, `7 ∤ Δ` -/

theorem sq_lt_delta (m : ℕ) : (3 * m) ^ 2 < 9 * m ^ 2 + 4 := by
  have h : (3 * m) ^ 2 = 9 * m ^ 2 := by ring
  omega

theorem delta_lt_sq {m : ℕ} (hm : 1 ≤ m) : 9 * m ^ 2 + 4 < (3 * m + 1) ^ 2 := by
  have h : (3 * m + 1) ^ 2 = 9 * m ^ 2 + 6 * m + 1 := by ring
  omega

/-- `Δ = 9m² + 4` is not a perfect square for `m ≥ 1`. -/
theorem delta_not_square {m : ℕ} (hm : 1 ≤ m) (k : ℕ) : k ^ 2 ≠ 9 * m ^ 2 + 4 := by
  intro hk
  have h1 : 3 * m < k := by
    by_contra h
    push Not at h
    have h' := Nat.pow_le_pow_left h 2
    have h'' := sq_lt_delta m
    omega
  have h2 : k < 3 * m + 1 := by
    by_contra h
    push Not at h
    have h' := Nat.pow_le_pow_left h 2
    have h'' := delta_lt_sq hm
    omega
  omega

theorem delta_mod_three (m : ℕ) : (9 * m ^ 2 + 4) % 3 = 1 := by
  omega

/-- `7 ∤ 9m² + 4`: otherwise `m² ≡ 5 (mod 7)`, which has no solution. -/
theorem seven_not_dvd_delta (m : ℕ) : ¬ 7 ∣ 9 * m ^ 2 + 4 := by
  intro h
  have h0 : ((9 * m ^ 2 + 4 : ℕ) : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h0
  have key : ∀ x : ZMod 7, 9 * x ^ 2 + 4 ≠ 0 := by decide
  exact key _ h0

/-- If `9m² + 4 = t² D` with `m ≥ 1`, then `D > 1`, `D ≡ 1 (mod 3)` and `7 ∤ D`
(manuscript lines 3926–3929). -/
theorem squareclass_props {m t D : ℕ} (hm : 1 ≤ m) (hΔ : t ^ 2 * D = 9 * m ^ 2 + 4) :
    1 < D ∧ D % 3 = 1 ∧ ¬ 7 ∣ D := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    push Not at h
    interval_cases D
    · omega
    · exact delta_not_square hm t (by omega)
  · have hcast : (t : ZMod 3) ^ 2 * (D : ZMod 3) = 9 * (m : ZMod 3) ^ 2 + 4 := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod 3) hΔ
    have key : ∀ x y z : ZMod 3, x ^ 2 * y = 9 * z ^ 2 + 4 → y = 1 := by decide
    have hD : (D : ZMod 3) = 1 := key _ _ _ hcast
    have hval := ZMod.val_natCast 3 D
    rw [hD] at hval
    have h1 : (1 : ZMod 3).val = 1 := rfl
    omega
  · intro h7
    have h7' : 7 ∣ t ^ 2 * D := Dvd.dvd.mul_left h7 _
    rw [hΔ] at h7'
    exact seven_not_dvd_delta m h7'

/-! ### The totient bound -/

/-- For squarefree `n`, `φ n = ∏_{p ∣ n} (p - 1)`. -/
theorem totient_eq_prod_of_squarefree {n : ℕ} (hn : Squarefree n) :
    Nat.totient n = ∏ p ∈ n.primeFactors, (p - 1) := by
  have h := Nat.totient_mul_prod_primeFactors n
  rw [Nat.prod_primeFactors_of_squarefree hn, mul_comm (Nat.totient n) n] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn.ne_zero) h

/-- A squarefree `n > 1` that is not prime has at least two prime factors. -/
theorem one_lt_card_primeFactors {n : ℕ} (hn : Squarefree n) (h1 : 1 < n) (hnp : ¬ n.Prime) :
    1 < n.primeFactors.card := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr h1
  by_contra h
  push Not at h
  have hc : n.primeFactors.card = 1 := le_antisymm h (Finset.card_pos.mpr hne)
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  have hpmem : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
  have hprod := Nat.prod_primeFactors_of_squarefree hn
  rw [hp, Finset.prod_singleton] at hprod
  apply hnp
  rw [← hprod]
  exact Nat.prime_of_mem_primeFactors hpmem

/-- Two distinct primes `p, q ≥ 5`: `(p-1)²(q-1)²/(pq) ≥ (16/5)(25/6) > 144/13`. -/
theorem two_prime_bound {p q : ℕ} (hp : 5 ≤ p) (hq : 5 ≤ q) (hpq : p ≠ q) :
    144 * (p * q) ≤ 13 * ((p - 1) ^ 2 * (q - 1) ^ 2) := by
  have key : ∀ a b : ℕ, 5 ≤ a → 6 ≤ b → 144 * (a * b) ≤ 13 * ((a - 1) ^ 2 * (b - 1) ^ 2) := by
    intro a b ha hb
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le ha
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hb
    have e1 : 5 + x - 1 = x + 4 := by omega
    have e2 : 6 + y - 1 = y + 5 := by omega
    rw [e1, e2]
    have e3 : 13 * ((x + 4) ^ 2 * (y + 5) ^ 2) = 144 * ((5 + x) * (6 + y)) +
        (13 * x ^ 2 * y ^ 2 + 130 * x ^ 2 * y + 325 * x ^ 2 + 104 * x * y ^ 2 + 896 * x * y +
          1736 * x + 208 * y ^ 2 + 1360 * y + 880) := by ring
    rw [e3]
    exact Nat.le_add_right _ _
  rcases Nat.lt_or_gt_of_ne hpq with h | h
  · exact key p q hp (by omega)
  · have h' := key q p hq (by omega)
    calc 144 * (p * q) = 144 * (q * p) := by ring
      _ ≤ 13 * ((q - 1) ^ 2 * (p - 1) ^ 2) := h'
      _ = 13 * ((p - 1) ^ 2 * (q - 1) ^ 2) := by ring

/-- A squarefree `n` with at least two prime factors, all `≥ 5`, has `144 n ≤ 13 φ(n)²`:
two of the factors `(p-1)²/p` already give more than `144/13`, and every further factor
`(r-1)²/r` exceeds one. -/
theorem two_factor_bound {n : ℕ} (hn : Squarefree n) (h5 : ∀ p ∈ n.primeFactors, 5 ≤ p)
    (hcard : 1 < n.primeFactors.card) : 144 * n ≤ 13 * Nat.totient n ^ 2 := by
  classical
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hcard
  have hq' : q ∈ n.primeFactors.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hq⟩
  have split : ∀ f : ℕ → ℕ, ∏ x ∈ n.primeFactors, f x =
      f p * (f q * ∏ x ∈ (n.primeFactors.erase p).erase q, f x) := by
    intro f
    rw [Finset.mul_prod_erase _ f hq', Finset.mul_prod_erase _ f hp]
  have hR : ∏ x ∈ (n.primeFactors.erase p).erase q, x ≤
      ∏ x ∈ (n.primeFactors.erase p).erase q, (x - 1) ^ 2 := by
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro x hx
    have hx5 := h5 x (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx))
    obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hx5
    have e : 5 + y - 1 = y + 4 := by omega
    rw [e]
    nlinarith
  have hφ : Nat.totient n ^ 2 = ∏ x ∈ n.primeFactors, (x - 1) ^ 2 := by
    rw [totient_eq_prod_of_squarefree hn, Finset.prod_pow]
  have hn' : n = ∏ x ∈ n.primeFactors, x := (Nat.prod_primeFactors_of_squarefree hn).symm
  have h2 := two_prime_bound (h5 p hp) (h5 q hq) hpq
  have sA := split (fun x => x)
  have sB := split (fun x => (x - 1) ^ 2)
  calc 144 * n = 144 * (p * q) * ∏ x ∈ (n.primeFactors.erase p).erase q, x := by
        conv_lhs => rw [hn']
        rw [sA]
        ring
    _ ≤ 13 * ((p - 1) ^ 2 * (q - 1) ^ 2) * ∏ x ∈ (n.primeFactors.erase p).erase q, x :=
        Nat.mul_le_mul h2 le_rfl
    _ ≤ 13 * ((p - 1) ^ 2 * (q - 1) ^ 2) *
          ∏ x ∈ (n.primeFactors.erase p).erase q, (x - 1) ^ 2 :=
        Nat.mul_le_mul le_rfl hR
    _ = 13 * Nat.totient n ^ 2 := by
        rw [hφ, sB]
        ring

/-- **eq:squareclass-bound**, cleared of square roots: for squarefree `D > 1` with
`D ≡ 1 (mod 3)`, `7 ∤ D` and `D ≠ 10`, one has `144 D ≤ 13 φ(2D)²`. -/
theorem squareclass_bound_nat {D : ℕ} (hsf : Squarefree D) (h1 : 1 < D) (h3 : D % 3 = 1)
    (h7 : ¬ 7 ∣ D) (h10 : D ≠ 10) : 144 * D ≤ 13 * Nat.totient (2 * D) ^ 2 := by
  obtain ⟨E, hE | hE⟩ := Nat.even_or_odd' D
  · -- `D = 2E`; squarefreeness makes `E` odd, and `φ(2D) = 2 φ(E)`.
    subst hE
    have hEodd : E % 2 = 1 := by
      by_contra hev
      have h4 : 2 * 2 ∣ 2 * E := Nat.mul_dvd_mul_left 2 (by omega)
      exact Nat.squarefree_iff_prime_squarefree.mp hsf 2 Nat.prime_two h4
    have hφ : Nat.totient (2 * (2 * E)) = 2 * Nat.totient E := by
      rw [Nat.totient_two_mul_of_even ⟨E, by ring⟩,
        Nat.totient_two_mul_of_odd ⟨E / 2, by omega⟩]
    have hEsf : Squarefree E := hsf.of_mul_right
    have h5 : ∀ p ∈ E.primeFactors, 5 ≤ p := by
      intro p hp
      have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      have hpE := Nat.dvd_of_mem_primeFactors hp
      by_contra hlt
      push Not at hlt
      interval_cases p <;> omega
    rw [hφ]
    by_cases hEp : E.Prime
    · -- a single odd prime `E ≡ 2 (mod 3)`, `E ≠ 5`, so `E ≥ 11`
      have hE11 : 11 ≤ E := by omega
      rw [Nat.totient_prime hEp]
      obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hE11
      have e : 11 + x - 1 = x + 10 := by omega
      rw [e]
      nlinarith
    · have hE1 : 1 < E := by omega
      have hb := two_factor_bound hEsf h5 (one_lt_card_primeFactors hEsf hE1 hEp)
      nlinarith [hb, sq_nonneg (Nat.totient E)]
  · -- `D` odd: `φ(2D) = φ(D)`.
    subst hE
    have h5 : ∀ p ∈ (2 * E + 1).primeFactors, 5 ≤ p := by
      intro p hp
      have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
      have hpD := Nat.dvd_of_mem_primeFactors hp
      by_contra hlt
      push Not at hlt
      interval_cases p <;> omega
    rw [Nat.totient_two_mul_of_odd ⟨E, rfl⟩]
    by_cases hDp : (2 * E + 1).Prime
    · -- a single prime `D ≡ 1 (mod 3)`, `D ≠ 7`, so `D ≥ 13`
      have hD13 : 13 ≤ 2 * E + 1 := by omega
      rw [Nat.totient_prime hDp]
      obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le hD13
      rw [hx]
      have e : 13 + x - 1 = x + 12 := by omega
      rw [e]
      nlinarith
    · exact two_factor_bound hsf h5 (one_lt_card_primeFactors hsf h1 hDp)

/-- **eq:squareclass-bound** (manuscript line 3930): `φ(2D)/√D ≥ 12/√13` for every
squarefree `D > 1` with `D ≡ 1 (mod 3)`, `7 ∤ D` and `D ≠ 10`. -/
theorem squareclass_bound {D : ℕ} (hsf : Squarefree D) (h1 : 1 < D) (h3 : D % 3 = 1)
    (h7 : ¬ 7 ∣ D) (h10 : D ≠ 10) :
    12 / Real.sqrt 13 ≤ (Nat.totient (2 * D) : ℝ) / Real.sqrt D := by
  have hnat := squareclass_bound_nat hsf h1 h3 h7 h10
  have hreal : (144 : ℝ) * D ≤ 13 * (Nat.totient (2 * D) : ℝ) ^ 2 := by exact_mod_cast hnat
  have hD : (0 : ℝ) < Real.sqrt D := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < D))
  have h13 : (0 : ℝ) < Real.sqrt 13 := Real.sqrt_pos.mpr (by norm_num)
  rw [div_le_div_iff₀ h13 hD]
  have e1 : 12 * Real.sqrt D = Real.sqrt (144 * D) := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 144 by norm_num), show (144 : ℝ) = 12 ^ 2 by norm_num,
      Real.sqrt_sq (show (0 : ℝ) ≤ 12 by norm_num)]
  have e2 : (Nat.totient (2 * D) : ℝ) * Real.sqrt 13 =
      Real.sqrt (13 * (Nat.totient (2 * D) : ℝ) ^ 2) := by
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 13 by norm_num),
      Real.sqrt_sq (show (0 : ℝ) ≤ (Nat.totient (2 * D) : ℝ) by positivity), mul_comm]
  rw [e1, e2]
  exact Real.sqrt_le_sqrt hreal

/-- The squareclass statement as used in the manuscript (lines 3926–3946): if
`9m² + 4 = t²D` with `m ≥ 1`, `D` squarefree and `D ≠ 10`, then
`φ(2D)/√D ≥ 12/√13`. -/
theorem squareclass_of_delta {m t D : ℕ} (hm : 1 ≤ m) (hΔ : t ^ 2 * D = 9 * m ^ 2 + 4)
    (hsf : Squarefree D) (h10 : D ≠ 10) :
    12 / Real.sqrt 13 ≤ (Nat.totient (2 * D) : ℝ) / Real.sqrt D := by
  obtain ⟨h1, h3, h7⟩ := squareclass_props hm hΔ
  exact squareclass_bound hsf h1 h3 h7 h10

#print axioms delta_not_square
#print axioms seven_not_dvd_delta
#print axioms squareclass_props
#print axioms squareclass_bound_nat
#print axioms squareclass_bound
#print axioms squareclass_of_delta

end HaagerupIzumi.C8.NumberTheory
