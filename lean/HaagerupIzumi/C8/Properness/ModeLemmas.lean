module

public import HaagerupIzumi.C8.VertexAlgebra.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

@[expose] public section

/-! # Mode identities used in the properness argument

General vertex-algebra consequences of the interface
`HaagerupIzumi.C8.VertexAlgebra` that the finite-gate argument of
`c8_expanded_20260929/haagerup_c8_expanded.tex`, Sections `sec:finite`–`sec:properness`
(lines 2093–2611), uses repeatedly:

* values of the binomial coefficients `zbinom` that occur;
* the vacuum, weight-zero vectors and translation;
* the zero-mode derivation rule `a₀(b_n c) = b_n(a₀ c) + (a₀ b)_n c`
  (the commutator formula with `m = 0`) and its `m = 1` analogue;
* the reduction `x_(n-1) v = n⁻¹ (x_n (T v) - T (x_n v))` used for negative modes
  (manuscript, proof of Lemma `lem:normal-controls`, line 2460);
* the Virasoro commutators of Lemma `lem:bootstrap`, eqs. `eq:L1-weight2` and
  `eq:L2-weight2` (lines 2377–2379), derived from the commutator formula with `ω`, and
  their weight-one analogues `[L(1), k_n] = -n k_(n+1)`, `[L(2), k_n] = -n k_(n+2)`
  (up to scalar terms from `L(1)k`);
* membership forms of skew symmetry and of the iterate formula.

Nothing here is specific to the central-charge-eight model and there are no hypotheses
beyond the fields of `VertexAlgebra` / `VertexOperatorAlgebra` (and `CharZero k` where a
division by a nonzero integer occurs).
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-! ### Binomial coefficients -/

theorem zbinom_natCast (n t : ℕ) : zbinom k (n : ℤ) t = (n.choose t : k) := by
  rw [zbinom, Ring.choose_natCast, Int.cast_natCast]

theorem zbinom_zero_zero : zbinom k 0 0 = 1 := by
  simpa using zbinom_natCast (k := k) 0 0

theorem zbinom_zero_of_ne_zero {t : ℕ} (ht : t ≠ 0) : zbinom k 0 t = 0 := by
  rw [zbinom, Ring.choose_zero_pos ℤ (Nat.pos_of_ne_zero ht), Int.cast_zero]

theorem zbinom_one_zero : zbinom k 1 0 = 1 := by
  simpa using zbinom_natCast (k := k) 1 0

theorem zbinom_one_one : zbinom k 1 1 = 1 := by
  simpa using zbinom_natCast (k := k) 1 1

theorem zbinom_one_add_two (t : ℕ) : zbinom k 1 (t + 2) = 0 := by
  have h := zbinom_natCast (k := k) 1 (t + 2)
  rw [Nat.choose_eq_zero_of_lt (by omega)] at h
  simpa using h

theorem zbinom_two_zero : zbinom k 2 0 = 1 := by
  simpa using zbinom_natCast (k := k) 2 0

theorem zbinom_two_one : zbinom k 2 1 = 2 := by
  simpa using zbinom_natCast (k := k) 2 1

theorem zbinom_two_two : zbinom k 2 2 = 1 := by
  simpa using zbinom_natCast (k := k) 2 2

theorem zbinom_two_three : zbinom k 2 3 = 0 := by
  have h := zbinom_natCast (k := k) 2 3
  rw [Nat.choose_eq_zero_of_lt (by norm_num)] at h
  simpa using h

theorem zbinom_three_zero : zbinom k 3 0 = 1 := by
  simpa using zbinom_natCast (k := k) 3 0

theorem zbinom_three_one : zbinom k 3 1 = 3 := by
  simpa using zbinom_natCast (k := k) 3 1

theorem zbinom_three_two : zbinom k 3 2 = 3 := by
  have h := zbinom_natCast (k := k) 3 2
  rw [show Nat.choose 3 2 = 3 by decide] at h
  simpa using h

theorem zbinom_three_three : zbinom k 3 3 = 1 := by
  simpa using zbinom_natCast (k := k) 3 3

namespace VertexAlgebra

variable (A : VertexAlgebra k V)

/-! ### Vacuum, weight zero, translation -/

theorem T_vac : A.T A.vac = 0 := by
  rw [A.T_eq, A.vac_mode]
  norm_num

theorem exists_smul_vac {x : V} (hx : x ∈ A.grade 0) : ∃ r : k, x = r • A.vac := by
  rw [A.grade_zero, Submodule.mem_span_singleton] at hx
  obtain ⟨r, hr⟩ := hx
  exact ⟨r, hr.symm⟩

theorem T_grade_zero {x : V} (hx : x ∈ A.grade 0) : A.T x = 0 := by
  obtain ⟨r, rfl⟩ := A.exists_smul_vac hx
  rw [map_smul, A.T_vac, smul_zero]

theorem mode_grade_zero_left {x : V} (hx : x ∈ A.grade 0) {n : ℤ} (hn : n ≠ -1) (y : V) :
    A.mode n x y = 0 := by
  obtain ⟨r, rfl⟩ := A.exists_smul_vac hx
  rw [map_smul, LinearMap.smul_apply, A.vac_mode, if_neg hn, smul_zero]

theorem mode_neg_one_grade_zero_left {x : V} (hx : x ∈ A.grade 0) (y : V) :
    ∃ r : k, A.mode (-1) x y = r • y := by
  obtain ⟨r, rfl⟩ := A.exists_smul_vac hx
  exact ⟨r, by rw [map_smul, LinearMap.smul_apply, A.vac_mode, if_pos rfl]⟩

theorem mode_neg_one_grade_zero_right {x : V} (hx : x ∈ A.grade 0) (y : V) :
    ∃ r : k, A.mode (-1) y x = r • y := by
  obtain ⟨r, rfl⟩ := A.exists_smul_vac hx
  exact ⟨r, by rw [map_smul, A.mode_vac_neg_one]⟩

/-- Weight bookkeeping: `a_(n) b` has weight `i + j - n - 1`. -/
theorem mode_mem_grade {i j d : ℕ} {a b : V} (ha : a ∈ A.grade i) (hb : b ∈ A.grade j)
    {n : ℤ} (h : (i : ℤ) + j - n - 1 = d) : A.mode n a b ∈ A.grade d := by
  have h' := A.mode_grade n ha hb (by omega)
  rwa [h, Int.toNat_natCast] at h'

theorem mode_T_zero (a b : V) : A.mode 0 (A.T a) b = 0 := by
  rw [A.mode_T]
  simp

/-- Zero modes commute with translation. -/
theorem zero_mode_T (a x : V) : A.mode 0 a (A.T x) = A.T (A.mode 0 a x) := by
  rw [A.T_mode, A.mode_T_zero, zero_add]

/-- `n x_(n-1) v = x_(n) (T v) - T (x_(n) v)`. -/
theorem mode_pred_smul (x v : V) (n : ℤ) :
    (n : k) • A.mode (n - 1) x v = A.mode n x (A.T v) - A.T (A.mode n x v) := by
  rw [A.T_mode, A.mode_T]
  abel

/-- Negative-mode reduction (manuscript line 2460): if `x_(n)(T v)` and `T(x_(n) v)` lie in a
subspace and `n ≠ 0`, so does `x_(n-1) v`. -/
theorem mode_pred_mem [CharZero k] {X : Submodule k V} {x v : V} {n : ℤ} (hn : n ≠ 0)
    (h1 : A.mode n x (A.T v) ∈ X) (h2 : A.T (A.mode n x v) ∈ X) :
    A.mode (n - 1) x v ∈ X := by
  have h := X.sub_mem h1 h2
  rw [← A.mode_pred_smul] at h
  exact (X.smul_mem_iff (Int.cast_ne_zero.mpr hn)).mp h

/-! ### Commutator formula with `m = 0` and `m = 1` -/

/-- The zero mode is a derivation of every product: `a₀(b_n c) = b_n(a₀ c) + (a₀ b)_n c`. -/
theorem zero_mode_comm {i j : ℕ} {a b : V} (ha : a ∈ A.grade i) (hb : b ∈ A.grade j)
    (n : ℤ) (c : V) :
    A.mode 0 a (A.mode n b c) = A.mode n b (A.mode 0 a c) + A.mode n (A.mode 0 a b) c := by
  have h := A.commutator ha hb 0 n c
  rcases Nat.eq_zero_or_pos (i + j) with hij | hij
  · rw [hij, Finset.sum_range_zero] at h
    have h0 : A.mode 0 a b = 0 := A.mode_trunc 0 ha hb (by omega)
    rw [h0, map_zero, LinearMap.zero_apply, add_zero]
    exact sub_eq_zero.mp h
  · rw [Finset.sum_eq_single 0] at h
    · rw [zbinom_zero_zero, one_smul] at h
      simp only [Nat.cast_zero, zero_add, sub_zero] at h
      rw [sub_eq_iff_eq_add] at h
      rw [h, add_comm]
    · intro t _ ht
      rw [zbinom_zero_of_ne_zero ht, zero_smul]
    · intro h0
      exact absurd (Finset.mem_range.mpr hij) h0

/-- The commutator formula with `m = 1`:
`a₁(b_n c) = b_n(a₁ c) + (a₀ b)_(n+1) c + (a₁ b)_n c`. -/
theorem one_mode_comm {i j : ℕ} {a b : V} (ha : a ∈ A.grade i) (hb : b ∈ A.grade j)
    (hij : 2 ≤ i + j) (n : ℤ) (c : V) :
    A.mode 1 a (A.mode n b c) =
      A.mode n b (A.mode 1 a c) + A.mode (n + 1) (A.mode 0 a b) c
        + A.mode n (A.mode 1 a b) c := by
  have h := A.commutator ha hb 1 n c
  rw [Finset.sum_eq_add 0 1 (by norm_num)] at h
  · simp only [Nat.cast_zero, Nat.cast_one, sub_zero, add_sub_cancel_left, zbinom_one_zero,
      zbinom_one_one, one_smul] at h
    rw [sub_eq_iff_eq_add, add_comm (1 : ℤ) n] at h
    rw [h]
    abel
  · intro t _ ht
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 2 := ⟨t - 2, by omega⟩
    rw [zbinom_one_add_two, zero_smul]
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0
  · intro h1
    exact absurd (Finset.mem_range.mpr (by omega)) h1

/-! ### Membership forms of skew symmetry and the iterate formula -/

/-- Skew symmetry, membership form: `b_(n) a` lies in `X` when every
`T^t (a_(n+t) b)` does. -/
theorem skew_mem {X : Submodule k V} {i j : ℕ} {a b : V} (ha : a ∈ A.grade i)
    (hb : b ∈ A.grade j) (n : ℤ)
    (h : ∀ t : ℕ, t < i + j + n.natAbs → (A.T ^ t) (A.mode (n + t) a b) ∈ X) :
    A.mode n b a ∈ X := by
  rw [A.skew ha hb n]
  exact X.sum_mem fun t ht => X.smul_mem _ (h t (Finset.mem_range.mp ht))

/-- The iterate formula, membership form. -/
theorem iterate_mem {X : Submodule k V} {i j l : ℕ} {a b c : V} (ha : a ∈ A.grade i)
    (hb : b ∈ A.grade j) (hc : c ∈ A.grade l) (m n : ℤ)
    (h1 : ∀ t : ℕ, t < i + j + l + n.natAbs → A.mode (m - t) a (A.mode (n + t) b c) ∈ X)
    (h2 : ∀ t : ℕ, t < i + j + l + n.natAbs → A.mode (m + n - t) b (A.mode t a c) ∈ X) :
    A.mode n (A.mode m a b) c ∈ X := by
  rw [A.iterate ha hb hc m n]
  exact X.sum_mem fun t ht => X.smul_mem _
    (X.sub_mem (h1 t (Finset.mem_range.mp ht)) (X.smul_mem _ (h2 t (Finset.mem_range.mp ht))))

/-- Powers of translation kill weight-zero vectors. -/
theorem T_pow_grade_zero {x : V} (hx : x ∈ A.grade 0) {t : ℕ} (ht : t ≠ 0) :
    (A.T ^ t) x = 0 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero ht
  rw [pow_succ, Module.End.mul_apply, A.T_grade_zero hx, map_zero]

end VertexAlgebra

namespace VertexOperatorAlgebra

variable (A : VertexOperatorAlgebra k V)

/-! ### Virasoro commutators (Lemma `lem:bootstrap`) -/

/-- `L(1) T x = T L(1) x + 2 d x` for `x` of weight `d`. -/
theorem L1_T {d : ℕ} {x : V} (hx : x ∈ A.grade d) :
    A.mode 2 A.ω (A.T x) = A.T (A.mode 2 A.ω x) + ((2 : k) * d) • x := by
  have h := A.T_mode 2 A.ω x
  rw [A.mode_T, show (2 : ℤ) - 1 = 1 by norm_num, A.L0 hx] at h
  rw [h]
  push_cast
  module

/-- `L(2) T x = T L(2) x + 3 L(1) x`. -/
theorem L2_T (x : V) :
    A.mode 3 A.ω (A.T x) = A.T (A.mode 3 A.ω x) + (3 : k) • A.mode 2 A.ω x := by
  have h := A.T_mode 3 A.ω x
  rw [A.mode_T, show (3 : ℤ) - 1 = 2 by norm_num] at h
  rw [h]
  push_cast
  module

/-- `[L(1), x_(n)] = -n x_(n+1) + (L(1) x)_(n)` for `x` of weight one. -/
theorem L1_comm_wt1 {x : V} (hx : x ∈ A.grade 1) (n : ℤ) (c : V) :
    A.mode 2 A.ω (A.mode n x c) =
      A.mode n x (A.mode 2 A.ω c) - (n : k) • A.mode (n + 1) x c
        + A.mode n (A.mode 2 A.ω x) c := by
  have h := A.commutator A.ω_mem hx 2 n c
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, sub_zero, zbinom_two_zero, zbinom_two_one,
    zbinom_two_two, one_smul] at h
  rw [A.Lm1, A.L0 hx, A.mode_T, map_smul, LinearMap.smul_apply,
    show (2 : ℤ) + n - 1 = n + 1 by ring, show (2 : ℤ) + n - 2 = n by ring] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

/-- `[L(2), x_(n)] = -n x_(n+2) + 3 (L(1) x)_(n+1)` for `x` of weight one. -/
theorem L2_comm_wt1 {x : V} (hx : x ∈ A.grade 1) (n : ℤ) (c : V) :
    A.mode 3 A.ω (A.mode n x c) =
      A.mode n x (A.mode 3 A.ω c) - (n : k) • A.mode (n + 2) x c
        + (3 : k) • A.mode (n + 1) (A.mode 2 A.ω x) c := by
  have h := A.commutator A.ω_mem hx 3 n c
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, sub_zero, zbinom_three_zero, zbinom_three_one,
    zbinom_three_two, one_smul] at h
  rw [A.Lm1, A.L0 hx, A.mode_T, map_smul, LinearMap.smul_apply,
    show (3 : ℤ) + n - 1 = n + 2 by ring, show (3 : ℤ) + n - 2 = n + 1 by ring] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

/-- Equation `eq:L1-weight2`: `[L(1), a_(n)] = (2-n) a_(n+1) + (L(1) a)_(n)` for `a` of
weight two. -/
theorem L1_comm_wt2 {a : V} (ha : a ∈ A.grade 2) (n : ℤ) (c : V) :
    A.mode 2 A.ω (A.mode n a c) =
      A.mode n a (A.mode 2 A.ω c) + ((2 : k) - n) • A.mode (n + 1) a c
        + A.mode n (A.mode 2 A.ω a) c := by
  have h := A.commutator A.ω_mem ha 2 n c
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, sub_zero, zbinom_two_zero, zbinom_two_one,
    zbinom_two_two, zbinom_two_three, one_smul, zero_smul, add_zero] at h
  rw [A.Lm1, A.L0 ha, A.mode_T, map_smul, LinearMap.smul_apply,
    show (2 : ℤ) + n - 1 = n + 1 by ring, show (2 : ℤ) + n - 2 = n by ring] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

/-- Equation `eq:L2-weight2`:
`[L(2), a_(n)] = (3-n) a_(n+2) + 3 (L(1) a)_(n+1) + (L(2) a)_(n)` for `a` of weight two. -/
theorem L2_comm_wt2 {a : V} (ha : a ∈ A.grade 2) (n : ℤ) (c : V) :
    A.mode 3 A.ω (A.mode n a c) =
      A.mode n a (A.mode 3 A.ω c) + ((3 : k) - n) • A.mode (n + 2) a c
        + (3 : k) • A.mode (n + 1) (A.mode 2 A.ω a) c + A.mode n (A.mode 3 A.ω a) c := by
  have h := A.commutator A.ω_mem ha 3 n c
  simp only [Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, sub_zero, zbinom_three_zero, zbinom_three_one,
    zbinom_three_two, zbinom_three_three, one_smul] at h
  rw [A.Lm1, A.L0 ha, A.mode_T, map_smul, LinearMap.smul_apply,
    show (3 : ℤ) + n - 1 = n + 2 by ring, show (3 : ℤ) + n - 2 = n + 1 by ring,
    show (3 : ℤ) + n - 3 = n by ring] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

end VertexOperatorAlgebra

#print axioms VertexAlgebra.zero_mode_comm
#print axioms VertexAlgebra.one_mode_comm
#print axioms VertexOperatorAlgebra.L1_comm_wt2
#print axioms VertexOperatorAlgebra.L2_comm_wt2

end HaagerupIzumi.C8
