module

public import HaagerupIzumi.C8.VertexAlgebra.NormalWords
public import Mathlib.Algebra.Module.Submodule.EqLocus

@[expose] public section

/-!
# Vertex algebras from the Borcherds identity

The shared interface `HaagerupIzumi.C8.VertexAlgebra` (file `Basic.lean`) records the commutator
formula, the iterate formula, skew symmetry and the translation identities as fields.  This file
derives all of them from the Borcherds (Jacobi) identity, so that the interface is foundational:
`BorcherdsVertexAlgebra.toVertexAlgebra` builds a `VertexAlgebra` from a
`BorcherdsVertexAlgebra`, whose only axioms are

* the modes `a_(n) b`, the vacuum `1`, an `ℕ`-grading of CFT type (`grade_internal`,
  `grade_zero`), the weight rule `mode_grade` and the truncation `mode_trunc` (as in `Basic`);
* the vacuum axioms `1_(n) = δ_{n,-1}` (`vac_mode`), `a_(n) 1 = 0` for `n ≥ 0`
  (`mode_vac_nonneg`) and `a_(-1) 1 = a` (`mode_vac_neg_one`);
* the Borcherds identity, for homogeneous `a ∈ V_i`, `b ∈ V_j`, `c ∈ V_l` and all `p q r : ℤ`,
  `∑_{t≥0} (p choose t) (a_(r+t) b)_(p+q-t) c =
     ∑_{t≥0} (-1)^t (r choose t) (a_(p+r-t) b_(q+t) c - (-1)^r b_(q+r-t) a_(p+t) c)`.

**Range of summation in `borcherds`.**  Both sums are written over `t < N` with
`N = i + j + l + |p| + |q| + |r| + 1`.  Every omitted summand vanishes by `mode_trunc`:
on the left `a_(r+t) b = 0` once `r + t ≥ i + j`, i.e. for `t ≥ i + j - r`; on the right
`b_(q+t) c = 0` once `t ≥ j + l - q` and `a_(p+t) c = 0` once `t ≥ i + l - p`.  All three
thresholds are `≤ i + j + l + |p| + |q| + |r|`, so the field is exactly the textbook identity;
the extra `+ 1` only guarantees that the `t = 0` term is always displayed (it matters only in
the degenerate case `i = j = l = p = q = r = 0`).

With `T a := a_(-2) 1` the following are proved (manuscript conventions; cf. Kac, *Vertex
algebras for beginners*, §4.8):
* `commutator` (Borcherds with `r = 0`), `iterate` (Borcherds with `p = 0`);
* `mode_T`: `(T a)_(n) b = -n a_(n-1) b` (Borcherds for `(a, 1, b)` with `q = 0`, `r = -2`:
  the right side vanishes and the left side is `(T a)_(n) b + n a_(n-1) b`);
* `T_mode`: `T (a_(n) b) = (T a)_(n) b + a_(n) (T b)` (Borcherds for `(a, b, 1)` with `p = 0`,
  `q = -2`, `r = n`);
* `factorial_smul_mode_vac`, `creation`: `t! • x_(-1-t) 1 = T^t x`, so
  `x_(-1-t) 1 = T^t x / t!` in characteristic zero;
* `skew`: `b_(n) a = ∑_t (-1)^(n+t+1) T^t (a_(n+t) b) / t!` (Borcherds for `(a, b, 1)` with
  `p = -1`, `q = 0`, `r = n`, characteristic zero).
The identities for non-homogeneous inputs follow by linearity from the decomposition
`V = ⊕ V_d` (`ext_grade`).  The ranges of summation match the fields of `Basic.lean` exactly
(they are enlarged or shrunk using `mode_trunc`).  No hypothesis is external.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

/-! ### Binomial coefficients -/

theorem zbinom_zero_right (k : Type*) [Field k] (m : ℤ) : zbinom k m 0 = 1 := by
  unfold zbinom
  rw [Ring.choose_zero_right, Int.cast_one]

theorem zbinom_one_right (k : Type*) [Field k] (m : ℤ) : zbinom k m 1 = (m : k) := by
  unfold zbinom
  rw [Ring.choose_one_right]

theorem choose_neg_one_int (t : ℕ) : Ring.choose (-1 : ℤ) t = (-1) ^ t := by
  induction t with
  | zero => rw [Ring.choose_zero_right, pow_zero]
  | succ t ih =>
    have h := Ring.choose_succ_succ (-1 : ℤ) t
    rw [neg_add_cancel, Ring.choose_zero_succ, ih] at h
    have h' : Ring.choose (-1 : ℤ) (t + 1) + (-1) ^ t = 0 := by
      rw [add_comm (Ring.choose (-1 : ℤ) (t + 1))]
      exact h.symm
    rw [pow_succ, mul_neg_one]
    exact eq_neg_of_add_eq_zero_left h'

theorem zbinom_neg_one (k : Type*) [Field k] (t : ℕ) : zbinom k (-1) t = (-1) ^ t := by
  unfold zbinom
  rw [choose_neg_one_int]
  simp

/-! ### Finite sums over `range` -/

section Sums

variable {M : Type*} [AddCommMonoid M]

/-- Sums over `range N` agree for all `N` beyond the point where the summands vanish. -/
theorem sum_range_eq_of_vanish (f : ℕ → M) {N₀ N₁ N₂ : ℕ} (h : ∀ t, N₀ ≤ t → f t = 0)
    (h₁ : N₀ ≤ N₁) (h₂ : N₀ ≤ N₂) :
    ∑ t ∈ Finset.range N₁, f t = ∑ t ∈ Finset.range N₂, f t := by
  have e : ∀ N, N₀ ≤ N → ∑ t ∈ Finset.range N₀, f t = ∑ t ∈ Finset.range N, f t := by
    intro N hN
    refine Finset.sum_subset (Finset.range_subset_range.2 hN) ?_
    intro t _ ht
    exact h t (by simpa using ht)
  rw [← e N₁ h₁, ← e N₂ h₂]

theorem sum_range_congr_of_vanish {f g : ℕ → M} {N₀ N₁ N₂ : ℕ} (hfg : ∀ t, f t = g t)
    (hg : ∀ t, N₀ ≤ t → g t = 0) (h₁ : N₀ ≤ N₁) (h₂ : N₀ ≤ N₂) :
    ∑ t ∈ Finset.range N₁, f t = ∑ t ∈ Finset.range N₂, g t := by
  rw [Finset.sum_congr rfl fun t _ => hfg t]
  exact sum_range_eq_of_vanish g hg h₁ h₂

theorem sum_range_eq_zero_term {f : ℕ → M} {N : ℕ} (hN : 0 < N) (hf : ∀ t, 1 ≤ t → f t = 0) :
    ∑ t ∈ Finset.range N, f t = f 0 := by
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hN)]
  intro t _ ht
  exact hf t (Nat.pos_of_ne_zero ht)

theorem sum_range_eq_two_terms {f : ℕ → M} {N : ℕ} (hN : 1 < N) (hf : ∀ t, 2 ≤ t → f t = 0) :
    ∑ t ∈ Finset.range N, f t = f 0 + f 1 := by
  rw [sum_range_eq_of_vanish f hf (by omega) (le_refl 2)]
  simp [Finset.sum_range_succ]

/-- Only `t = 0` contributes on the right. -/
theorem eq_of_sum_right_single {f g : ℕ → M} {N : ℕ}
    (h : ∑ t ∈ Finset.range N, f t = ∑ t ∈ Finset.range N, g t) (hN : 0 < N)
    (hg : ∀ t, 1 ≤ t → g t = 0) : ∑ t ∈ Finset.range N, f t = g 0 := by
  rw [h, sum_range_eq_zero_term hN hg]

/-- Only `t = 0` contributes on the left. -/
theorem eq_of_sum_left_single {f g : ℕ → M} {N : ℕ}
    (h : ∑ t ∈ Finset.range N, f t = ∑ t ∈ Finset.range N, g t) (hN : 0 < N)
    (hf : ∀ t, 1 ≤ t → f t = 0) : f 0 = ∑ t ∈ Finset.range N, g t := by
  rw [← h, sum_range_eq_zero_term hN hf]

/-- Only `t = 0, 1` contribute on the left, and the right vanishes. -/
theorem eq_of_sum_left_two_right_zero {f g : ℕ → M} {N : ℕ}
    (h : ∑ t ∈ Finset.range N, f t = ∑ t ∈ Finset.range N, g t) (hN : 1 < N)
    (hf : ∀ t, 2 ≤ t → f t = 0) (hg : ∀ t, g t = 0) : f 0 + f 1 = 0 := by
  rw [← sum_range_eq_two_terms hN hf, h]
  exact Finset.sum_eq_zero fun t _ => hg t

/-- Only `t = 0` contributes on the left and only `t = 0, 1` on the right. -/
theorem eq_of_sum_left_single_right_two {f g : ℕ → M} {N : ℕ}
    (h : ∑ t ∈ Finset.range N, f t = ∑ t ∈ Finset.range N, g t) (hN : 1 < N)
    (hf : ∀ t, 1 ≤ t → f t = 0) (hg : ∀ t, 2 ≤ t → g t = 0) : f 0 = g 0 + g 1 := by
  rw [← sum_range_eq_zero_term (N := N) (by omega) hf, h, sum_range_eq_two_terms hN hg]

end Sums

/-! ### The structure -/

/-- An `ℕ`-graded vertex algebra of CFT type over a field `k`, presented by its modes and
axiomatized by the vacuum axioms and the Borcherds identity.  The summation range in
`borcherds` is justified in the module docstring: every omitted summand vanishes by
`mode_trunc`. -/
structure BorcherdsVertexAlgebra (k : Type*) [Field k] (V : Type*) [AddCommGroup V]
    [Module k V] where
  /-- `mode n a b = a_(n) b`. -/
  mode : ℤ → V →ₗ[k] V →ₗ[k] V
  /-- The vacuum vector. -/
  vac : V
  /-- The conformal-weight grading. -/
  grade : ℕ → Submodule k V
  grade_internal : DirectSum.IsInternal grade
  /-- CFT type: `V_0 = k·1`. -/
  grade_zero : grade 0 = k ∙ vac
  /-- `a_(n)` changes weight by `wt a - n - 1`. -/
  mode_grade : ∀ {i j : ℕ} {a b : V} (n : ℤ), a ∈ grade i → b ∈ grade j →
    n + 1 ≤ (i : ℤ) + j → mode n a b ∈ grade ((i : ℤ) + j - n - 1).toNat
  /-- Products of negative weight vanish. -/
  mode_trunc : ∀ {i j : ℕ} {a b : V} (n : ℤ), a ∈ grade i → b ∈ grade j →
    (i : ℤ) + j ≤ n → mode n a b = 0
  /-- `1_(n) = δ_{n,-1}`. -/
  vac_mode : ∀ (n : ℤ) (b : V), mode n vac b = if n = -1 then b else 0
  /-- Creation: `a_(n) 1 = 0` for `n ≥ 0`. -/
  mode_vac_nonneg : ∀ (n : ℤ) (a : V), 0 ≤ n → mode n a vac = 0
  /-- Creation: `a_(-1) 1 = a`. -/
  mode_vac_neg_one : ∀ a : V, mode (-1) a vac = a
  /-- The Borcherds identity for homogeneous `a ∈ V_i`, `b ∈ V_j`, `c ∈ V_l`. -/
  borcherds : ∀ {i j l : ℕ} {a b c : V}, a ∈ grade i → b ∈ grade j → c ∈ grade l →
    ∀ p q r : ℤ,
    ∑ t ∈ Finset.range (i + j + l + p.natAbs + q.natAbs + r.natAbs + 1),
        zbinom k p t • mode (p + q - t) (mode (r + t) a b) c =
      ∑ t ∈ Finset.range (i + j + l + p.natAbs + q.natAbs + r.natAbs + 1),
        ((-1 : k) ^ t * zbinom k r t) •
          (mode (p + r - t) a (mode (q + t) b c) -
            (-1 : k) ^ r • mode (q + r - t) b (mode (p + t) a c))

namespace BorcherdsVertexAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (B : BorcherdsVertexAlgebra k V)

/-! ### Elementary consequences -/

theorem vac_mem_grade_zero : B.vac ∈ B.grade 0 := by
  rw [B.grade_zero]
  exact Submodule.mem_span_singleton_self _

theorem vac_mode_of_ne {n : ℤ} (hn : n ≠ -1) (b : V) : B.mode n B.vac b = 0 := by
  rw [B.vac_mode, if_neg hn]

theorem mode_mem_grade' {i j e : ℕ} {a b : V} (n : ℤ) (ha : a ∈ B.grade i)
    (hb : b ∈ B.grade j) (he : (e : ℤ) = i + j - n - 1) : B.mode n a b ∈ B.grade e := by
  have h := B.mode_grade n ha hb (by omega)
  have h' : ((i : ℤ) + j - n - 1).toNat = e := by omega
  rwa [h'] at h

/-- Two linear maps out of `V` agreeing on every graded piece are equal. -/
theorem ext_grade {W : Type*} [AddCommGroup W] [Module k W] {f g : V →ₗ[k] W}
    (h : ∀ l, ∀ c ∈ B.grade l, f c = g c) : f = g := by
  have htop : (⊤ : Submodule k V) ≤ LinearMap.eqLocus f g := by
    rw [← B.grade_internal.submodule_iSup_eq_top]
    exact iSup_le fun l c hc => LinearMap.mem_eqLocus.2 (h l c hc)
  exact LinearMap.ext fun c => LinearMap.mem_eqLocus.1 (htop Submodule.mem_top)

/-! ### Translation -/

/-- Translation `T a = a_(-2) 1`. -/
noncomputable def T : V →ₗ[k] V := (B.mode (-2)).flip B.vac

theorem T_apply (a : V) : B.T a = B.mode (-2) a B.vac := rfl

theorem T_grade {i : ℕ} {a : V} (ha : a ∈ B.grade i) : B.T a ∈ B.grade (i + 1) := by
  rw [T_apply]
  exact B.mode_mem_grade' (-2) ha B.vac_mem_grade_zero (by omega)

/-- `(T a)_(n) b = -n a_(n-1) b` for homogeneous `a`, `b`. -/
theorem mode_T_hom {i l : ℕ} {a b : V} (ha : a ∈ B.grade i) (hb : b ∈ B.grade l) (n : ℤ) :
    B.mode n (B.T a) b = -((n : k) • B.mode (n - 1) a b) := by
  have h := eq_of_sum_left_two_right_zero (B.borcherds ha B.vac_mem_grade_zero hb n 0 (-2))
    (by omega)
    (fun t ht => by
      rw [B.mode_vac_nonneg (-2 + (t : ℤ)) a (by omega), map_zero, LinearMap.zero_apply,
        smul_zero])
    (fun t => by
      simp only [B.vac_mode_of_ne (show (0 : ℤ) + t ≠ -1 by omega),
        B.vac_mode_of_ne (show (0 : ℤ) + -2 - t ≠ -1 by omega), map_zero, smul_zero,
        sub_zero])
  have e : (-2 : ℤ) + 1 = -1 := by norm_num
  simp only [Nat.cast_zero, Nat.cast_one, add_zero, sub_zero, zbinom_zero_right,
    zbinom_one_right, one_smul, e, B.mode_vac_neg_one] at h
  rw [T_apply]
  exact eq_neg_of_add_eq_zero_left h

/-- `T (a_(n) b) = (T a)_(n) b + a_(n) (T b)` for homogeneous `a`, `b`. -/
theorem T_mode_hom {i j : ℕ} {a b : V} (ha : a ∈ B.grade i) (hb : b ∈ B.grade j) (n : ℤ) :
    B.T (B.mode n a b) = B.mode n (B.T a) b + B.mode n a (B.T b) := by
  have h := eq_of_sum_left_single_right_two (B.borcherds ha hb B.vac_mem_grade_zero 0 (-2) n)
    (by omega)
    (fun t ht => by rw [zbinom_zero_left_of_pos k (t := t) (by omega), zero_smul])
    (fun t ht => by
      simp only [B.mode_vac_nonneg (-2 + (t : ℤ)) b (by omega),
        B.mode_vac_nonneg (0 + (t : ℤ)) a (by omega), map_zero, smul_zero, sub_zero])
  have e : (-2 : ℤ) + 1 = -1 := by norm_num
  simp only [Nat.cast_zero, Nat.cast_one, add_zero, zero_add, sub_zero, zbinom_zero_right,
    zbinom_one_right, pow_zero, pow_one, one_mul, neg_one_mul, one_smul, e,
    B.mode_vac_neg_one, B.mode_vac_nonneg 0 a le_rfl, B.mode_vac_nonneg 1 a zero_le_one,
    map_zero, smul_zero] at h
  rw [B.mode_T_hom ha hb n]
  simp only [T_apply]
  rw [h, neg_smul]
  abel

/-- `(T a)_(n) b = -n a_(n-1) b` for all `a`, `b`. -/
theorem mode_T (n : ℤ) (a b : V) : B.mode n (B.T a) b = -((n : k) • B.mode (n - 1) a b) := by
  have h1 : ∀ i a, a ∈ B.grade i → ∀ b,
      B.mode n (B.T a) b = -((n : k) • B.mode (n - 1) a b) := by
    intro i a ha b
    have key : B.mode n (B.T a) = -((n : k) • B.mode (n - 1) a) :=
      B.ext_grade fun l b hb => by
        simp only [LinearMap.neg_apply, LinearMap.smul_apply]
        exact B.mode_T_hom ha hb n
    rw [key, LinearMap.neg_apply, LinearMap.smul_apply]
  have key : ((B.mode n).flip b).comp B.T = -((n : k) • (B.mode (n - 1)).flip b) :=
    B.ext_grade fun i a ha => by
      simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.smul_apply,
        LinearMap.flip_apply]
      exact h1 i a ha b
  have := LinearMap.congr_fun key a
  simpa only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.flip_apply] using this

/-- `T (a_(n) b) = (T a)_(n) b + a_(n) (T b)` for all `a`, `b`. -/
theorem T_mode (n : ℤ) (a b : V) :
    B.T (B.mode n a b) = B.mode n (B.T a) b + B.mode n a (B.T b) := by
  have h1 : ∀ i a, a ∈ B.grade i → ∀ b,
      B.T (B.mode n a b) = B.mode n (B.T a) b + B.mode n a (B.T b) := by
    intro i a ha b
    have key : B.T.comp (B.mode n a) = B.mode n (B.T a) + (B.mode n a).comp B.T :=
      B.ext_grade fun l b hb => by
        simp only [LinearMap.comp_apply, LinearMap.add_apply]
        exact B.T_mode_hom ha hb n
    have := LinearMap.congr_fun key b
    simpa only [LinearMap.comp_apply, LinearMap.add_apply] using this
  have key : B.T.comp ((B.mode n).flip b) =
      ((B.mode n).flip b).comp B.T + (B.mode n).flip (B.T b) :=
    B.ext_grade fun i a ha => by
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.flip_apply]
      exact h1 i a ha b
  have := LinearMap.congr_fun key a
  simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.flip_apply] using this

/-! ### Creation -/

/-- `t! • x_(-1-t) 1 = T^t x`. -/
theorem factorial_smul_mode_vac (t : ℕ) (x : V) :
    ((t.factorial : ℕ) : k) • B.mode (-1 - (t : ℤ)) x B.vac = (B.T ^ t) x := by
  induction t generalizing x with
  | zero => simp [B.mode_vac_neg_one]
  | succ t ih =>
    rw [pow_succ, Module.End.mul_apply, ← ih (B.T x), B.mode_T, Nat.factorial_succ]
    have e1 : (-1 - ((t + 1 : ℕ) : ℤ)) = -1 - (t : ℤ) - 1 := by push_cast; ring
    have e2 : (((-1 - (t : ℤ) : ℤ)) : k) = -((t : k) + 1) := by push_cast; ring
    rw [e1, e2, neg_smul, neg_neg, smul_smul]
    congr 1
    push_cast
    ring

/-- **Creation.** `x_(-1-t) 1 = T^t x / t!` in characteristic zero. -/
theorem creation [CharZero k] (t : ℕ) (x : V) :
    B.mode (-1 - (t : ℤ)) x B.vac = ((t.factorial : k))⁻¹ • (B.T ^ t) x := by
  rw [← B.factorial_smul_mode_vac t x, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast t.factorial_ne_zero), one_smul]

/-! ### Commutator and iterate formulas -/

/-- Commutator formula for homogeneous `a`, `b`, `c` (Borcherds with `r = 0`). -/
theorem commutator_hom {i j l : ℕ} {a b c : V} (ha : a ∈ B.grade i) (hb : b ∈ B.grade j)
    (hc : c ∈ B.grade l) (m n : ℤ) :
    B.mode m a (B.mode n b c) - B.mode n b (B.mode m a c) =
      ∑ t ∈ Finset.range (i + j), zbinom k m t • B.mode (m + n - t) (B.mode t a b) c := by
  have h := eq_of_sum_right_single (B.borcherds ha hb hc m n 0) (by omega)
    (fun t ht => by rw [zbinom_zero_left_of_pos k (t := t) (by omega), mul_zero, zero_smul])
  simp only [Nat.cast_zero, add_zero, zero_add, sub_zero, pow_zero, zpow_zero,
    zbinom_zero_right, mul_one, one_smul] at h
  rw [← h]
  refine sum_range_eq_of_vanish _ (fun t ht => ?_) (by omega) le_rfl
  rw [B.mode_trunc (t : ℤ) ha hb (by omega), map_zero, LinearMap.zero_apply, smul_zero]

/-- **Commutator formula** `[a_(m), b_(n)] = ∑_t (m choose t) (a_(t) b)_(m+n-t)`, for
homogeneous `a`, `b` and every `c`. -/
theorem commutator {i j : ℕ} {a b : V} (ha : a ∈ B.grade i) (hb : b ∈ B.grade j) (m n : ℤ)
    (c : V) :
    B.mode m a (B.mode n b c) - B.mode n b (B.mode m a c) =
      ∑ t ∈ Finset.range (i + j), zbinom k m t • B.mode (m + n - t) (B.mode t a b) c := by
  have key : (B.mode m a).comp (B.mode n b) - (B.mode n b).comp (B.mode m a) =
      ∑ t ∈ Finset.range (i + j), zbinom k m t • B.mode (m + n - t) (B.mode t a b) :=
    B.ext_grade fun l c hc => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smul_apply]
      exact B.commutator_hom ha hb hc m n
  have := LinearMap.congr_fun key c
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] using this

/-- **Iterate formula** (Borcherds with `p = 0`), with the summation range of `Basic.lean`. -/
theorem iterate {i j l : ℕ} {a b c : V} (ha : a ∈ B.grade i) (hb : b ∈ B.grade j)
    (hc : c ∈ B.grade l) (m n : ℤ) :
    B.mode n (B.mode m a b) c =
      ∑ t ∈ Finset.range (i + j + l + n.natAbs),
        ((-1 : k) ^ t * zbinom k m t) •
          (B.mode (m - t) a (B.mode (n + t) b c) -
            (-1 : k) ^ m • B.mode (m + n - t) b (B.mode t a c)) := by
  have h := eq_of_sum_left_single (B.borcherds ha hb hc 0 n m) (by omega)
    (fun t ht => by rw [zbinom_zero_left_of_pos k (t := t) (by omega), zero_smul])
  simp only [Nat.cast_zero, add_zero, zero_add, sub_zero, zbinom_zero_right, one_smul] at h
  rw [h]
  refine sum_range_congr_of_vanish (fun t => ?_) (fun t ht => ?_) (by omega) le_rfl
  · rw [add_comm n m]
  · rw [B.mode_trunc (n + (t : ℤ)) hb hc (by omega), B.mode_trunc (t : ℤ) ha hc (by omega)]
    simp

/-! ### Skew symmetry -/

/-- **Skew symmetry** `b_(n) a = ∑_t (-1)^(n+t+1) T^t (a_(n+t) b) / t!` (Borcherds for
`(a, b, 1)` with `p = -1`, `q = 0`, `r = n`), with the summation range of `Basic.lean`. -/
theorem skew [CharZero k] {i j : ℕ} {a b : V} (ha : a ∈ B.grade i) (hb : b ∈ B.grade j)
    (n : ℤ) :
    B.mode n b a =
      ∑ t ∈ Finset.range (i + j + n.natAbs),
        ((-1 : k) ^ (n + t + 1) * ((t.factorial : k))⁻¹) • (B.T ^ t) (B.mode (n + t) a b) := by
  have h := eq_of_sum_right_single (B.borcherds ha hb B.vac_mem_grade_zero (-1) 0 n) (by omega)
    (fun t ht => by
      simp only [B.mode_vac_nonneg (0 + (t : ℤ)) b (by omega),
        B.mode_vac_nonneg (-1 + (t : ℤ)) a (by omega), map_zero, smul_zero, sub_zero])
  simp only [Nat.cast_zero, add_zero, zero_add, sub_zero, pow_zero, zbinom_zero_right, mul_one,
    one_smul, B.mode_vac_nonneg 0 b le_rfl, map_zero, zero_sub, B.mode_vac_neg_one] at h
  have hS : ∑ t ∈ Finset.range (i + j + n.natAbs),
      ((-1 : k) ^ t * ((t.factorial : k))⁻¹) • (B.T ^ t) (B.mode (n + t) a b) =
        -((-1 : k) ^ n • B.mode n b a) := by
    refine (sum_range_congr_of_vanish (fun t => ?_) (fun t ht => ?_) ?_ le_rfl).symm.trans h
    · rw [zbinom_neg_one, B.creation, smul_smul]
    · rw [B.mode_trunc (n + (t : ℤ)) ha hb (by omega), map_zero, smul_zero]
    · omega
  have h0 : (-1 : k) ≠ 0 := by norm_num
  have hcoef : ∀ t : ℕ, (-1 : k) ^ (n + t + 1) * ((t.factorial : k))⁻¹ =
      -((-1 : k) ^ n) * ((-1 : k) ^ t * ((t.factorial : k))⁻¹) := by
    intro t
    rw [zpow_add₀ h0, zpow_add₀ h0, zpow_natCast, zpow_one]
    ring
  have hsq : (-1 : k) ^ n * (-1 : k) ^ n = 1 := by
    rw [← mul_zpow, neg_one_mul, neg_neg, one_zpow]
  calc B.mode n b a = (-((-1 : k) ^ n)) • (-((-1 : k) ^ n • B.mode n b a)) := by
        rw [smul_neg, neg_smul, neg_neg, smul_smul, hsq, one_smul]
    _ = (-((-1 : k) ^ n)) • ∑ t ∈ Finset.range (i + j + n.natAbs),
          ((-1 : k) ^ t * ((t.factorial : k))⁻¹) • (B.T ^ t) (B.mode (n + t) a b) := by
        rw [hS]
    _ = ∑ t ∈ Finset.range (i + j + n.natAbs),
          ((-1 : k) ^ (n + t + 1) * ((t.factorial : k))⁻¹) • (B.T ^ t) (B.mode (n + t) a b) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [smul_smul, hcoef t]

/-! ### The interface -/

/-- The vertex algebra of the shared interface defined by a Borcherds vertex algebra, with
translation `T a = a_(-2) 1`.  Every field of `VertexAlgebra` is proved from the Borcherds
identity and the vacuum axioms. -/
noncomputable def toVertexAlgebra [CharZero k] : VertexAlgebra k V where
  mode := B.mode
  vac := B.vac
  T := B.T
  grade := B.grade
  grade_internal := B.grade_internal
  grade_zero := B.grade_zero
  mode_grade := B.mode_grade
  mode_trunc := B.mode_trunc
  T_grade := B.T_grade
  vac_mode := B.vac_mode
  mode_vac_nonneg := B.mode_vac_nonneg
  mode_vac_neg_one := B.mode_vac_neg_one
  T_eq := B.T_apply
  mode_T := B.mode_T
  T_mode := B.T_mode
  commutator := B.commutator
  iterate := B.iterate
  skew := B.skew

@[simp] theorem toVertexAlgebra_mode [CharZero k] : B.toVertexAlgebra.mode = B.mode := rfl
@[simp] theorem toVertexAlgebra_vac [CharZero k] : B.toVertexAlgebra.vac = B.vac := rfl
@[simp] theorem toVertexAlgebra_T [CharZero k] : B.toVertexAlgebra.T = B.T := rfl
@[simp] theorem toVertexAlgebra_grade [CharZero k] : B.toVertexAlgebra.grade = B.grade := rfl

end BorcherdsVertexAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.BorcherdsVertexAlgebra.toVertexAlgebra
#print axioms HaagerupIzumi.C8.BorcherdsVertexAlgebra.commutator
#print axioms HaagerupIzumi.C8.BorcherdsVertexAlgebra.iterate
#print axioms HaagerupIzumi.C8.BorcherdsVertexAlgebra.mode_T
#print axioms HaagerupIzumi.C8.BorcherdsVertexAlgebra.T_mode
#print axioms HaagerupIzumi.C8.BorcherdsVertexAlgebra.creation
#print axioms HaagerupIzumi.C8.BorcherdsVertexAlgebra.skew
