module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsReduce

@[expose] public section

/-!
# Binomial toolkit for the closure of the Borcherds identity

W3, item (1), step (ii) of `Lattice/W3_PLAN.md`.  Reusable binomial and reindexing facts at the
level of modes:

* `zbinom_add`: Chu–Vandermonde `(x + y choose s) = ∑_t (x choose t) (y choose s - t)` for
  integer `x, y` (from `Ring.add_choose_eq`);
* `zbinom_neg`: `(-x choose t) = (-1)^t (x + t - 1 choose t)` (from `Ring.choose_neg`);
* `zbinom_natCast_symm`, `zbinom_mul_choose`: symmetry for natural upper index and
  `(m choose s) (s choose j) = (m choose j) (m - j choose s - j)` (from `Ring.choose_smul_choose`);
* the **locality operator** `dz k R F p q = ∑_{t ≤ R} (-1)^t (R choose t) F(p + R - t, q + t)`,
  the coefficient of `z₁^{-p-1} z₂^{-q-1}` in `(z₁ - z₂)^R F(z₁, z₂)` for
  `F(z₁, z₂) = ∑ F(p, q) z₁^{-p-1} z₂^{-q-1}`, with
  - `dz_succ` (`(z₁ - z₂)^{R+1} = (z₁ - z₂) (z₁ - z₂)^R`), `dz_add` (composition),
    `dz_mono` (locality of order `R` implies locality of every order `R' ≥ R`),
  - `dz_swap` (exchange of the two variables: `(z₂ - z₁)^R = (-1)^R (z₁ - z₂)^R`),
  - linearity (`dz_add_fun`, `dz_sub_fun`, `dz_neg_fun`, `dz_smul_fun`, `dz_map`,
    `dz_linearMap_apply`);
* `ModeAlgebra.bR_eq_dz`: for `r = R ≥ 0` the right side of the Borcherds identity is
  `dz k R [a_(·), b_(·)] c` (the classical form `(z₁ - z₂)^R [Y(a, z₁), Y(b, z₂)]`).

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

section Binom

variable (k : Type*) [Field k]

/-- **Chu–Vandermonde** for integer upper indices. -/
theorem zbinom_add (x y : ℤ) (s : ℕ) :
    zbinom k (x + y) s = ∑ t ∈ Finset.range (s + 1), zbinom k x t * zbinom k y (s - t) := by
  unfold zbinom
  rw [Ring.add_choose_eq s (Commute.all x y), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Nat.succ_eq_add_one, Int.cast_sum, Int.cast_mul]

/-- Upper negation. -/
theorem zbinom_neg (x : ℤ) (t : ℕ) :
    zbinom k (-x) t = (-1 : k) ^ t * zbinom k (x + t - 1) t := by
  unfold zbinom
  rw [Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, smul_eq_mul]
  push_cast
  ring

/-- Symmetry for a natural upper index. -/
theorem zbinom_natCast_symm {n t : ℕ} (h : t ≤ n) :
    zbinom k (n : ℤ) t = zbinom k (n : ℤ) (n - t) := by
  rw [zbinom_natCast, zbinom_natCast, Nat.choose_symm h]

/-- `(m choose s) (s choose j) = (m choose j) (m - j choose s - j)` for `j ≤ s`. -/
theorem zbinom_mul_choose (m : ℤ) {j s : ℕ} (h : j ≤ s) :
    zbinom k m s * (s.choose j : k) = zbinom k m j * zbinom k (m - j) (s - j) := by
  unfold zbinom
  have e := Ring.choose_smul_choose m h
  rw [nsmul_eq_mul] at e
  have e' := congrArg (fun z : ℤ => (z : k)) e
  push_cast at e'
  rw [mul_comm]
  exact e'

end Binom

/-! ## The locality operator `(z₁ - z₂)^R` -/

section Dz

variable (k : Type*) [Field k] {W : Type*} [AddCommGroup W] [Module k W]

/-- `dz k R F p q = ∑_{t ≤ R} (-1)^t (R choose t) F(p + R - t, q + t)`: the coefficient of
`z₁^{-p-1} z₂^{-q-1}` in `(z₁ - z₂)^R F(z₁, z₂)`. -/
def dz (R : ℕ) (F : ℤ → ℤ → W) (p q : ℤ) : W :=
  ∑ t ∈ Finset.range (R + 1), ((-1 : k) ^ t * (R.choose t : k)) • F (p + R - t) (q + t)

theorem dz_zero (F : ℤ → ℤ → W) (p q : ℤ) : dz k 0 F p q = F p q := by
  simp [dz]

theorem dz_succ (R : ℕ) (F : ℤ → ℤ → W) (p q : ℤ) :
    dz k (R + 1) F p q = dz k R F (p + 1) q - dz k R F p (q + 1) := by
  -- the middle sum, extended by a vanishing term
  have h1 : dz k R F (p + 1) q = ∑ t ∈ Finset.range (R + 2),
      ((-1 : k) ^ t * (R.choose t : k)) • F (p + 1 + R - t) (q + t) := by
    unfold dz
    rw [Finset.sum_range_succ _ (R + 1), Nat.choose_succ_self, Nat.cast_zero, mul_zero,
      zero_smul, add_zero]
  rw [h1]
  unfold dz
  rw [Finset.sum_range_succ' _ (R + 1), Finset.sum_range_succ' _ (R + 1)]
  have key : ∀ t ∈ Finset.range (R + 1),
      ((-1 : k) ^ (t + 1) * ((R + 1).choose (t + 1) : k)) •
          F (p + ((R + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)) (q + ((t + 1 : ℕ) : ℤ)) =
        ((-1 : k) ^ (t + 1) * (R.choose (t + 1) : k)) •
            F (p + 1 + (R : ℤ) - ((t + 1 : ℕ) : ℤ)) (q + ((t + 1 : ℕ) : ℤ)) -
          ((-1 : k) ^ t * (R.choose t : k)) • F (p + (R : ℤ) - (t : ℤ)) (q + 1 + (t : ℤ)) := by
    intro t _
    have e1 : p + ((R + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) = p + (R : ℤ) - (t : ℤ) := by
      push_cast; ring
    have e2 : p + 1 + (R : ℤ) - ((t + 1 : ℕ) : ℤ) = p + (R : ℤ) - (t : ℤ) := by
      push_cast; ring
    have e3 : q + ((t + 1 : ℕ) : ℤ) = q + 1 + (t : ℤ) := by
      push_cast; ring
    rw [e1, e2, e3, Nat.choose_succ_succ', Nat.cast_add, pow_succ]
    module
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib]
  simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one, one_smul, Nat.cast_zero,
    sub_zero, add_zero]
  have e4 : p + ((R + 1 : ℕ) : ℤ) = p + 1 + (R : ℤ) := by push_cast; ring
  rw [e4]
  abel

/-- `(z₁ - z₂)^{R+S} = (z₁ - z₂)^S (z₁ - z₂)^R`. -/
theorem dz_add (R S : ℕ) (F : ℤ → ℤ → W) :
    ∀ p q, dz k (R + S) F p q = dz k S (dz k R F) p q := by
  induction S with
  | zero => intro p q; rw [dz_zero, add_zero]
  | succ S ih =>
    intro p q
    rw [← add_assoc, dz_succ, dz_succ, ih, ih]

theorem dz_zero_fun (R : ℕ) (p q : ℤ) : dz k R (fun _ _ => (0 : W)) p q = 0 := by
  simp [dz]

/-- **Monotonicity of locality**: order `R` implies every order `R' ≥ R`. -/
theorem dz_mono {R R' : ℕ} (F : ℤ → ℤ → W) (h : ∀ p q, dz k R F p q = 0) (hR : R ≤ R') :
    ∀ p q, dz k R' F p q = 0 := by
  obtain ⟨S, rfl⟩ := Nat.exists_eq_add_of_le hR
  intro p q
  have hF : dz k R F = fun _ _ => (0 : W) := funext fun p => funext fun q => h p q
  rw [dz_add, hF, dz_zero_fun]

theorem neg_one_pow_mul_self (n : ℕ) : (-1 : k) ^ n * (-1 : k) ^ n = 1 := by
  rw [← mul_pow]
  simp

/-- **Exchange of the variables**: `dz k R F^swap q p = (-1)^R dz k R F p q`. -/
theorem dz_swap (R : ℕ) (F : ℤ → ℤ → W) (p q : ℤ) :
    dz k R (fun u v => F v u) q p = (-1 : k) ^ R • dz k R F p q := by
  unfold dz
  rw [Finset.smul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t ≤ R := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht'
  have e0 : t + s + 1 - 1 - t = s := by omega
  rw [e0]
  have e1 : q + ((t + s : ℕ) : ℤ) - (s : ℤ) = q + (t : ℤ) := by push_cast; ring
  have e2 : p + ((t + s : ℕ) : ℤ) - ((t + s - s : ℕ) : ℤ) = p + (s : ℤ) := by
    rw [show t + s - s = t by omega]; push_cast; ring
  have e3 : p + (s : ℤ) = p + ((t + s : ℕ) : ℤ) - (t : ℤ) := by push_cast; ring
  have e4 : q + ((t + s : ℕ) : ℤ) - ((t + s - s : ℕ) : ℤ) = q + (s : ℤ) := by
    rw [show t + s - s = t by omega]; push_cast; ring
  show ((-1 : k) ^ s * ((t + s).choose s : k)) • F (p + (s : ℤ)) (q + ((t + s : ℕ) : ℤ) - s) =
    (-1 : k) ^ (t + s) • (((-1 : k) ^ t * ((t + s).choose t : k)) •
      F (p + ((t + s : ℕ) : ℤ) - (t : ℤ)) (q + (t : ℤ)))
  rw [e1, ← e3, smul_smul, Nat.choose_symm_add]
  congr 1
  rw [pow_add, show (-1 : k) ^ t * (-1 : k) ^ s * ((-1 : k) ^ t * ((t + s).choose s : k)) =
    ((-1 : k) ^ t * (-1 : k) ^ t) * ((-1 : k) ^ s * ((t + s).choose s : k)) by ring,
    neg_one_pow_mul_self, one_mul]

theorem dz_add_fun (R : ℕ) (F G : ℤ → ℤ → W) (p q : ℤ) :
    dz k R (fun u v => F u v + G u v) p q = dz k R F p q + dz k R G p q := by
  simp only [dz, smul_add, Finset.sum_add_distrib]

theorem dz_sub_fun (R : ℕ) (F G : ℤ → ℤ → W) (p q : ℤ) :
    dz k R (fun u v => F u v - G u v) p q = dz k R F p q - dz k R G p q := by
  simp only [dz, smul_sub, Finset.sum_sub_distrib]

theorem dz_neg_fun (R : ℕ) (F : ℤ → ℤ → W) (p q : ℤ) :
    dz k R (fun u v => -F u v) p q = -dz k R F p q := by
  simp only [dz, smul_neg, Finset.sum_neg_distrib]

theorem dz_smul_fun (R : ℕ) (μ : k) (F : ℤ → ℤ → W) (p q : ℤ) :
    dz k R (fun u v => μ • F u v) p q = μ • dz k R F p q := by
  simp only [dz, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_comm]

theorem dz_map {W' : Type*} [AddCommGroup W'] [Module k W'] (f : W →ₗ[k] W') (R : ℕ)
    (F : ℤ → ℤ → W) (p q : ℤ) : f (dz k R F p q) = dz k R (fun u v => f (F u v)) p q := by
  simp only [dz, map_sum, map_smul]

theorem dz_linearMap_apply {V' : Type*} [AddCommGroup V'] [Module k V'] (R : ℕ)
    (F : ℤ → ℤ → (V' →ₗ[k] W)) (p q : ℤ) (c : V') :
    dz k R F p q c = dz k R (fun u v => F u v c) p q := by
  simp only [dz, LinearMap.sum_apply, LinearMap.smul_apply]

end Dz

/-! ## The right side of the Borcherds identity as `(z₁ - z₂)^R [Y(a, z₁), Y(b, z₂)]` -/

namespace ModeAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (M : ModeAlgebra k V)

/-- The commutator family `[a_(u), b_(v)] c`. -/
def comm (a b c : V) : ℤ → ℤ → V :=
  fun u v => M.mode u a (M.mode v b c) - M.mode v b (M.mode u a c)

/-- **For `r = R ≥ 0` the right side of the Borcherds identity is `(z₁ - z₂)^R [a(z₁), b(z₂)]`**
(any range `N > R`). -/
theorem bR_eq_dz (a b c : V) (p q : ℤ) (R : ℕ) {N : ℕ} (hN : R + 1 ≤ N) :
    M.bR a b c p q R N = dz k R (M.comm a b c) p q := by
  have hcut : M.bR a b c p q R N = M.bR a b c p q R (R + 1) :=
    sum_range_eq_of_vanish _ (fun t ht => by
      rw [zbinom_natCast_of_lt k (by omega), mul_zero, zero_smul]) hN le_rfl
  rw [hcut]
  -- the `Z` part, reflected
  have hZ : ∑ t ∈ Finset.range (R + 1), ((-1 : k) ^ t * (R.choose t : k)) •
        M.mode (q + (R : ℤ) - t) b (M.mode (p + t) a c) =
      (-1 : k) ^ R • dz k R (fun u v => M.mode v b (M.mode u a c)) p q := by
    have h := dz_swap k R (fun u v => M.mode v b (M.mode u a c)) p q
    unfold dz at h ⊢
    rw [← h]
  have hs : (-1 : k) ^ ((R : ℕ) : ℤ) = (-1 : k) ^ R := zpow_natCast _ _
  unfold bR comm
  rw [dz_sub_fun]
  have hY : ∑ t ∈ Finset.range (R + 1), ((-1 : k) ^ t * zbinom k (R : ℤ) t) •
        (M.mode (p + (R : ℤ) - t) a (M.mode (q + t) b c) -
          (-1 : k) ^ ((R : ℕ) : ℤ) • M.mode (q + (R : ℤ) - t) b (M.mode (p + t) a c)) =
      dz k R (fun u v => M.mode u a (M.mode v b c)) p q -
        (-1 : k) ^ R • ∑ t ∈ Finset.range (R + 1), ((-1 : k) ^ t * (R.choose t : k)) •
          M.mode (q + (R : ℤ) - t) b (M.mode (p + t) a c) := by
    unfold dz
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [zbinom_natCast, hs]
    module
  rw [hY, hZ, smul_smul, neg_one_pow_mul_self, one_smul]

end ModeAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.zbinom_add
#print axioms HaagerupIzumi.C8.zbinom_neg
#print axioms HaagerupIzumi.C8.zbinom_mul_choose
#print axioms HaagerupIzumi.C8.dz_succ
#print axioms HaagerupIzumi.C8.dz_add
#print axioms HaagerupIzumi.C8.dz_mono
#print axioms HaagerupIzumi.C8.dz_swap
#print axioms HaagerupIzumi.C8.ModeAlgebra.bR_eq_dz
