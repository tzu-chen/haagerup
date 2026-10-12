module

public import HaagerupIzumi.C8.VertexAlgebra.Borcherds

@[expose] public section

/-!
# The Borcherds identity: reduction to the commutator and iterate families, the vacuum, and
generation

W3, first milestone (Borcherds identity for the lattice model).  Abstract setting: a
`ModeAlgebra` is a `BorcherdsVertexAlgebra` (`VertexAlgebra/Borcherds.lean`) without the field
`borcherds`: modes `a_(n) b`, a vacuum, an `ℕ`-grading with truncation, and the vacuum axioms.
For `a, b, c` and `p q r : ℤ` write (with summation range `N`)

* `bL a b c p q r N = ∑_{t<N} (p choose t) (a_(r+t) b)_(p+q-t) c`,
* `bR a b c p q r N = ∑_{t<N} (-1)^t (r choose t) (a_(p+r-t) b_(q+t) c - (-1)^r b_(q+r-t) a_(p+t) c)`,

and, for homogeneous `a ∈ V_i`, `b ∈ V_j`, `c ∈ V_l`, the *defect*
`bD i j l a b c p q r = bL - bR` at the range `i + j + l + |p| + |q| + |r| + 1` of
`BorcherdsVertexAlgebra.borcherds` (the summands beyond it vanish, `bL_stable`, `bR_stable`).
Proved here:

* **Pascal recursion** (`bD_pascal`): `D(p+1, q, r) = D(p, q+1, r) + D(p, q, r+1)`, from
  `(p+1 choose t+1) = (p choose t) + (p choose t+1)` (`lsum_pascal`, `ysum_pascal`);
* **reduction to two families** (`eq_zero_of_pascal`, `bD_eq_zero_of_comm_iter`): if the
  commutator family `D(p, q, 0)` and the iterate family `D(0, q, r)` vanish, then `D ≡ 0`
  (cf. Kac, *Vertex algebras for beginners*, 2nd ed., §4.8, the Borcherds identity (4.8.3)
  (numbering checked only against citations in the literature, not the book), and
  Lepowsky–Li, *Introduction to vertex operator algebras and their representations*, Ch. 3
  (section numbers from memory): the Jacobi identity is equivalent to the commutator formula
  plus the iterate (associator) formula);
* **the vacuum** (`good_vac`): the Borcherds identity holds for `(𝟏, b, c)`;
* `Good a`: the Borcherds identity holds for `(a, b, c)` for all homogeneous `b, c` and all
  `p, q, r` (with any sufficiently large range); `goodSub`: these `a` form a subspace;
  `good_iff_bD`: for homogeneous `a` this is exactly the identity in the form of
  `BorcherdsVertexAlgebra.borcherds`;
* **generation** (`goodSub_eq_top`): if `Good` is closed under `g_(n) -` for the generators `g`
  (`ProductClosedFor`) and `V` is generated from `𝟏` by the generators, then every `a` is `Good`.

**Not proved here**: closure under `n`-th products, `Good a ∧ Good b ⇒ Good (a_(n) b)`
(`ProductClosed`); it is reduced to the iterate family in `VertexAlgebra/BorcherdsProduct.lean`,
see `Lattice/W3_PLAN.md`.

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

theorem zbinom_succ_succ (k : Type*) [Field k] (m : ℤ) (t : ℕ) :
    zbinom k (m + 1) (t + 1) = zbinom k m t + zbinom k m (t + 1) := by
  unfold zbinom
  rw [Ring.choose_succ_succ]
  push_cast
  ring

/-! ## Generic sums and their Pascal recursions -/

section Sums

variable (k : Type*) [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- `∑_{t<N} (p choose t) X(r+t, p+q-t)`. -/
def lsum (X : ℤ → ℤ → V) (p q r : ℤ) (N : ℕ) : V :=
  ∑ t ∈ Finset.range N, zbinom k p t • X (r + t) (p + q - t)

/-- `∑_{t<N} (-1)^t (r choose t) Y(p+r-t, q+t)`. -/
def ysum (Y : ℤ → ℤ → V) (p q r : ℤ) (N : ℕ) : V :=
  ∑ t ∈ Finset.range N, ((-1 : k) ^ t * zbinom k r t) • Y (p + r - t) (q + t)

theorem lsum_pascal (X : ℤ → ℤ → V) (p q r : ℤ) (N : ℕ) :
    lsum k X (p + 1) q r (N + 1) = lsum k X p (q + 1) r (N + 1) + lsum k X p q (r + 1) N := by
  unfold lsum
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have key : ∀ t ∈ Finset.range N,
      zbinom k (p + 1) (t + 1) • X (r + ((t + 1 : ℕ) : ℤ)) (p + 1 + q - ((t + 1 : ℕ) : ℤ)) =
        zbinom k p (t + 1) • X (r + ((t + 1 : ℕ) : ℤ)) (p + (q + 1) - ((t + 1 : ℕ) : ℤ)) +
          zbinom k p t • X (r + 1 + (t : ℤ)) (p + q - (t : ℤ)) := by
    intro t _
    rw [zbinom_succ_succ, add_smul,
      show p + (q + 1) - ((t + 1 : ℕ) : ℤ) = p + 1 + q - ((t + 1 : ℕ) : ℤ) by ring,
      show r + ((t + 1 : ℕ) : ℤ) = r + 1 + (t : ℤ) by push_cast; ring,
      show p + 1 + q - ((t + 1 : ℕ) : ℤ) = p + q - (t : ℤ) by push_cast; ring]
    abel
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, zbinom_zero_right, zbinom_zero_right,
    show p + 1 + q - ((0 : ℕ) : ℤ) = p + (q + 1) - ((0 : ℕ) : ℤ) by ring]
  abel

theorem ysum_pascal (Y : ℤ → ℤ → V) (p q r : ℤ) (N : ℕ) :
    ysum k Y p q (r + 1) (N + 1) = ysum k Y (p + 1) q r (N + 1) - ysum k Y p (q + 1) r N := by
  unfold ysum
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have key : ∀ t ∈ Finset.range N,
      ((-1 : k) ^ (t + 1) * zbinom k (r + 1) (t + 1)) •
          Y (p + (r + 1) - ((t + 1 : ℕ) : ℤ)) (q + ((t + 1 : ℕ) : ℤ)) =
        ((-1 : k) ^ (t + 1) * zbinom k r (t + 1)) •
            Y (p + 1 + r - ((t + 1 : ℕ) : ℤ)) (q + ((t + 1 : ℕ) : ℤ)) -
          ((-1 : k) ^ t * zbinom k r t) • Y (p + r - (t : ℤ)) (q + 1 + (t : ℤ)) := by
    intro t _
    rw [zbinom_succ_succ,
      show p + (r + 1) - ((t + 1 : ℕ) : ℤ) = p + 1 + r - ((t + 1 : ℕ) : ℤ) by ring,
      show q + ((t + 1 : ℕ) : ℤ) = q + 1 + (t : ℤ) by push_cast; ring,
      show p + 1 + r - ((t + 1 : ℕ) : ℤ) = p + r - (t : ℤ) by push_cast; ring, pow_succ]
    module
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, zbinom_zero_right, zbinom_zero_right,
    show p + (r + 1) - ((0 : ℕ) : ℤ) = p + 1 + r - ((0 : ℕ) : ℤ) by ring]
  abel

end Sums

/-! ## Reduction to two families -/

/-- **Reduction to the commutator and iterate families.**  A function `f : ℤ³ → W` with
`f(p+1, q, r) = f(p, q+1, r) + f(p, q, r+1)` vanishes identically as soon as `f(p, q, 0) = 0`
and `f(0, q, r) = 0` for all `p, q, r`. -/
theorem eq_zero_of_pascal {W : Type*} [AddCommGroup W] (f : ℤ → ℤ → ℤ → W)
    (hpas : ∀ p q r, f (p + 1) q r = f p (q + 1) r + f p q (r + 1))
    (hcomm : ∀ p q, f p q 0 = 0) (hiter : ∀ q r, f 0 q r = 0) : ∀ p q r, f p q r = 0 := by
  have hpos : ∀ n : ℕ, ∀ q r, f n q r = 0 := by
    intro n
    induction n with
    | zero => exact hiter
    | succ n ih =>
      intro q r
      have h := hpas n q r
      push_cast
      rw [h, ih, ih, add_zero]
  have hneg : ∀ n : ℕ, ∀ q r, f (-(n : ℤ)) q r = 0 := by
    intro n
    induction n with
    | zero => intro q r; simpa using hiter q r
    | succ n ih =>
      have hg : ∀ q r, f (-((n + 1 : ℕ) : ℤ)) q (r + 1) = -f (-((n + 1 : ℕ) : ℤ)) (q + 1) r := by
        intro q r
        have h := hpas (-((n + 1 : ℕ) : ℤ)) q r
        rw [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring, ih] at h
        exact eq_neg_of_add_eq_zero_right h.symm
      intro q r
      induction r generalizing q with
      | zero => exact hcomm _ q
      | succ r ihr => rw [hg, ihr, neg_zero]
      | pred r ihr =>
        have h := hg (q - 1) (-(r : ℤ) - 1)
        rw [show -(r : ℤ) - 1 + 1 = -(r : ℤ) by ring, ihr, show q - 1 + 1 = q by ring] at h
        exact neg_eq_zero.1 h.symm
  intro p q r
  rcases Int.eq_nat_or_neg p with ⟨n, rfl | rfl⟩
  · exact hpos n q r
  · exact hneg n q r

/-! ## Mode algebras -/

/-- A `BorcherdsVertexAlgebra` without the Borcherds identity: modes, vacuum, an `ℕ`-grading
of CFT type with the weight rule and truncation, and the vacuum axioms. -/
structure ModeAlgebra (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] where
  /-- `mode n a b = a_(n) b`. -/
  mode : ℤ → V →ₗ[k] V →ₗ[k] V
  /-- The vacuum vector. -/
  vac : V
  /-- The conformal-weight grading. -/
  grade : ℕ → Submodule k V
  grade_internal : DirectSum.IsInternal grade
  grade_zero : grade 0 = k ∙ vac
  mode_grade : ∀ {i j : ℕ} {a b : V} (n : ℤ), a ∈ grade i → b ∈ grade j →
    n + 1 ≤ (i : ℤ) + j → mode n a b ∈ grade ((i : ℤ) + j - n - 1).toNat
  mode_trunc : ∀ {i j : ℕ} {a b : V} (n : ℤ), a ∈ grade i → b ∈ grade j →
    (i : ℤ) + j ≤ n → mode n a b = 0
  vac_mode : ∀ (n : ℤ) (b : V), mode n vac b = if n = -1 then b else 0
  mode_vac_nonneg : ∀ (n : ℤ) (a : V), 0 ≤ n → mode n a vac = 0
  mode_vac_neg_one : ∀ a : V, mode (-1) a vac = a

namespace ModeAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (M : ModeAlgebra k V)

theorem vac_mem : M.vac ∈ M.grade 0 := by
  rw [M.grade_zero]
  exact Submodule.mem_span_singleton_self _

/-- The left side of the Borcherds identity with range `N`. -/
def bL (a b c : V) (p q r : ℤ) (N : ℕ) : V :=
  ∑ t ∈ Finset.range N, zbinom k p t • M.mode (p + q - t) (M.mode (r + t) a b) c

/-- The right side of the Borcherds identity with range `N`. -/
def bR (a b c : V) (p q r : ℤ) (N : ℕ) : V :=
  ∑ t ∈ Finset.range N, ((-1 : k) ^ t * zbinom k r t) •
    (M.mode (p + r - t) a (M.mode (q + t) b c) -
      (-1 : k) ^ r • M.mode (q + r - t) b (M.mode (p + t) a c))

/-- The range of `BorcherdsVertexAlgebra.borcherds`. -/
def bN (i j l : ℕ) (p q r : ℤ) : ℕ := i + j + l + p.natAbs + q.natAbs + r.natAbs + 1

/-- The Borcherds defect of homogeneous `a ∈ V_i`, `b ∈ V_j`, `c ∈ V_l`. -/
def bD (i j l : ℕ) (a b c : V) (p q r : ℤ) : V :=
  M.bL a b c p q r (bN i j l p q r) - M.bR a b c p q r (bN i j l p q r)

def X (a b c : V) : ℤ → ℤ → V := fun u v => M.mode v (M.mode u a b) c
def Y (a b c : V) : ℤ → ℤ → V := fun u v => M.mode u a (M.mode v b c)
def Z (a b c : V) : ℤ → ℤ → V := fun u v => M.mode u b (M.mode v a c)

theorem bL_eq_lsum (a b c : V) (p q r : ℤ) (N : ℕ) :
    M.bL a b c p q r N = lsum k (M.X a b c) p q r N := rfl

theorem bR_eq_ysum (a b c : V) (p q r : ℤ) (N : ℕ) :
    M.bR a b c p q r N =
      ysum k (M.Y a b c) p q r N - (-1 : k) ^ r • ysum k (M.Z a b c) q p r N := by
  unfold bR ysum Y Z
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  module

/-! ### Stability of the ranges -/

theorem bL_stable {i j : ℕ} {a b : V} (ha : a ∈ M.grade i) (hb : b ∈ M.grade j) (c : V)
    (p q r : ℤ) {N N' : ℕ} (hN : i + j + r.natAbs ≤ N) (hN' : i + j + r.natAbs ≤ N') :
    M.bL a b c p q r N = M.bL a b c p q r N' :=
  sum_range_eq_of_vanish _ (fun t ht => by
    rw [M.mode_trunc (r + (t : ℤ)) ha hb (by omega), map_zero, LinearMap.zero_apply,
      smul_zero]) hN hN'

theorem bR_stable {i j l : ℕ} {a b c : V} (ha : a ∈ M.grade i) (hb : b ∈ M.grade j)
    (hc : c ∈ M.grade l) (p q r : ℤ) {N N' : ℕ} (hN : i + j + l + p.natAbs + q.natAbs ≤ N)
    (hN' : i + j + l + p.natAbs + q.natAbs ≤ N') :
    M.bR a b c p q r N = M.bR a b c p q r N' :=
  sum_range_eq_of_vanish _ (fun t ht => by
    rw [M.mode_trunc (q + (t : ℤ)) hb hc (by omega), M.mode_trunc (p + (t : ℤ)) ha hc (by omega)]
    simp) hN hN'

theorem ysumY_stable {j l : ℕ} {b c : V} (a : V) (hb : b ∈ M.grade j) (hc : c ∈ M.grade l)
    (p q r : ℤ) {N N' : ℕ} (hN : j + l + q.natAbs ≤ N) (hN' : j + l + q.natAbs ≤ N') :
    ysum k (M.Y a b c) p q r N = ysum k (M.Y a b c) p q r N' :=
  sum_range_eq_of_vanish _ (fun t ht => by
    show _ • M.mode _ a (M.mode (q + (t : ℤ)) b c) = 0
    rw [M.mode_trunc (q + (t : ℤ)) hb hc (by omega), map_zero, smul_zero]) hN hN'

theorem ysumZ_stable {i l : ℕ} {a c : V} (b : V) (ha : a ∈ M.grade i) (hc : c ∈ M.grade l)
    (p q r : ℤ) {N N' : ℕ} (hN : i + l + p.natAbs ≤ N) (hN' : i + l + p.natAbs ≤ N') :
    ysum k (M.Z a b c) q p r N = ysum k (M.Z a b c) q p r N' :=
  sum_range_eq_of_vanish _ (fun t ht => by
    show _ • M.mode _ b (M.mode (p + (t : ℤ)) a c) = 0
    rw [M.mode_trunc (p + (t : ℤ)) ha hc (by omega), map_zero, smul_zero]) hN hN'

/-! ### The Pascal recursion of the defect -/

theorem bD_pascal {i j l : ℕ} {a b c : V} (ha : a ∈ M.grade i) (hb : b ∈ M.grade j)
    (hc : c ∈ M.grade l) (p q r : ℤ) :
    M.bD i j l a b c (p + 1) q r = M.bD i j l a b c p (q + 1) r + M.bD i j l a b c p q (r + 1) := by
  -- the three left sides
  have hL : M.bL a b c (p + 1) q r (bN i j l (p + 1) q r) =
      M.bL a b c p (q + 1) r (bN i j l p (q + 1) r) +
        M.bL a b c p q (r + 1) (bN i j l p q (r + 1)) := by
    set N := i + j + r.natAbs + 1
    rw [M.bL_stable ha hb c (p + 1) q r (N := bN i j l (p + 1) q r) (N' := N + 1)
        (by unfold bN; omega) (by omega),
      M.bL_stable ha hb c p (q + 1) r (N := bN i j l p (q + 1) r) (N' := N + 1)
        (by unfold bN; omega) (by omega),
      M.bL_stable ha hb c p q (r + 1) (N := bN i j l p q (r + 1)) (N' := N)
        (by unfold bN; omega) (by omega)]
    exact lsum_pascal k (M.X a b c) p q r N
  -- the `Y` parts
  have hY : ysum k (M.Y a b c) (p + 1) q r (bN i j l (p + 1) q r) =
      ysum k (M.Y a b c) p (q + 1) r (bN i j l p (q + 1) r) +
        ysum k (M.Y a b c) p q (r + 1) (bN i j l p q (r + 1)) := by
    set N := j + l + q.natAbs + 1
    rw [M.ysumY_stable a hb hc (p + 1) q r (N := bN i j l (p + 1) q r) (N' := N + 1)
        (by unfold bN; omega) (by omega),
      M.ysumY_stable a hb hc p (q + 1) r (N := bN i j l p (q + 1) r) (N' := N)
        (by unfold bN; omega) (by omega),
      M.ysumY_stable a hb hc p q (r + 1) (N := bN i j l p q (r + 1)) (N' := N + 1)
        (by unfold bN; omega) (by omega),
      ysum_pascal k (M.Y a b c) p q r N]
    abel
  -- the `Z` parts
  have hZ : ysum k (M.Z a b c) q (p + 1) r (bN i j l (p + 1) q r) =
      ysum k (M.Z a b c) (q + 1) p r (bN i j l p (q + 1) r) -
        ysum k (M.Z a b c) q p (r + 1) (bN i j l p q (r + 1)) := by
    set N := i + l + p.natAbs + 1
    rw [M.ysumZ_stable b ha hc (p + 1) q r (N := bN i j l (p + 1) q r) (N' := N)
        (by unfold bN; omega) (by omega),
      M.ysumZ_stable b ha hc p (q + 1) r (N := bN i j l p (q + 1) r) (N' := N + 1)
        (by unfold bN; omega) (by omega),
      M.ysumZ_stable b ha hc p q (r + 1) (N := bN i j l p q (r + 1)) (N' := N + 1)
        (by unfold bN; omega) (by omega),
      ysum_pascal k (M.Z a b c) q p r N]
    abel
  have hs : (-1 : k) ^ (r + 1) = -(-1 : k) ^ r := by
    rw [zpow_add_one₀ (by norm_num : (-1 : k) ≠ 0)]
    ring
  unfold bD
  rw [M.bR_eq_ysum, M.bR_eq_ysum, M.bR_eq_ysum, hL, hY, hZ, hs]
  module

/-- **The Borcherds identity from the commutator and iterate families.** -/
theorem bD_eq_zero_of_comm_iter {i j l : ℕ} {a b c : V} (ha : a ∈ M.grade i)
    (hb : b ∈ M.grade j) (hc : c ∈ M.grade l) (hcomm : ∀ p q, M.bD i j l a b c p q 0 = 0)
    (hiter : ∀ q r, M.bD i j l a b c 0 q r = 0) : ∀ p q r, M.bD i j l a b c p q r = 0 :=
  eq_zero_of_pascal (fun p q r => M.bD i j l a b c p q r) (M.bD_pascal ha hb hc) hcomm hiter

/-! ## The vacuum -/

theorem vac_bL_comm (b c : V) (p q : ℤ) (N : ℕ) : M.bL M.vac b c p q 0 N = 0 :=
  Finset.sum_eq_zero fun t _ => by
    rw [M.vac_mode, if_neg (by omega), map_zero, LinearMap.zero_apply, smul_zero]

theorem vac_bR_comm (b c : V) (p q : ℤ) {N : ℕ} (hN : 0 < N) : M.bR M.vac b c p q 0 N = 0 := by
  unfold bR
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.cast_zero, add_zero, sub_zero, M.vac_mode, zbinom_zero_right, pow_zero,
      mul_one, one_smul, zpow_zero]
    split_ifs <;> simp
  · intro t _ ht
    rw [zbinom_zero_left_of_pos k (Nat.pos_of_ne_zero ht), mul_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_range.2 hN) h

theorem vac_iter (b c : V) (q r : ℤ) {N : ℕ} (hN : 0 < N) :
    M.bL M.vac b c 0 q r N = M.bR M.vac b c 0 q r N := by
  have hL : M.bL M.vac b c 0 q r N = if r = -1 then M.mode q b c else 0 := by
    unfold bL
    rw [Finset.sum_eq_single 0]
    · simp only [Nat.cast_zero, add_zero, sub_zero, zero_add, zbinom_zero_right, one_smul,
        M.vac_mode]
      split_ifs <;> simp
    · intro t _ ht
      rw [zbinom_zero_left_of_pos k (Nat.pos_of_ne_zero ht), zero_smul]
    · intro h
      exact absurd (Finset.mem_range.2 hN) h
  have hR : M.bR M.vac b c 0 q r N = if r = -1 then M.mode q b c else 0 := by
    unfold bR
    have h2 : ∀ t : ℕ, M.mode (0 + (t : ℤ)) M.vac c = 0 := fun t => by
      rw [M.vac_mode, if_neg (by omega)]
    simp only [h2, map_zero, smul_zero, sub_zero]
    split_ifs with hr
    · subst hr
      rw [Finset.sum_eq_single 0]
      · simp [M.vac_mode, zbinom_zero_right]
      · intro t _ ht
        rw [M.vac_mode, if_neg (by omega), smul_zero]
      · intro h
        exact absurd (Finset.mem_range.2 hN) h
    · refine Finset.sum_eq_zero fun t _ => ?_
      rw [M.vac_mode]
      split_ifs with ht
      · have hr' : r = ((t - 1 : ℕ) : ℤ) := by omega
        rw [hr', zbinom_natCast_of_lt k (by omega), mul_zero, zero_smul]
      · rw [smul_zero]
  rw [hL, hR]

theorem bN_pos (i j l : ℕ) (p q r : ℤ) : 0 < bN i j l p q r := by
  unfold bN
  omega

/-- **The Borcherds identity for the vacuum**, `(𝟏, b, c)`, all `p, q, r`. -/
theorem bD_vac {j l : ℕ} {b c : V} (hb : b ∈ M.grade j) (hc : c ∈ M.grade l) :
    ∀ p q r, M.bD 0 j l M.vac b c p q r = 0 :=
  M.bD_eq_zero_of_comm_iter M.vac_mem hb hc
    (fun p q => by
      unfold bD
      rw [M.vac_bL_comm, M.vac_bR_comm b c p q (bN_pos 0 j l p q 0), sub_zero])
    (fun q r => by
      unfold bD
      rw [M.vac_iter b c q r (bN_pos 0 j l 0 q r), sub_self])

/-! ## `Good` vectors -/

/-- `Good a`: the Borcherds identity holds for `(a, b, c)` for all homogeneous `b`, `c` and all
`p, q, r`, with every sufficiently large summation range. -/
def Good (a : V) : Prop :=
  ∀ {j l : ℕ} {b c : V}, b ∈ M.grade j → c ∈ M.grade l → ∀ p q r : ℤ,
    ∃ N₀ : ℕ, ∀ N ≥ N₀, M.bL a b c p q r N = M.bR a b c p q r N

/-- For homogeneous `a`, `Good a` is the Borcherds identity in the form of
`BorcherdsVertexAlgebra.borcherds`. -/
theorem good_iff_bD {i : ℕ} {a : V} (ha : a ∈ M.grade i) :
    M.Good a ↔ ∀ {j l : ℕ} {b c : V}, b ∈ M.grade j → c ∈ M.grade l →
      ∀ p q r, M.bD i j l a b c p q r = 0 := by
  constructor
  · intro h j l b c hb hc p q r
    obtain ⟨N₀, hN₀⟩ := h hb hc p q r
    have e := hN₀ (max N₀ (bN i j l p q r)) (le_max_left _ _)
    unfold bD
    rw [M.bL_stable ha hb c p q r (N := bN i j l p q r) (N' := max N₀ (bN i j l p q r))
        (by unfold bN; omega) (by unfold bN; omega),
      M.bR_stable ha hb hc p q r (N := bN i j l p q r) (N' := max N₀ (bN i j l p q r))
        (by unfold bN; omega) (by unfold bN; omega), e, sub_self]
  · intro h j l b c hb hc p q r
    refine ⟨bN i j l p q r, fun N hN => ?_⟩
    have e := sub_eq_zero.1 (h hb hc p q r)
    rw [M.bL_stable ha hb c p q r (N := N) (N' := bN i j l p q r) (by unfold bN at hN; omega)
        (by unfold bN; omega),
      M.bR_stable ha hb hc p q r (N := N) (N' := bN i j l p q r) (by unfold bN at hN; omega)
        (by unfold bN; omega)]
    exact e

theorem good_vac : M.Good M.vac :=
  (M.good_iff_bD M.vac_mem).2 fun hb hc p q r => M.bD_vac hb hc p q r

/-! ### Linearity in the first argument -/

theorem bL_add (a a' b c : V) (p q r : ℤ) (N : ℕ) :
    M.bL (a + a') b c p q r N = M.bL a b c p q r N + M.bL a' b c p q r N := by
  simp only [bL, map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib]

theorem bR_add (a a' b c : V) (p q r : ℤ) (N : ℕ) :
    M.bR (a + a') b c p q r N = M.bR a b c p q r N + M.bR a' b c p q r N := by
  simp only [bR, map_add, LinearMap.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  module

theorem bL_smul (μ : k) (a b c : V) (p q r : ℤ) (N : ℕ) :
    M.bL (μ • a) b c p q r N = μ • M.bL a b c p q r N := by
  simp only [bL, map_smul, LinearMap.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [smul_comm]

theorem bR_smul (μ : k) (a b c : V) (p q r : ℤ) (N : ℕ) :
    M.bR (μ • a) b c p q r N = μ • M.bR a b c p q r N := by
  simp only [bR, map_smul, LinearMap.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  module

theorem bL_zero (b c : V) (p q r : ℤ) (N : ℕ) : M.bL 0 b c p q r N = 0 := by
  simp [bL]

theorem bR_zero (b c : V) (p q r : ℤ) (N : ℕ) : M.bR 0 b c p q r N = 0 := by
  simp [bR]

/-- The `Good` vectors form a subspace. -/
def goodSub : Submodule k V where
  carrier := {a | M.Good a}
  zero_mem' := fun _ _ _ _ _ => ⟨0, fun N _ => by rw [M.bL_zero, M.bR_zero]⟩
  add_mem' := by
    intro a a' ha ha' j l b c hb hc p q r
    obtain ⟨N₁, h₁⟩ := ha hb hc p q r
    obtain ⟨N₂, h₂⟩ := ha' hb hc p q r
    refine ⟨max N₁ N₂, fun N hN => ?_⟩
    rw [M.bL_add, M.bR_add, h₁ N (le_of_max_le_left hN), h₂ N (le_of_max_le_right hN)]
  smul_mem' := by
    intro μ a ha j l b c hb hc p q r
    obtain ⟨N₁, h₁⟩ := ha hb hc p q r
    refine ⟨N₁, fun N hN => ?_⟩
    rw [M.bL_smul, M.bR_smul, h₁ N hN]

theorem mem_goodSub {a : V} : a ∈ M.goodSub ↔ M.Good a := Iff.rfl

/-! ## Generation -/

/-- Closure of `Good` under `n`-th products (the open part of the milestone):
`Good a ∧ Good w ⇒ Good (a_(n) w)` for homogeneous `a`. -/
def ProductClosed : Prop :=
  ∀ {i : ℕ} {a : V}, a ∈ M.grade i → M.Good a → ∀ w, M.Good w → ∀ n, M.Good (M.mode n a w)

/-- Closure of `Good` under `g_(n) -` for the generators `g ∈ G`. -/
def ProductClosedFor (G : Set V) : Prop :=
  ∀ g ∈ G, ∀ n : ℤ, ∀ w, M.Good w → M.Good (M.mode n g w)

theorem productClosedFor_of_productClosed (hP : M.ProductClosed) {G : Set V}
    (hhom : ∀ g ∈ G, ∃ i, g ∈ M.grade i) (hgood : ∀ g ∈ G, M.Good g) : M.ProductClosedFor G :=
  fun g hg n w hw => by
    obtain ⟨i, hi⟩ := hhom g hg
    exact hP hi (hgood g hg) w hw n

/-- **Generation.**  If `V` is generated from `𝟏` by the modes of the generators `G` and `Good`
is closed under `g_(n) -` for `g ∈ G`, then every vector is `Good`. -/
theorem goodSub_eq_top {G : Set V} (hclosed : M.ProductClosedFor G)
    (hgen : ∀ W : Submodule k V, M.vac ∈ W → (∀ g ∈ G, ∀ n : ℤ, ∀ w ∈ W, M.mode n g w ∈ W) →
      W = ⊤) : M.goodSub = ⊤ :=
  hgen M.goodSub M.good_vac fun g hg n w hw => hclosed g hg n w hw

/-- The Borcherds identity in the form of `BorcherdsVertexAlgebra.borcherds`, from generation. -/
theorem borcherds_of_generation {G : Set V} (hclosed : M.ProductClosedFor G)
    (hgen : ∀ W : Submodule k V, M.vac ∈ W → (∀ g ∈ G, ∀ n : ℤ, ∀ w ∈ W, M.mode n g w ∈ W) →
      W = ⊤)
    {i j l : ℕ} {a b c : V} (ha : a ∈ M.grade i) (hb : b ∈ M.grade j) (hc : c ∈ M.grade l)
    (p q r : ℤ) : M.bL a b c p q r (bN i j l p q r) = M.bR a b c p q r (bN i j l p q r) := by
  have hgood : M.Good a := by
    have h := M.goodSub_eq_top hclosed hgen
    rw [← M.mem_goodSub, h]
    exact Submodule.mem_top
  exact sub_eq_zero.1 ((M.good_iff_bD ha).1 hgood hb hc p q r)

end ModeAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.eq_zero_of_pascal
#print axioms HaagerupIzumi.C8.ModeAlgebra.bD_pascal
#print axioms HaagerupIzumi.C8.ModeAlgebra.bD_eq_zero_of_comm_iter
#print axioms HaagerupIzumi.C8.ModeAlgebra.bD_vac
#print axioms HaagerupIzumi.C8.ModeAlgebra.good_iff_bD
#print axioms HaagerupIzumi.C8.ModeAlgebra.goodSub_eq_top
#print axioms HaagerupIzumi.C8.ModeAlgebra.borcherds_of_generation
