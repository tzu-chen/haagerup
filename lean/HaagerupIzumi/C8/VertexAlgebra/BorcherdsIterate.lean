module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsVandermonde
public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsClosure

@[expose] public section

/-!
# Locality and the iterate formula for a `Good` vector; `Good` from locality plus iterate

W3, item (1), step (i) of `Lattice/W3_PLAN.md`.  For a `ModeAlgebra` and a homogeneous `Good`
vector `a ∈ V_i` (`VertexAlgebra/BorcherdsReduce.lean`):

* **locality** (`locality_of_good`): for every homogeneous `b ∈ V_j` and every `R ≥ i + j`,
  `(z₁ - z₂)^R [Y(a, z₁), Y(b, z₂)] = 0` on all of `V`, in the mode form
  `dz k R (comm a b c) p q = 0` (`VertexAlgebra/BorcherdsVandermonde.lean`); and the same for
  `(b, a)` (`locality_swap_of_good`);
* **the iterate formula** (`iterate_of_good`, on homogeneous `c` with an explicit range;
  `iterate_op_of_good`, operator form for `r = R ≥ 0`):
  `(a_(r) b)_(q) = ∑_t (-1)^t (r choose t) (a_(r-t) b_(q+t) - (-1)^r b_(q+r-t) a_(t))`.

Conversely (**a third reduction**, besides `bD_eq_zero_of_comm_iter` and `bD_eq_zero_of_weak`):

* `eq_zero_of_pascal_iter_face`: a function on `ℤ³` with the Pascal recursion vanishes as soon as
  it vanishes on the iterate family `p = 0` and on a locality face `r ≥ R`;
* `bD_eq_zero_of_local_iter`, `good_of_local_iter`: **`Good x` follows from locality of `x` with
  every homogeneous `b` (of some order) and the iterate formula for `x`.**  So closure under
  `n`-th products (item (1)) reduces to Dong's lemma (locality of `a_(n) w`) and the iterate
  formula for `a_(n) w`.

The binomial manipulations follow the formal-calculus arguments of Kac, *Vertex algebras for
beginners*, and Lepowsky–Li, *Introduction to vertex operator algebras and their
representations*, translated to modes; see `Lattice/W3_PLAN.md` for the references and for
which section numbers were checked.

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

/-- **Reduction to the iterate family and a locality face.**  A function `f : ℤ³ → W` with
`f(p+1, q, r) = f(p, q+1, r) + f(p, q, r+1)` vanishes identically as soon as `f(0, q, r) = 0`
for all `q, r` and `f(p, q, r) = 0` for `r ≥ R`. -/
theorem eq_zero_of_pascal_iter_face {W : Type*} [AddCommGroup W] (f : ℤ → ℤ → ℤ → W)
    (hpas : ∀ p q r, f (p + 1) q r = f p (q + 1) r + f p q (r + 1)) (R : ℤ)
    (hR : ∀ p q r, R ≤ r → f p q r = 0) (hiter : ∀ q r, f 0 q r = 0) :
    ∀ p q r, f p q r = 0 := by
  -- downward step in `p`, using the face
  have step : ∀ p, (∀ q r, f (p + 1) q r = 0) → ∀ q r, f p q r = 0 := by
    intro p hp1
    have hrec : ∀ q r, f p q r = -f p (q - 1) (r + 1) := by
      intro q r
      have h := hpas p (q - 1) r
      rw [hp1, sub_add_cancel] at h
      exact eq_neg_of_add_eq_zero_left h.symm
    have hm : ∀ m : ℕ, ∀ q, f p q (R - m) = 0 := by
      intro m
      induction m with
      | zero => intro q; exact hR p q _ (by simp)
      | succ m ih =>
        intro q
        rw [hrec, show R - ((m + 1 : ℕ) : ℤ) + 1 = R - m by push_cast; ring, ih, neg_zero]
    intro q r
    by_cases h : R ≤ r
    · exact hR p q r h
    · have := hm (R - r).toNat q
      rwa [show R - ((R - r).toNat : ℤ) = r by omega] at this
  -- upward in `p` from the iterate family
  have hpos : ∀ n : ℕ, ∀ q r, f n q r = 0 := by
    intro n
    induction n with
    | zero => exact hiter
    | succ n ih =>
      intro q r
      have h := hpas n q r
      push_cast
      rw [h, ih, ih, add_zero]
  -- downward in `p`
  have hneg : ∀ n : ℕ, ∀ q r, f (-(n : ℤ)) q r = 0 := by
    intro n
    induction n with
    | zero => intro q r; simpa using hiter q r
    | succ n ih =>
      refine step _ fun q r => ?_
      rw [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by push_cast; ring]
      exact ih q r
  intro p q r
  rcases Int.eq_nat_or_neg p with ⟨n, rfl | rfl⟩
  · exact hpos n q r
  · exact hneg n q r

namespace ModeAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (M : ModeAlgebra k V)

/-! ## Locality of a `Good` vector -/

/-- Locality of order `R` of `a` with `b` on homogeneous `c`, from `Good a` (`R ≥ i + j`). -/
theorem locality_hom {i j l : ℕ} {a b c : V} (ha : a ∈ M.grade i) (hgood : M.Good a)
    (hb : b ∈ M.grade j) (hc : c ∈ M.grade l) {R : ℕ} (hR : i + j ≤ R) (p q : ℤ) :
    dz k R (M.comm a b c) p q = 0 := by
  obtain ⟨N₀, hN₀⟩ := hgood hb hc p q R
  have h := hN₀ (max N₀ (R + 1)) (le_max_left _ _)
  rw [M.bL_eq_zero_of_le ha hb c p q R (by omega),
    M.bR_eq_dz a b c p q R (le_max_right _ _)] at h
  exact h.symm

/-- **Locality of a `Good` vector**: `(z₁ - z₂)^R [Y(a, z₁), Y(b, z₂)] = 0` on all of `V` for
`R ≥ i + j`. -/
theorem locality_of_good {i j : ℕ} {a b : V} (ha : a ∈ M.grade i) (hgood : M.Good a)
    (hb : b ∈ M.grade j) {R : ℕ} (hR : i + j ≤ R) (p q : ℤ) (c : V) :
    dz k R (M.comm a b c) p q = 0 := by
  have key : dz k R (fun u v => (M.mode u a).comp (M.mode v b) - (M.mode v b).comp (M.mode u a))
      p q = 0 :=
    M.ext_grade fun l c hc => by
      rw [dz_linearMap_apply, LinearMap.zero_apply]
      exact M.locality_hom ha hgood hb hc hR p q
  have h := LinearMap.congr_fun key c
  rw [dz_linearMap_apply, LinearMap.zero_apply] at h
  exact h

/-- Locality of `b` with a `Good` vector `a` (the variables exchanged). -/
theorem locality_swap_of_good {i j : ℕ} {a b : V} (ha : a ∈ M.grade i) (hgood : M.Good a)
    (hb : b ∈ M.grade j) {R : ℕ} (hR : i + j ≤ R) (p q : ℤ) (c : V) :
    dz k R (M.comm b a c) q p = 0 := by
  have h := dz_swap k R (M.comm a b c) p q
  rw [M.locality_of_good ha hgood hb hR p q c, smul_zero] at h
  have e : dz k R (M.comm b a c) q p = -dz k R (fun u v => M.comm a b c v u) q p := by
    rw [← dz_neg_fun]
    congr 1
    funext u v
    simp only [comm]
    abel
  rw [e, h, neg_zero]

/-! ## The iterate formula for a `Good` vector -/

/-- **The iterate formula** on homogeneous `c`, with any range `N ≥ i + j + l + |q|`. -/
theorem iterate_of_good {i j l : ℕ} {a b c : V} (ha : a ∈ M.grade i) (hgood : M.Good a)
    (hb : b ∈ M.grade j) (hc : c ∈ M.grade l) (q r : ℤ) {N : ℕ}
    (hN : i + j + l + q.natAbs ≤ N) :
    M.mode q (M.mode r a b) c = ∑ t ∈ Finset.range N, ((-1 : k) ^ t * zbinom k r t) •
      (M.mode (r - t) a (M.mode (q + t) b c) -
        (-1 : k) ^ r • M.mode (q + r - t) b (M.mode t a c)) := by
  have h : M.bL a b c 0 q r (bN i j l 0 q r) = M.bR a b c 0 q r (bN i j l 0 q r) :=
    sub_eq_zero.1 ((M.good_iff_bD ha).1 hgood hb hc 0 q r)
  have hL : M.bL a b c 0 q r (bN i j l 0 q r) = M.mode q (M.mode r a b) c := by
    unfold bL
    rw [sum_range_eq_zero_term (bN_pos i j l 0 q r) (fun t ht => by
      rw [zbinom_zero_left_of_pos k (by omega), zero_smul])]
    simp [zbinom_zero_right]
  rw [← hL, h, M.bR_stable ha hb hc 0 q r (N := bN i j l 0 q r) (N' := N)
    (by unfold bN; simp only [Int.natAbs_zero]; omega) (by simp only [Int.natAbs_zero]; omega)]
  unfold bR
  simp only [zero_add]

/-- **The iterate formula in operator form** for `r = R ≥ 0`:
`(a_(R) b)_(q) = ∑_{t ≤ R} (-1)^t (R choose t) (a_(R-t) b_(q+t) - (-1)^R b_(q+R-t) a_(t))`. -/
theorem iterate_op_of_good {i j : ℕ} {a b : V} (ha : a ∈ M.grade i) (hgood : M.Good a)
    (hb : b ∈ M.grade j) (q : ℤ) (R : ℕ) (c : V) :
    M.mode q (M.mode R a b) c = ∑ t ∈ Finset.range (R + 1), ((-1 : k) ^ t * (R.choose t : k)) •
      (M.mode ((R : ℤ) - t) a (M.mode (q + t) b c) -
        (-1 : k) ^ R • M.mode (q + R - t) b (M.mode t a c)) := by
  have key : M.mode q (M.mode R a b) = ∑ t ∈ Finset.range (R + 1),
      ((-1 : k) ^ t * (R.choose t : k)) • ((M.mode ((R : ℤ) - t) a).comp (M.mode (q + t) b) -
        (-1 : k) ^ R • (M.mode (q + R - t) b).comp (M.mode t a)) :=
    M.ext_grade fun l c hc => by
      rw [M.iterate_of_good ha hgood hb hc q R (N := max (i + j + l + q.natAbs) (R + 1))
        (le_max_left _ _)]
      rw [sum_range_eq_of_vanish _ (N₀ := R + 1) (fun t ht => by
        rw [zbinom_natCast_of_lt k (by omega), mul_zero, zero_smul]) (le_max_right _ _) le_rfl]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
        LinearMap.comp_apply, zbinom_natCast, zpow_natCast]
  have h := LinearMap.congr_fun key c
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.comp_apply] using h

/-! ## `Good` from locality and the iterate formula -/

/-- **The Borcherds identity from locality and the iterate family.** -/
theorem bD_eq_zero_of_local_iter {i j l : ℕ} {a b c : V} (ha : a ∈ M.grade i)
    (hb : b ∈ M.grade j) (hc : c ∈ M.grade l) {R : ℕ}
    (hloc : ∀ p q, dz k R (M.comm a b c) p q = 0)
    (hiter : ∀ q r, M.bD i j l a b c 0 q r = 0) : ∀ p q r, M.bD i j l a b c p q r = 0 :=
  eq_zero_of_pascal_iter_face (fun p q r => M.bD i j l a b c p q r) (M.bD_pascal ha hb hc)
    (((i + j + R : ℕ)) : ℤ)
    (fun p q r hr => by
      obtain ⟨S, hS⟩ : ∃ S : ℕ, r = (S : ℤ) := ⟨r.toNat, by omega⟩
      subst hS
      show M.bL a b c p q S _ - M.bR a b c p q S _ = 0
      rw [M.bL_eq_zero_of_le ha hb c p q S (by push_cast at hr; omega),
        M.bR_eq_dz a b c p q S (by unfold bN; simp only [Int.natAbs_natCast]; omega),
        dz_mono k (M.comm a b c) hloc (by push_cast at hr; omega) p q, sub_zero])
    hiter

/-- **`Good` from locality and the iterate formula**: if the homogeneous `x ∈ V_e` is local
(of some order) with every homogeneous `b` on every homogeneous `c`, and the iterate family of
the Borcherds identity holds for `(x, b, c)`, then `x` is `Good`. -/
theorem good_of_local_iter {e : ℕ} {x : V} (hx : x ∈ M.grade e)
    (hloc : ∀ {j l : ℕ} {b c : V}, b ∈ M.grade j → c ∈ M.grade l →
      ∃ R : ℕ, ∀ p q, dz k R (M.comm x b c) p q = 0)
    (hiter : ∀ {j l : ℕ} {b c : V}, b ∈ M.grade j → c ∈ M.grade l →
      ∀ q r, M.bD e j l x b c 0 q r = 0) : M.Good x :=
  (M.good_iff_bD hx).2 fun hb hc p q r => by
    obtain ⟨R, hR⟩ := hloc hb hc
    exact M.bD_eq_zero_of_local_iter hx hb hc hR (hiter hb hc) p q r

end ModeAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.eq_zero_of_pascal_iter_face
#print axioms HaagerupIzumi.C8.ModeAlgebra.locality_of_good
#print axioms HaagerupIzumi.C8.ModeAlgebra.locality_swap_of_good
#print axioms HaagerupIzumi.C8.ModeAlgebra.iterate_of_good
#print axioms HaagerupIzumi.C8.ModeAlgebra.iterate_op_of_good
#print axioms HaagerupIzumi.C8.ModeAlgebra.bD_eq_zero_of_local_iter
#print axioms HaagerupIzumi.C8.ModeAlgebra.good_of_local_iter
