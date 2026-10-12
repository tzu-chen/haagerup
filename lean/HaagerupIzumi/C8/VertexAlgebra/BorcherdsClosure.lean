module

public import HaagerupIzumi.C8.VertexAlgebra.BorcherdsReduce
public import Mathlib.Algebra.Module.Submodule.EqLocus

@[expose] public section

/-!
# Toward closure of the Borcherds identity under `n`-th products

W3, first milestone, item (1) (`Lattice/W3_PLAN.md`): partial results.  For a `ModeAlgebra`
(`VertexAlgebra/BorcherdsReduce.lean`):

* `eq_zero_of_pascal_faces`, `bD_eq_zero_of_weak`: the Borcherds identity for `(a, b, c)` also
  follows from the two "weak" faces, **weak commutativity** (`r ≥ i + j`, where the left side
  vanishes) and **weak associativity** (`p ≥ i + l`, where the term `b_(q+r-t) a_(p+t) c`
  vanishes).  This is the form used by the Dong-lemma proof of closure (H. Li, *Local systems
  of vertex operators, vertex superalgebras and modules*, J. Pure Appl. Algebra 109 (1996), and
  Lepowsky–Li, *Introduction to vertex operator algebras and their representations*, Ch. 3 and
  Ch. 5, section numbers from memory; Kac, *Vertex algebras for beginners*, 2nd ed., Lemma 3.2
  (Dong's lemma) and §4.8, numbering checked only against citations in the literature);
* `ext_grade`, `commutator_of_good`: for `Good a` the commutator formula
  `[a_(m), b_(n)] c = ∑_t (m choose t) (a_(t) b)_(m+n-t) c` holds for all `c` (operator form);
* `ProductClosedHom`: closure under `n`-th products of **homogeneous** `Good` vectors, the form
  in which (1) is needed; `goodSub_eq_top_of_hom`: generation from homogeneous generators only
  needs `ProductClosedHom`.

Nothing here is an external hypothesis.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

/-- **Reduction to the weak faces.**  A function `f : ℤ³ → W` with
`f(p+1, q, r) = f(p, q+1, r) + f(p, q, r+1)` vanishes identically as soon as it vanishes for
`r ≥ R` (all `p, q`) and for `p ≥ P` (all `q, r`). -/
theorem eq_zero_of_pascal_faces {W : Type*} [AddCommGroup W] (f : ℤ → ℤ → ℤ → W)
    (hpas : ∀ p q r, f (p + 1) q r = f p (q + 1) r + f p q (r + 1)) (R P : ℤ)
    (hR : ∀ p q r, R ≤ r → f p q r = 0) (hP : ∀ p q r, P ≤ p → f p q r = 0) :
    ∀ p q r, f p q r = 0 := by
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
  have hn : ∀ n : ℕ, ∀ q r, f (P - n) q r = 0 := by
    intro n
    induction n with
    | zero => intro q r; exact hP _ q r (by simp)
    | succ n ih =>
      refine step _ fun q r => ?_
      rw [show P - ((n + 1 : ℕ) : ℤ) + 1 = P - n by push_cast; ring]
      exact ih q r
  intro p q r
  by_cases h : P ≤ p
  · exact hP p q r h
  · have := hn (P - p).toNat q r
    rwa [show P - ((P - p).toNat : ℤ) = p by omega] at this

namespace ModeAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (M : ModeAlgebra k V)

/-- The left side vanishes for `r ≥ i + j`. -/
theorem bL_eq_zero_of_le {i j : ℕ} {a b : V} (ha : a ∈ M.grade i) (hb : b ∈ M.grade j)
    (c : V) (p q r : ℤ) (hr : (i : ℤ) + j ≤ r) (N : ℕ) : M.bL a b c p q r N = 0 :=
  Finset.sum_eq_zero fun t _ => by
    rw [M.mode_trunc (r + (t : ℤ)) ha hb (by omega), map_zero, LinearMap.zero_apply, smul_zero]

/-- **The Borcherds identity from weak commutativity and weak associativity.** -/
theorem bD_eq_zero_of_weak {i j l : ℕ} {a b c : V} (ha : a ∈ M.grade i) (hb : b ∈ M.grade j)
    (hc : c ∈ M.grade l)
    (hcomm : ∀ p q r, (i : ℤ) + j ≤ r → M.bR a b c p q r (bN i j l p q r) = 0)
    (hassoc : ∀ p q r, (i : ℤ) + l ≤ p → M.bD i j l a b c p q r = 0) :
    ∀ p q r, M.bD i j l a b c p q r = 0 :=
  eq_zero_of_pascal_faces (fun p q r => M.bD i j l a b c p q r) (M.bD_pascal ha hb hc)
    ((i : ℤ) + j) ((i : ℤ) + l)
    (fun p q r hr => by
      show M.bL a b c p q r _ - M.bR a b c p q r _ = 0
      rw [M.bL_eq_zero_of_le ha hb c p q r hr, hcomm p q r hr, sub_zero])
    hassoc

/-! ## The commutator formula in operator form -/

/-- Two linear maps out of `V` agreeing on every graded piece are equal. -/
theorem ext_grade {W : Type*} [AddCommGroup W] [Module k W] {f g : V →ₗ[k] W}
    (h : ∀ l, ∀ c ∈ M.grade l, f c = g c) : f = g := by
  have htop : (⊤ : Submodule k V) ≤ LinearMap.eqLocus f g := by
    rw [← M.grade_internal.submodule_iSup_eq_top]
    exact iSup_le fun l c hc => LinearMap.mem_eqLocus.2 (h l c hc)
  exact LinearMap.ext fun c => LinearMap.mem_eqLocus.1 (htop Submodule.mem_top)

theorem commutator_of_bD {i j l : ℕ} {a b c : V} (ha : a ∈ M.grade i) (hb : b ∈ M.grade j)
    (m n : ℤ) (hD : M.bD i j l a b c m n 0 = 0) :
    M.mode m a (M.mode n b c) - M.mode n b (M.mode m a c) =
      ∑ t ∈ Finset.range (i + j), zbinom k m t • M.mode (m + n - t) (M.mode t a b) c := by
  have h : M.bL a b c m n 0 (bN i j l m n 0) = M.bR a b c m n 0 (bN i j l m n 0) :=
    sub_eq_zero.1 hD
  have hR : M.bR a b c m n 0 (bN i j l m n 0) =
      M.mode m a (M.mode n b c) - M.mode n b (M.mode m a c) := by
    unfold bR
    rw [Finset.sum_eq_single 0]
    · simp [zbinom_zero_right]
    · intro t _ ht
      rw [zbinom_zero_left_of_pos k (Nat.pos_of_ne_zero ht), mul_zero, zero_smul]
    · intro h0
      exact absurd (Finset.mem_range.2 (bN_pos i j l m n 0)) h0
  rw [← hR, ← h]
  unfold bL
  exact sum_range_congr_of_vanish (fun t => by rw [zero_add]) (fun t ht => by
    rw [M.mode_trunc (t : ℤ) ha hb (by omega), map_zero, LinearMap.zero_apply, smul_zero])
    (by unfold bN; omega) le_rfl

/-- **Commutator formula for a `Good` vector**, in operator form:
`[a_(m), b_(n)] = ∑_t (m choose t) (a_(t) b)_(m+n-t)` for homogeneous `b`, on all of `V`. -/
theorem commutator_of_good {i j : ℕ} {a b : V} (ha : a ∈ M.grade i) (hgood : M.Good a)
    (hb : b ∈ M.grade j) (m n : ℤ) (c : V) :
    M.mode m a (M.mode n b c) - M.mode n b (M.mode m a c) =
      ∑ t ∈ Finset.range (i + j), zbinom k m t • M.mode (m + n - t) (M.mode t a b) c := by
  have key : (M.mode m a).comp (M.mode n b) - (M.mode n b).comp (M.mode m a) =
      ∑ t ∈ Finset.range (i + j), zbinom k m t • M.mode (m + n - t) (M.mode t a b) :=
    M.ext_grade fun l c hc => by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smul_apply]
      exact M.commutator_of_bD ha hb m n ((M.good_iff_bD ha).1 hgood hb hc m n 0)
  have := LinearMap.congr_fun key c
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply] using this

/-! ## Generation from homogeneous closure -/

/-- Closure of `Good` under `n`-th products of **homogeneous** vectors (milestone item (1), in
the form needed for generation). -/
def ProductClosedHom : Prop :=
  ∀ {i m : ℕ} {a w : V}, a ∈ M.grade i → M.Good a → w ∈ M.grade m → M.Good w →
    ∀ n, M.Good (M.mode n a w)

theorem productClosedHom_of_productClosed (h : M.ProductClosed) : M.ProductClosedHom :=
  fun ha hga _ hgw n => h ha hga _ hgw n

/-- `a_(n) w` is homogeneous for homogeneous `a`, `w`. -/
theorem mode_mem_some_grade {i m : ℕ} {a w : V} (ha : a ∈ M.grade i) (hw : w ∈ M.grade m)
    (n : ℤ) : ∃ e, M.mode n a w ∈ M.grade e := by
  by_cases hn : n + 1 ≤ (i : ℤ) + m
  · exact ⟨_, M.mode_grade n ha hw hn⟩
  · exact ⟨0, by rw [M.mode_trunc n ha hw (by omega)]; exact Submodule.zero_mem _⟩

/-- The span of the homogeneous `Good` vectors. -/
def homGoodSub : Submodule k V :=
  Submodule.span k {w | (∃ m, w ∈ M.grade m) ∧ M.Good w}

theorem homGoodSub_le : M.homGoodSub ≤ M.goodSub :=
  Submodule.span_le.2 fun _ hw => hw.2

/-- **Generation from homogeneous generators.**  If the generators `G` are homogeneous and
`Good`, `Good` is closed under products of homogeneous vectors (`ProductClosedHom`), and `V` is
generated from `𝟏` by the modes of `G`, then every vector is `Good`. -/
theorem goodSub_eq_top_of_hom {G : Set V} (hG : ∀ g ∈ G, (∃ i, g ∈ M.grade i) ∧ M.Good g)
    (hP : M.ProductClosedHom)
    (hgen : ∀ W : Submodule k V, M.vac ∈ W → (∀ g ∈ G, ∀ n : ℤ, ∀ w ∈ W, M.mode n g w ∈ W) →
      W = ⊤) : M.goodSub = ⊤ := by
  have htop : M.homGoodSub = ⊤ := by
    refine hgen _ (Submodule.subset_span ⟨⟨0, M.vac_mem⟩, M.good_vac⟩) ?_
    intro g hg n w hw
    obtain ⟨⟨i, hgi⟩, hgg⟩ := hG g hg
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨m, hxm⟩, hxg⟩ := hx
      exact Submodule.subset_span ⟨M.mode_mem_some_grade hgi hxm n, hP hgi hgg hxm hxg n⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul μ x _ hx => rw [map_smul]; exact Submodule.smul_mem _ μ hx
  rw [eq_top_iff, ← htop]
  exact M.homGoodSub_le

end ModeAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.eq_zero_of_pascal_faces
#print axioms HaagerupIzumi.C8.ModeAlgebra.bD_eq_zero_of_weak
#print axioms HaagerupIzumi.C8.ModeAlgebra.commutator_of_good
#print axioms HaagerupIzumi.C8.ModeAlgebra.goodSub_eq_top_of_hom
