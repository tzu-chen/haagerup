module

public import HaagerupIzumi.C8.VertexAlgebra.FilteredWick

@[expose] public section

/-!
# The recursive strong-generation criterion

Theorem `thm:recursive` (line 2147 of `c8_expanded_20260929/haagerup_c8_expanded.tex`) and the
weight-one consequence used for `U_1 = K` (line 2601).

Let `A` be a vertex algebra (interface `HaagerupIzumi.C8.VertexAlgebra`, an `ℕ`-graded vertex
algebra of CFT type over a field `k` of characteristic zero).  Let `S d ⊆ V_d` be subspaces,
with `S d = 0` for `d > h`, and let `𝒩` be the differential normal span of `⋃ d, S d`.
Write `K = S 1` and `A₂ = S 2`.  Assume

1. `x_(n) s ∈ 𝒩` for all `x ∈ S 1 ∪ S 2`, all `s ∈ S d` and all `n ≥ 0`;
2. for `3 ≤ d ≤ h`, `S d ⊆ span {a_(0) b | a ∈ S 2, b ∈ S (d-1)} + 𝒩(S 1 ∪ ⋯ ∪ S (d-1)) ∩ V_d`.

Then `𝒩` is a vertex subalgebra (`recursive_isSubalgebra`), so the `S d` strongly generate the
vertex algebra that they generate (`generated_eq_normalSpan`), and the weight-one part of that
vertex algebra is `S 1` (`normalSpan_iUnion_inf_grade_one`; more generally, for `d ≠ 0` the
weight-`d` part is `S d` plus derivatives and products of positive-weight normal elements,
`normalSpan_iUnion_inf_grade`).  The bundled statement is `recursive_strong_generation`.

Proof (manuscript lines 2160–2194).  Zero modes of `S 2` preserve `𝒩`
(`zero_mode_mem_normalSpan`: `a_(0)` is a derivation of `(-1)`-products and commutes with
`T`).  Generator pairs `(s, t)` close by a lexicographic induction on
`(wt s + wt t, wt s)` (`recursive_pairs`): left weight `≤ 2` is hypothesis 1; otherwise
hypothesis 2 writes `s = ∑ a_(0) b + r`; the remainder `r` is a combination of derivatives and
of products of positive-weight normal elements, handled by the filtered Wick lemma (b); and
`(a_(0) b)_(n) t = a_(0) (b_(n) t) - b_(n) (a_(0) t)` (commutator formula with `m = 0`), where
`a_(0) t` is a normal element of weight `wt t + 1` whose single-generator part is an earlier
lexicographic case and whose other parts are handled by the filtered Wick lemma (b).  The
filtered Wick lemma (a) then closes all nonnegative modes on `𝒩`, and negative modes follow
from `x_(-1-r) y = (r!)⁻¹ (T^r x)_(-1) y` (`neg_mode_mem`, characteristic zero).

Hypotheses 1 and 2 are the finite certificate inputs of the manuscript; nothing else is
assumed beyond the interface fields.  `[CharZero k]` is used only for negative modes.
-/

namespace HaagerupIzumi.C8

namespace VertexAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (A : VertexAlgebra k V)

/-! ### Generators given by graded subspaces -/

theorem homogeneous_iUnion {S : ℕ → Submodule k V} (hgrade : ∀ d, S d ≤ A.grade d) :
    ∀ s ∈ ⋃ d, (S d : Set V), ∃ d, s ∈ A.grade d := by
  intro s hs
  obtain ⟨d, hd⟩ := Set.mem_iUnion.1 hs
  exact ⟨d, hgrade d hd⟩

/-- A generator lying in `V_d` lies in `S d` (distinct graded pieces meet in zero). -/
theorem mem_of_mem_iUnion_of_mem_grade {S : ℕ → Submodule k V}
    (hgrade : ∀ d, S d ≤ A.grade d) {d : ℕ} {s : V} (hs : s ∈ ⋃ e, (S e : Set V))
    (hd : s ∈ A.grade d) : s ∈ S d := by
  obtain ⟨e, he⟩ := Set.mem_iUnion.1 hs
  by_cases hed : e = d
  · subst hed
    exact he
  · have hs0 : s = 0 := A.eq_zero_of_mem_grade_of_ne (hgrade e he) hd hed
    rw [hs0]
    exact Submodule.zero_mem _

/-- For graded generator spaces, the span of the generators lying in `V_d` is `S d`. -/
theorem genSpan_iUnion {S : ℕ → Submodule k V} (hgrade : ∀ d, S d ≤ A.grade d) (d : ℕ) :
    A.genSpan (⋃ e, (S e : Set V)) d = S d := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro s ⟨hs, hsg⟩
    exact A.mem_of_mem_iUnion_of_mem_grade hgrade hs hsg
  · intro s hs
    exact Submodule.subset_span ⟨Set.mem_iUnion.2 ⟨d, hs⟩, hgrade d hs⟩

/-- **Weight one** (line 2601).  For graded generator spaces `S d ⊆ V_d`, the weight-one part
of their differential normal span is `S 1`: a normal word in homogeneous generators has weight
one only if it is a weight-one generator up to vacuum factors. -/
theorem normalSpan_iUnion_inf_grade_one {S : ℕ → Submodule k V}
    (hgrade : ∀ d, S d ≤ A.grade d) :
    A.normalSpan (⋃ d, (S d : Set V)) ⊓ A.grade 1 = S 1 := by
  rw [A.normalSpan_inf_grade_one (A.homogeneous_iUnion hgrade), A.genSpan_iUnion hgrade]

/-- For graded generator spaces and `d ≠ 0`, the weight-`d` part of their normal span is `S d`
plus derivatives of weight-`(d-1)` normal elements and `(-1)`-products of two positive-weight
normal elements of total weight `d`. -/
theorem normalSpan_iUnion_inf_grade {S : ℕ → Submodule k V} (hgrade : ∀ d, S d ≤ A.grade d)
    {d : ℕ} (hd : d ≠ 0) :
    A.normalSpan (⋃ e, (S e : Set V)) ⊓ A.grade d =
      S d ⊔ A.derivProdSpan (⋃ e, (S e : Set V)) d := by
  rw [A.normalSpan_inf_grade_eq_sup (A.homogeneous_iUnion hgrade) hd, A.genSpan_iUnion hgrade]

/-! ### Zero modes -/

/-- If `a` is homogeneous and `a_(0)` sends the generators into `𝒩(S)`, then `a_(0)`
preserves `𝒩(S)`: `a_(0) (x_(-1) y) = (a_(0) x)_(-1) y + x_(-1) (a_(0) y)` and
`a_(0) T = T a_(0)`. -/
theorem zero_mode_mem_normalSpan {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {p : ℕ}
    {a : V} (ha : a ∈ A.grade p) (hgen : ∀ s ∈ S, A.mode 0 a s ∈ A.normalSpan S) {x : V}
    (hx : x ∈ A.normalSpan S) : A.mode 0 a x ∈ A.normalSpan S := by
  rw [A.normalSpan_eq_span_words hS] at hx
  refine A.mode_mem_of_mem_span_right ?_ hx
  rintro y ⟨d, hy⟩
  induction hy with
  | vac =>
    rw [A.mode_vac_nonneg 0 a le_rfl]
    exact Submodule.zero_mem _
  | gen hs _ => exact hgen _ hs
  | @deriv d x hx ih =>
    have key : A.mode 0 a (A.T x) = A.T (A.mode 0 a x) := by
      rw [A.T_mode, A.mode_T]
      simp
    rw [key]
    exact A.T_mem_normalSpan ih
  | @prod i j x y hx hy ihx ihy =>
    have hxg : x ∈ A.grade i := A.normalWord_mem_grade hx
    have hcomm := A.commutator ha hxg 0 (-1) y
    rw [sub_eq_iff_eq_add] at hcomm
    rw [hcomm]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun t _ => ?_)
      (A.prod_mem_normalSpan (A.normalWord_mem_normalSpan hx) ihy)
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · refine Submodule.smul_mem _ _ ?_
      simpa using A.prod_mem_normalSpan ihx (A.normalWord_mem_normalSpan hy)
    · rw [zbinom_zero_left_of_pos k ht, zero_smul]
      exact Submodule.zero_mem _

/-! ### Generator pairs -/

/-- **Generator pairs close** (lexicographic induction on `(wt s + wt t, wt s)`). -/
theorem recursive_pairs {S : ℕ → Submodule k V} {h : ℕ} (hgrade : ∀ d, S d ≤ A.grade d)
    (htop : ∀ d, h < d → S d = ⊥)
    (h1 : ∀ x, x ∈ S 1 ∨ x ∈ S 2 → ∀ d, ∀ s ∈ S d, ∀ n : ℕ,
      A.mode n x s ∈ A.normalSpan (⋃ e, (S e : Set V)))
    (h2 : ∀ d, 3 ≤ d → d ≤ h →
      S d ≤ Submodule.span k {x | ∃ a ∈ S 2, ∃ b ∈ S (d - 1), x = A.mode 0 a b} ⊔
        (A.normalSpan (⋃ e, ⋃ (_ : e < d), (S e : Set V)) ⊓ A.grade d)) :
    ∀ m i j, i + j = m → ∀ s ∈ S i, ∀ t ∈ S j, ∀ n : ℕ,
      A.mode n s t ∈ A.normalSpan (⋃ e, (S e : Set V)) := by
  have hG := A.homogeneous_iUnion hgrade
  have hzero : ∀ a ∈ S 2, ∀ x ∈ A.normalSpan (⋃ e, (S e : Set V)),
      A.mode 0 a x ∈ A.normalSpan (⋃ e, (S e : Set V)) := by
    intro a ha x hx
    refine A.zero_mode_mem_normalSpan hG (hgrade 2 ha) ?_ hx
    intro s hs
    obtain ⟨d, hd⟩ := Set.mem_iUnion.1 hs
    simpa using h1 a (Or.inr ha) d s hd 0
  intro m
  induction m using Nat.strong_induction_on with | _ m IHm
  intro i
  induction i using Nat.strong_induction_on with | _ i IHi
  intro j hij s hs t ht n
  have hW : ∀ i' j', i' + j' < m → A.Closes (⋃ e, (S e : Set V)) i' j' :=
    A.closes_of_lt hG fun i' j' s' t' hs' hs'g ht' ht'g hlt n' =>
      IHm _ hlt i' j' rfl s' (A.mem_of_mem_iUnion_of_mem_grade hgrade hs' hs'g) t'
        (A.mem_of_mem_iUnion_of_mem_grade hgrade ht' ht'g) n'
  have htW : t ∈ A.wordSpan (⋃ e, (S e : Set V)) j :=
    A.normalWord_mem_wordSpan (IsNormalWord.gen (Set.mem_iUnion.2 ⟨j, ht⟩) (hgrade j ht))
  rcases Nat.lt_or_ge i 3 with hi3 | hi3
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [A.mode_natCast_of_mem_grade_zero (hgrade 0 hs) n t]
      exact Submodule.zero_mem _
    · have h12 : s ∈ S 1 ∨ s ∈ S 2 := by
        rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
        · exact Or.inl hs
        · exact Or.inr hs
      exact h1 s h12 j t ht n
  rcases Nat.lt_or_ge h i with hhi | hhi
  · rw [htop i hhi] at hs
    rw [(Submodule.mem_bot k).1 hs, map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := Submodule.mem_sup.1 (h2 i hi3 hhi hs)
  rw [map_add, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · -- the part `A₀ S_{i-1}`: `(a_(0) b)_(n) t = a_(0) (b_(n) t) - b_(n) (a_(0) t)`
    refine A.mode_mem_of_mem_span_left ?_ hs₁
    rintro x ⟨a, ha, b, hb, rfl⟩
    have hag : a ∈ A.grade 2 := hgrade 2 ha
    have hbg : b ∈ A.grade (i - 1) := hgrade (i - 1) hb
    have hcomm := A.commutator hag hbg 0 (n : ℤ) t
    have hsum : ∑ u ∈ Finset.range (2 + (i - 1)),
        zbinom k 0 u • A.mode (0 + (n : ℤ) - u) (A.mode u a b) t =
          A.mode n (A.mode 0 a b) t := by
      rw [Finset.sum_eq_single 0]
      · simp [zbinom_zero_left]
      · intro u _ hu
        rw [zbinom_zero_left_of_pos k (Nat.pos_of_ne_zero hu), zero_smul]
      · intro h0
        exact absurd (Finset.mem_range.2 (by omega)) h0
    rw [← hcomm.trans hsum]
    refine Submodule.sub_mem _
      (hzero a ha _ (IHm (i - 1 + j) (by omega) (i - 1) j rfl b hb t ht n)) ?_
    have hat : A.mode 0 a t ∈ A.normalSpan (⋃ e, (S e : Set V)) := by
      simpa using h1 a (Or.inr ha) j t ht 0
    have hatg : A.mode 0 a t ∈ A.grade (j + 1) :=
      A.mode_mem_grade' 0 hag (hgrade j ht) (by omega)
    have hatW := A.mem_wordSpan_of_mem hG hat hatg
    have hbW : b ∈ A.wordSpan (⋃ e, (S e : Set V)) (i - 1) :=
      A.normalWord_mem_wordSpan (IsNormalWord.gen (Set.mem_iUnion.2 ⟨i - 1, hb⟩) hbg)
    refine A.mode_mem_of_mem_span_right ?_ (A.wordSpan_le_span_reduced _ _ hatW)
    rintro y (hy : A.IsReduced (⋃ e, (S e : Set V)) (j + 1) y)
    cases hy with
    | vac =>
      rw [A.mode_vac_natCast]
      exact Submodule.zero_mem _
    | gen hy hyg =>
      exact IHi (i - 1) (by omega) (j + 1) (by omega) b hb y
        (A.mem_of_mem_iUnion_of_mem_grade hgrade hy hyg) n
    | dp hy => exact A.closes_right_dp hG hW (by omega) hbW hy n
  · -- the normal remainder of weight `i` in generators of weight `< i`
    obtain ⟨hs₂N, hs₂g⟩ := Submodule.mem_inf.1 hs₂
    have hsub : (⋃ e, ⋃ (_ : e < i), (S e : Set V)) ⊆ ⋃ e, (S e : Set V) := by
      intro x hx
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx ⊢
      obtain ⟨e, _, hxe⟩ := hx
      exact ⟨e, hxe⟩
    have hG' : ∀ x ∈ ⋃ e, ⋃ (_ : e < i), (S e : Set V), ∃ d, x ∈ A.grade d :=
      fun x hx => hG x (hsub hx)
    have hs₂W := A.mem_wordSpan_of_mem hG' hs₂N hs₂g
    refine A.mode_mem_of_mem_span_left ?_ (A.wordSpan_le_span_reduced _ _ hs₂W)
    rintro x (hx : A.IsReduced (⋃ e, ⋃ (_ : e < i), (S e : Set V)) i x)
    cases hx with
    | vac =>
      rw [A.vac_mode_natCast]
      exact Submodule.zero_mem _
    | gen hx hxg =>
      simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hx
      obtain ⟨e, he, hxe⟩ := hx
      have hx0 : x = 0 := A.eq_zero_of_mem_grade_of_ne (hgrade e hxe) hxg (by omega)
      rw [hx0, map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    | dp hx => exact A.closes_left_dp hG hW hij (A.isDerivOrProd_mono hsub hx) htW n

/-! ### All modes -/

/-- Nonnegative modes preserve `𝒩`. -/
theorem recursive_nonneg_mem {S : ℕ → Submodule k V} {h : ℕ}
    (hgrade : ∀ d, S d ≤ A.grade d) (htop : ∀ d, h < d → S d = ⊥)
    (h1 : ∀ x, x ∈ S 1 ∨ x ∈ S 2 → ∀ d, ∀ s ∈ S d, ∀ n : ℕ,
      A.mode n x s ∈ A.normalSpan (⋃ e, (S e : Set V)))
    (h2 : ∀ d, 3 ≤ d → d ≤ h →
      S d ≤ Submodule.span k {x | ∃ a ∈ S 2, ∃ b ∈ S (d - 1), x = A.mode 0 a b} ⊔
        (A.normalSpan (⋃ e, ⋃ (_ : e < d), (S e : Set V)) ⊓ A.grade d))
    {x y : V} (hx : x ∈ A.normalSpan (⋃ e, (S e : Set V)))
    (hy : y ∈ A.normalSpan (⋃ e, (S e : Set V))) (n : ℕ) :
    A.mode n x y ∈ A.normalSpan (⋃ e, (S e : Set V)) := by
  have hG := A.homogeneous_iUnion hgrade
  have hpairs := A.recursive_pairs hgrade htop h1 h2
  rw [A.normalSpan_eq_span_words hG] at hx hy
  refine bilin_mem_of_mem_span (A.mode n) ?_ hx hy
  rintro a ⟨i, ha⟩ b ⟨j, hb⟩
  refine A.closes_of_lt hG (w := i + j + 1) ?_ i j (by omega) a
    (A.normalWord_mem_wordSpan ha) b (A.normalWord_mem_wordSpan hb) n
  intro i' j' s t hs hsg ht htg _ n'
  exact hpairs _ i' j' rfl s (A.mem_of_mem_iUnion_of_mem_grade hgrade hs hsg) t
    (A.mem_of_mem_iUnion_of_mem_grade hgrade ht htg) n'

/-- A subspace closed under `T` and under `(-1)`-products is closed under every negative
mode: `x_(-1-r) y = (r + 1)⁻¹ (T x)_(-r) y`, i.e. `x_(-1-r) y = (r!)⁻¹ (T^r x)_(-1) y`. -/
theorem neg_mode_mem [CharZero k] {W : Submodule k V} (hT : ∀ x ∈ W, A.T x ∈ W)
    (hprod : ∀ x ∈ W, ∀ y ∈ W, A.mode (-1) x y ∈ W) (r : ℕ) :
    ∀ x ∈ W, ∀ y ∈ W, A.mode (-1 - (r : ℤ)) x y ∈ W := by
  induction r with
  | zero =>
    intro x hx y hy
    simpa using hprod x hx y hy
  | succ r ih =>
    intro x hx y hy
    have hr : ((r : k) + 1) ≠ 0 := Nat.cast_add_one_ne_zero r
    have key := A.mode_T (-1 - (r : ℤ)) x y
    have e2 : (((-1 - (r : ℤ)) : ℤ) : k) = -((r : k) + 1) := by push_cast; ring
    rw [e2, neg_smul, neg_neg] at key
    have e1 : (-1 - ((r + 1 : ℕ) : ℤ)) = -1 - (r : ℤ) - 1 := by push_cast; ring
    have hmode : A.mode (-1 - (r : ℤ) - 1) x y =
        ((r : k) + 1)⁻¹ • A.mode (-1 - (r : ℤ)) (A.T x) y := by
      rw [key, smul_smul, inv_mul_cancel₀ hr, one_smul]
    rw [e1, hmode]
    exact W.smul_mem _ (ih (A.T x) (hT x hx) y hy)

/-! ### The vertex subalgebra generated by a set -/

theorem generated_isSubalgebra (G : Set V) : A.IsSubalgebra (A.generated G) := by
  refine ⟨Submodule.mem_sInf.2 fun W hW => hW.1.1, fun n x hx y hy => ?_⟩
  refine Submodule.mem_sInf.2 fun W hW => ?_
  exact hW.1.2 n x (Submodule.mem_sInf.1 hx W hW) y (Submodule.mem_sInf.1 hy W hW)

theorem subset_generated (G : Set V) : G ⊆ A.generated G :=
  fun _ hx => Submodule.mem_sInf.2 fun _ hW => hW.2 hx

theorem normalSpan_le_generated (G : Set V) : A.normalSpan G ≤ A.generated G := by
  have hsub := A.generated_isSubalgebra G
  refine A.normalSpan_le hsub.1 (A.subset_generated G) ?_ ?_
  · intro x hx
    rw [A.T_eq]
    exact hsub.2 (-2) x hx A.vac hsub.1
  · intro x hx y hy
    exact hsub.2 (-1) x hx y hy

/-- If the normal span of `G` is a vertex subalgebra, it is the vertex subalgebra generated by
`G`, i.e. `G` strongly generates the vertex algebra it generates. -/
theorem generated_eq_normalSpan {G : Set V} (hN : A.IsSubalgebra (A.normalSpan G)) :
    A.generated G = A.normalSpan G :=
  le_antisymm (A.generated_le hN (A.subset_normalSpan G)) (A.normalSpan_le_generated G)

/-! ### The criterion -/

/-- **Theorem `thm:recursive`, closure.** Under hypotheses 1 and 2 the differential normal span
of `⋃ d, S d` is a vertex subalgebra. -/
theorem recursive_isSubalgebra [CharZero k] {S : ℕ → Submodule k V} {h : ℕ}
    (hgrade : ∀ d, S d ≤ A.grade d) (htop : ∀ d, h < d → S d = ⊥)
    (h1 : ∀ x, x ∈ S 1 ∨ x ∈ S 2 → ∀ d, ∀ s ∈ S d, ∀ n : ℕ,
      A.mode n x s ∈ A.normalSpan (⋃ e, (S e : Set V)))
    (h2 : ∀ d, 3 ≤ d → d ≤ h →
      S d ≤ Submodule.span k {x | ∃ a ∈ S 2, ∃ b ∈ S (d - 1), x = A.mode 0 a b} ⊔
        (A.normalSpan (⋃ e, ⋃ (_ : e < d), (S e : Set V)) ⊓ A.grade d)) :
    A.IsSubalgebra (A.normalSpan (⋃ e, (S e : Set V))) := by
  refine ⟨A.vac_mem_normalSpan _, fun n x hx y hy => ?_⟩
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact A.recursive_nonneg_mem hgrade htop h1 h2 hx hy n
  · have e : n = -1 - ((-1 - n).toNat : ℤ) := by omega
    rw [e]
    exact A.neg_mode_mem (fun z hz => A.T_mem_normalSpan hz)
      (fun a ha b hb => A.prod_mem_normalSpan ha hb) _ x hx y hy

/-- **Theorem `thm:recursive` (recursive strong-generation criterion).**
Let `S d ⊆ V_d` (`d : ℕ`) be subspaces with `S d = 0` for `d > h`, and let
`𝒩 = A.normalSpan (⋃ d, S d)`.  Assume
1. (`h1`) `x_(n) s ∈ 𝒩` for every `x ∈ S 1 ∪ S 2`, every `s ∈ S d` and every `n ≥ 0`;
2. (`h2`) for `3 ≤ d ≤ h`,
   `S d ⊆ span {a_(0) b | a ∈ S 2, b ∈ S (d - 1)} + 𝒩(⋃_{e<d} S e) ∩ V_d`.

Then `𝒩` is a vertex subalgebra, it equals the vertex subalgebra generated by `⋃ d, S d`
(strong generation), and the weight-one part of that vertex subalgebra is `S 1`. -/
theorem recursive_strong_generation [CharZero k] (S : ℕ → Submodule k V) (h : ℕ)
    (hgrade : ∀ d, S d ≤ A.grade d) (htop : ∀ d, h < d → S d = ⊥)
    (h1 : ∀ x, x ∈ S 1 ∨ x ∈ S 2 → ∀ d, ∀ s ∈ S d, ∀ n : ℕ,
      A.mode n x s ∈ A.normalSpan (⋃ e, (S e : Set V)))
    (h2 : ∀ d, 3 ≤ d → d ≤ h →
      S d ≤ Submodule.span k {x | ∃ a ∈ S 2, ∃ b ∈ S (d - 1), x = A.mode 0 a b} ⊔
        (A.normalSpan (⋃ e, ⋃ (_ : e < d), (S e : Set V)) ⊓ A.grade d)) :
    A.IsSubalgebra (A.normalSpan (⋃ d, (S d : Set V))) ∧
      A.generated (⋃ d, (S d : Set V)) = A.normalSpan (⋃ d, (S d : Set V)) ∧
      A.generated (⋃ d, (S d : Set V)) ⊓ A.grade 1 = S 1 := by
  have hsub := A.recursive_isSubalgebra hgrade htop h1 h2
  have hgen := A.generated_eq_normalSpan hsub
  refine ⟨hsub, hgen, ?_⟩
  rw [hgen]
  exact A.normalSpan_iUnion_inf_grade_one hgrade

/-- Strong generation in the vocabulary of the interface. -/
theorem recursive_stronglyGenerates [CharZero k] (S : ℕ → Submodule k V) (h : ℕ)
    (hgrade : ∀ d, S d ≤ A.grade d) (htop : ∀ d, h < d → S d = ⊥)
    (h1 : ∀ x, x ∈ S 1 ∨ x ∈ S 2 → ∀ d, ∀ s ∈ S d, ∀ n : ℕ,
      A.mode n x s ∈ A.normalSpan (⋃ e, (S e : Set V)))
    (h2 : ∀ d, 3 ≤ d → d ≤ h →
      S d ≤ Submodule.span k {x | ∃ a ∈ S 2, ∃ b ∈ S (d - 1), x = A.mode 0 a b} ⊔
        (A.normalSpan (⋃ e, ⋃ (_ : e < d), (S e : Set V)) ⊓ A.grade d)) :
    A.StronglyGenerates (⋃ d, (S d : Set V)) (A.generated (⋃ d, (S d : Set V))) :=
  (A.recursive_strong_generation S h hgrade htop h1 h2).2.1.symm

end VertexAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.VertexAlgebra.recursive_strong_generation
#print axioms HaagerupIzumi.C8.VertexAlgebra.recursive_isSubalgebra
#print axioms HaagerupIzumi.C8.VertexAlgebra.recursive_stronglyGenerates
#print axioms HaagerupIzumi.C8.VertexAlgebra.normalSpan_iUnion_inf_grade_one
#print axioms HaagerupIzumi.C8.VertexAlgebra.normalSpan_iUnion_inf_grade
#print axioms HaagerupIzumi.C8.VertexAlgebra.generated_eq_normalSpan
#print axioms HaagerupIzumi.C8.VertexAlgebra.zero_mode_mem_normalSpan
#print axioms HaagerupIzumi.C8.VertexAlgebra.neg_mode_mem
