module

public import HaagerupIzumi.C8.VertexAlgebra.Basic
public import Mathlib.Algebra.Module.Submodule.Bilinear

@[expose] public section

/-!
# Normal words and the graded structure of the differential normal span

For a vertex algebra `A` (the interface `HaagerupIzumi.C8.VertexAlgebra`) and a set `S` of
homogeneous vectors, this file describes the differential normal span `A.normalSpan S`
(Definition `def:normal-span`, line 2098 of `c8_expanded_20260929/haagerup_c8_expanded.tex`)
weight by weight.

* `IsNormalWord A S d x`: `x` is the value of a differential normal word of weight `d` in the
  generators `S` (the vacuum, a generator lying in `V_d`, a translate `T w`, or a
  `(-1)`-product `w₁ (-1) w₂`, in any parenthesization).
* `wordSpan A S d`: the span of the normal words of weight `d`.
* `normalSpan_eq_iSup_wordSpan`, `normalSpan_eq_span_words`: if every element of `S` is
  homogeneous, the normal span is spanned by normal words.
* `normalSpan_inf_grade`: if every element of `S` is homogeneous,
  `normalSpan S ⊓ V_d = wordSpan S d` (this uses the independence of the grading).
* `wordSpan_le_span_reduced`, `wordSpan_le_sup`: modulo vacuum factors, a normal word of weight
  `d` is the vacuum, a generator lying in `V_d`, a translate, or a `(-1)`-product of two
  positive-weight normal elements (`IsReduced`, `IsDerivOrProd`).
* `normalSpan_inf_grade_eq_sup`: for `d ≠ 0`,
  `normalSpan S ⊓ V_d = genSpan S d ⊔ derivProdSpan S d`.
* `wordSpan_zero_le`, `normalSpan_inf_grade_zero`, `wordSpan_one`, `normalSpan_inf_grade_one`:
  weight-zero normal elements are multiples of the vacuum, and the weight-one part of the
  normal span is spanned by the weight-one generators (the observation "a normal word in
  positive-weight generators cannot acquire weight one unless it is a weight-one generator",
  line 2601).

The file also contains elementary consequences of the interface fields (vacuum identities,
binomial coefficients `zbinom` at `0` and at natural numbers, grading of modes, independence
of distinct graded pieces).  No hypothesis is external: only the fields of `VertexAlgebra`
are used.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

/-! ### Binomial coefficients -/

theorem zbinom_zero_left (k : Type*) [Field k] (t : ℕ) :
    zbinom k 0 t = if t = 0 then 1 else 0 := by
  unfold zbinom
  rw [Ring.choose_zero_ite ℤ t]
  split_ifs <;> simp

theorem zbinom_zero_left_of_pos (k : Type*) [Field k] {t : ℕ} (ht : 0 < t) :
    zbinom k 0 t = 0 := by
  rw [zbinom_zero_left, if_neg (Nat.pos_iff_ne_zero.1 ht)]

theorem zbinom_natCast (k : Type*) [Field k] (n t : ℕ) :
    zbinom k (n : ℤ) t = (n.choose t : k) := by
  unfold zbinom
  rw [Ring.choose_natCast]
  simp

theorem zbinom_natCast_of_lt (k : Type*) [Field k] {n t : ℕ} (h : n < t) :
    zbinom k (n : ℤ) t = 0 := by
  rw [zbinom_natCast, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

/-! ### Spans and (bi)linear maps -/

section Span

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- A linear map sends a span into `W` once it sends the spanning set into `W`. -/
theorem linear_mem_of_mem_span (f : V →ₗ[k] V) {s : Set V} {W : Submodule k V}
    (h : ∀ x ∈ s, f x ∈ W) {x : V} (hx : x ∈ Submodule.span k s) : f x ∈ W := by
  have hle : Submodule.span k s ≤ W.comap f := Submodule.span_le.2 fun y hy => h y hy
  exact hle hx

/-- A bilinear map sends a pair of spans into `W` once it sends pairs of spanning vectors
into `W`. -/
theorem bilin_mem_of_mem_span (f : V →ₗ[k] V →ₗ[k] V) {s t : Set V} {W : Submodule k V}
    (h : ∀ x ∈ s, ∀ y ∈ t, f x y ∈ W) {x y : V} (hx : x ∈ Submodule.span k s)
    (hy : y ∈ Submodule.span k t) : f x y ∈ W := by
  have hle : Submodule.map₂ f (Submodule.span k s) (Submodule.span k t) ≤ W := by
    rw [Submodule.map₂_span_span, Submodule.span_le]
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact h a ha b hb
  exact hle (Submodule.apply_mem_map₂ f hx hy)

end Span

namespace VertexAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (A : VertexAlgebra k V)

/-! ### Elementary mode identities -/

theorem T_vac : A.T A.vac = 0 := by
  have h : (-2 : ℤ) ≠ -1 := by norm_num
  rw [A.T_eq, A.vac_mode, if_neg h]

theorem vac_mode_natCast (n : ℕ) (b : V) : A.mode n A.vac b = 0 := by
  have h : (n : ℤ) ≠ -1 := by omega
  rw [A.vac_mode, if_neg h]

theorem mode_vac_natCast (n : ℕ) (a : V) : A.mode n a A.vac = 0 :=
  A.mode_vac_nonneg n a (by omega)

theorem vac_mode_neg_one (b : V) : A.mode (-1) A.vac b = b := by
  rw [A.vac_mode, if_pos rfl]

theorem mode_neg_one_smul_vac_left (c : k) (b : V) : A.mode (-1) (c • A.vac) b = c • b := by
  rw [map_smul, LinearMap.smul_apply, A.vac_mode_neg_one]

theorem mode_neg_one_smul_vac_right (c : k) (a : V) : A.mode (-1) a (c • A.vac) = c • a := by
  rw [map_smul, A.mode_vac_neg_one]

theorem mem_grade_zero {x : V} (hx : x ∈ A.grade 0) : ∃ c : k, x = c • A.vac := by
  rw [A.grade_zero, Submodule.mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := hx
  exact ⟨c, hc.symm⟩

theorem mode_natCast_of_mem_grade_zero {x : V} (hx : x ∈ A.grade 0) (n : ℕ) (y : V) :
    A.mode n x y = 0 := by
  obtain ⟨c, rfl⟩ := A.mem_grade_zero hx
  rw [map_smul, LinearMap.smul_apply, A.vac_mode_natCast, smul_zero]

/-- The grading of a mode, with the target weight given as a natural number. -/
theorem mode_mem_grade' {i j e : ℕ} {a b : V} (n : ℤ) (ha : a ∈ A.grade i)
    (hb : b ∈ A.grade j) (he : (e : ℤ) = i + j - n - 1) : A.mode n a b ∈ A.grade e := by
  have h := A.mode_grade n ha hb (by omega)
  have h' : ((i : ℤ) + j - n - 1).toNat = e := by omega
  rwa [h'] at h

/-- Distinct graded pieces meet in zero. -/
theorem eq_zero_of_mem_grade_of_ne {d e : ℕ} {x : V} (hd : x ∈ A.grade d)
    (he : x ∈ A.grade e) (hde : d ≠ e) : x = 0 := by
  have hdisj : Disjoint (A.grade d) (A.grade e) :=
    A.grade_internal.submodule_iSupIndep.pairwiseDisjoint hde
  exact Submodule.disjoint_def.1 hdisj x hd he

/-- If a family of subspaces lies in the graded pieces, the degree-`d` part of its sum is the
`d`-th member. -/
theorem iSup_inf_grade_le (N : ℕ → Submodule k V) (hN : ∀ e, N e ≤ A.grade e) (d : ℕ) :
    (⨆ e, N e) ⊓ A.grade d ≤ N d := by
  intro x hx
  obtain ⟨hx, hxd⟩ := Submodule.mem_inf.1 hx
  have hsplit : (⨆ e, N e) ≤ N d ⊔ ⨆ (e : ℕ) (_ : e ≠ d), N e := by
    refine iSup_le fun e => ?_
    by_cases he : e = d
    · subst he
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le e he le_rfl)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hsplit hx)
  have hz' : z ∈ ⨆ (e : ℕ) (_ : e ≠ d), A.grade e := iSup₂_mono (fun e _ => hN e) hz
  have hzd : z ∈ A.grade d := by
    have h := Submodule.sub_mem _ hxd (hN d hy)
    simpa using h
  have hz0 : z = 0 :=
    Submodule.disjoint_def.1 (A.grade_internal.submodule_iSupIndep d) z hzd hz'
  rw [hz0, add_zero]
  exact hy

theorem T_pow_mem {W : Submodule k V} (hT : ∀ x ∈ W, A.T x ∈ W) (t : ℕ) {x : V}
    (hx : x ∈ W) : (A.T ^ t) x ∈ W := by
  induction t with
  | zero => simpa using hx
  | succ t ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hT _ ih

theorem mode_mem_of_mem_span_left {s : Set V} {W : Submodule k V} {n : ℤ} {y : V}
    (h : ∀ x ∈ s, A.mode n x y ∈ W) {x : V} (hx : x ∈ Submodule.span k s) :
    A.mode n x y ∈ W := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    rw [map_zero, LinearMap.zero_apply]
    exact W.zero_mem
  | add x z _ _ hx hz =>
    rw [map_add, LinearMap.add_apply]
    exact W.add_mem hx hz
  | smul c x _ hx =>
    rw [map_smul, LinearMap.smul_apply]
    exact W.smul_mem c hx

theorem mode_mem_of_mem_span_right {s : Set V} {W : Submodule k V} {n : ℤ} {x : V}
    (h : ∀ y ∈ s, A.mode n x y ∈ W) {y : V} (hy : y ∈ Submodule.span k s) :
    A.mode n x y ∈ W :=
  linear_mem_of_mem_span (A.mode n x) h hy

/-! ### Normal words -/

/-- `A.IsNormalWord S d x`: `x` is the value of a differential normal word of weight `d` in the
generators `S`: the vacuum (weight `0`), a generator lying in `V_d` (weight `d`), a translate
(weight `+1`), or a `(-1)`-product (weights add), with every parenthesization allowed. -/
inductive IsNormalWord (S : Set V) : ℕ → V → Prop
  | vac : IsNormalWord S 0 A.vac
  | gen {d : ℕ} {s : V} : s ∈ S → s ∈ A.grade d → IsNormalWord S d s
  | deriv {d : ℕ} {x : V} : IsNormalWord S d x → IsNormalWord S (d + 1) (A.T x)
  | prod {i j : ℕ} {x y : V} : IsNormalWord S i x → IsNormalWord S j y →
      IsNormalWord S (i + j) (A.mode (-1) x y)

/-- The span of the normal words of weight `d`. -/
def wordSpan (S : Set V) (d : ℕ) : Submodule k V :=
  Submodule.span k {x | A.IsNormalWord S d x}

/-- The span of the generators lying in `V_d`. -/
def genSpan (S : Set V) (d : ℕ) : Submodule k V :=
  Submodule.span k {s | s ∈ S ∧ s ∈ A.grade d}

/-- `A.IsDerivOrProd S d x`: `x` is a translate of a normal element of weight `d - 1`, or a
`(-1)`-product of two normal elements of positive weights adding up to `d`. -/
inductive IsDerivOrProd (S : Set V) : ℕ → V → Prop
  | deriv {d : ℕ} {y : V} : y ∈ A.wordSpan S d → IsDerivOrProd S (d + 1) (A.T y)
  | prod {i j : ℕ} {y z : V} : 0 < i → 0 < j → y ∈ A.wordSpan S i → z ∈ A.wordSpan S j →
      IsDerivOrProd S (i + j) (A.mode (-1) y z)

/-- The span of derivatives and of products of two positive-weight normal elements, of
weight `d`. -/
def derivProdSpan (S : Set V) (d : ℕ) : Submodule k V :=
  Submodule.span k {x | A.IsDerivOrProd S d x}

/-- Reduced spanning vectors of weight `d`: the vacuum, a generator lying in `V_d`, or a
derivative or product as in `IsDerivOrProd`. -/
inductive IsReduced (S : Set V) : ℕ → V → Prop
  | vac {d : ℕ} : IsReduced S d A.vac
  | gen {d : ℕ} {s : V} : s ∈ S → s ∈ A.grade d → IsReduced S d s
  | dp {d : ℕ} {x : V} : A.IsDerivOrProd S d x → IsReduced S d x

theorem normalWord_mem_grade {S : Set V} {d : ℕ} {x : V} (h : A.IsNormalWord S d x) :
    x ∈ A.grade d := by
  induction h with
  | vac =>
    rw [A.grade_zero]
    exact Submodule.mem_span_singleton_self _
  | gen _ hs => exact hs
  | deriv _ ih => exact A.T_grade ih
  | @prod i j x y _ _ ihx ihy => exact A.mode_mem_grade' (-1) ihx ihy (by omega)

theorem normalWord_mem_normalSpan {S : Set V} {d : ℕ} {x : V} (h : A.IsNormalWord S d x) :
    x ∈ A.normalSpan S := by
  induction h with
  | vac => exact A.vac_mem_normalSpan S
  | gen hs _ => exact A.subset_normalSpan S hs
  | deriv _ ih => exact A.T_mem_normalSpan ih
  | prod _ _ ihx ihy => exact A.prod_mem_normalSpan ihx ihy

theorem normalWord_mem_wordSpan {S : Set V} {d : ℕ} {x : V} (h : A.IsNormalWord S d x) :
    x ∈ A.wordSpan S d :=
  Submodule.subset_span h

theorem wordSpan_le_grade (S : Set V) (d : ℕ) : A.wordSpan S d ≤ A.grade d :=
  Submodule.span_le.2 fun _ hx => A.normalWord_mem_grade hx

theorem wordSpan_le_normalSpan (S : Set V) (d : ℕ) : A.wordSpan S d ≤ A.normalSpan S :=
  Submodule.span_le.2 fun _ hx => A.normalWord_mem_normalSpan hx

theorem deriv_mem_wordSpan {S : Set V} {d : ℕ} {x : V} (hx : x ∈ A.wordSpan S d) :
    A.T x ∈ A.wordSpan S (d + 1) := by
  refine linear_mem_of_mem_span A.T ?_ hx
  intro y hy
  exact A.normalWord_mem_wordSpan (IsNormalWord.deriv hy)

theorem prod_mem_wordSpan {S : Set V} {i j : ℕ} {x y : V} (hx : x ∈ A.wordSpan S i)
    (hy : y ∈ A.wordSpan S j) : A.mode (-1) x y ∈ A.wordSpan S (i + j) := by
  refine bilin_mem_of_mem_span (A.mode (-1)) ?_ hx hy
  intro a ha b hb
  exact A.normalWord_mem_wordSpan (IsNormalWord.prod ha hb)

theorem normalWord_mono {S S' : Set V} (hSS' : S ⊆ S') {d : ℕ} {x : V}
    (h : A.IsNormalWord S d x) : A.IsNormalWord S' d x := by
  induction h with
  | vac => exact IsNormalWord.vac
  | gen hs hd => exact IsNormalWord.gen (hSS' hs) hd
  | deriv _ ih => exact IsNormalWord.deriv ih
  | prod _ _ ihx ihy => exact IsNormalWord.prod ihx ihy

theorem wordSpan_mono {S S' : Set V} (hSS' : S ⊆ S') (d : ℕ) :
    A.wordSpan S d ≤ A.wordSpan S' d :=
  Submodule.span_mono fun _ hx => A.normalWord_mono hSS' hx

theorem isDerivOrProd_mono {S S' : Set V} (hSS' : S ⊆ S') {d : ℕ} {x : V}
    (h : A.IsDerivOrProd S d x) : A.IsDerivOrProd S' d x := by
  cases h with
  | deriv hy => exact IsDerivOrProd.deriv (A.wordSpan_mono hSS' _ hy)
  | prod hi hj hy hz =>
    exact IsDerivOrProd.prod hi hj (A.wordSpan_mono hSS' _ hy) (A.wordSpan_mono hSS' _ hz)

theorem isDerivOrProd_mem_wordSpan {S : Set V} {d : ℕ} {x : V} (h : A.IsDerivOrProd S d x) :
    x ∈ A.wordSpan S d := by
  cases h with
  | deriv hy => exact A.deriv_mem_wordSpan hy
  | prod _ _ hy hz => exact A.prod_mem_wordSpan hy hz

theorem derivProdSpan_le_wordSpan (S : Set V) (d : ℕ) :
    A.derivProdSpan S d ≤ A.wordSpan S d :=
  Submodule.span_le.2 fun _ hx => A.isDerivOrProd_mem_wordSpan hx

/-! ### The normal span is spanned by normal words -/

theorem iSup_wordSpan (S : Set V) :
    ⨆ d, A.wordSpan S d = Submodule.span k {x | ∃ d, A.IsNormalWord S d x} := by
  have h : {x | ∃ d, A.IsNormalWord S d x} = ⋃ d, {x | A.IsNormalWord S d x} := by
    ext x
    simp
  rw [h, Submodule.span_iUnion]
  rfl

theorem normalSpan_le_iSup_wordSpan {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) :
    A.normalSpan S ≤ ⨆ d, A.wordSpan S d := by
  rw [A.iSup_wordSpan S]
  apply A.normalSpan_le
  · exact Submodule.subset_span ⟨0, IsNormalWord.vac⟩
  · intro s hs
    obtain ⟨d, hd⟩ := hS s hs
    exact Submodule.subset_span ⟨d, IsNormalWord.gen hs hd⟩
  · intro x hx
    refine linear_mem_of_mem_span A.T ?_ hx
    rintro y ⟨d, hy⟩
    exact Submodule.subset_span ⟨d + 1, IsNormalWord.deriv hy⟩
  · intro x hx y hy
    refine bilin_mem_of_mem_span (A.mode (-1)) ?_ hx hy
    rintro a ⟨i, ha⟩ b ⟨j, hb⟩
    exact Submodule.subset_span ⟨i + j, IsNormalWord.prod ha hb⟩

/-- The normal span is the sum of its graded pieces `wordSpan S d`. -/
theorem normalSpan_eq_iSup_wordSpan {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) :
    A.normalSpan S = ⨆ d, A.wordSpan S d :=
  le_antisymm (A.normalSpan_le_iSup_wordSpan hS)
    (iSup_le fun d => A.wordSpan_le_normalSpan S d)

/-- The normal span is spanned by the values of normal words. -/
theorem normalSpan_eq_span_words {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) :
    A.normalSpan S = Submodule.span k {x | ∃ d, A.IsNormalWord S d x} := by
  rw [A.normalSpan_eq_iSup_wordSpan hS, A.iSup_wordSpan]

/-- **Graded description of the normal span.** If every element of `S` is homogeneous, the
weight-`d` part of `𝒩(S)` is spanned by the normal words of weight `d`. -/
theorem normalSpan_inf_grade {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) (d : ℕ) :
    A.normalSpan S ⊓ A.grade d = A.wordSpan S d := by
  apply le_antisymm
  · calc A.normalSpan S ⊓ A.grade d ≤ (⨆ e, A.wordSpan S e) ⊓ A.grade d :=
          inf_le_inf_right _ (A.normalSpan_le_iSup_wordSpan hS)
      _ ≤ A.wordSpan S d := A.iSup_inf_grade_le _ (A.wordSpan_le_grade S) d
  · exact le_inf (A.wordSpan_le_normalSpan S d) (A.wordSpan_le_grade S d)

theorem mem_wordSpan_of_mem {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {d : ℕ} {x : V}
    (hx : x ∈ A.normalSpan S) (hd : x ∈ A.grade d) : x ∈ A.wordSpan S d := by
  rw [← A.normalSpan_inf_grade hS d]
  exact Submodule.mem_inf.2 ⟨hx, hd⟩

/-! ### Reduced form of a normal word -/

theorem normalWord_mem_span_reduced {S : Set V} {d : ℕ} {x : V} (h : A.IsNormalWord S d x) :
    x ∈ Submodule.span k {y | A.IsReduced S d y} := by
  induction h with
  | vac => exact Submodule.subset_span IsReduced.vac
  | gen hs hd => exact Submodule.subset_span (IsReduced.gen hs hd)
  | deriv hx _ =>
    exact Submodule.subset_span
      (IsReduced.dp (IsDerivOrProd.deriv (A.normalWord_mem_wordSpan hx)))
  | @prod i j x y hx hy ihx ihy =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · obtain ⟨c, rfl⟩ := A.mem_grade_zero (A.normalWord_mem_grade hx)
      rw [zero_add, A.mode_neg_one_smul_vac_left]
      exact Submodule.smul_mem _ c ihy
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · obtain ⟨c, rfl⟩ := A.mem_grade_zero (A.normalWord_mem_grade hy)
      rw [add_zero, A.mode_neg_one_smul_vac_right]
      exact Submodule.smul_mem _ c ihx
    · exact Submodule.subset_span (IsReduced.dp (IsDerivOrProd.prod hi hj
        (A.normalWord_mem_wordSpan hx) (A.normalWord_mem_wordSpan hy)))

/-- Modulo vacuum factors, a normal element of weight `d` is a combination of the vacuum,
generators lying in `V_d`, derivatives, and products of two positive-weight normal
elements. -/
theorem wordSpan_le_span_reduced (S : Set V) (d : ℕ) :
    A.wordSpan S d ≤ Submodule.span k {y | A.IsReduced S d y} :=
  Submodule.span_le.2 fun _ hx => A.normalWord_mem_span_reduced hx

theorem wordSpan_le_sup (S : Set V) (d : ℕ) :
    A.wordSpan S d ≤ (k ∙ A.vac) ⊔ A.genSpan S d ⊔ A.derivProdSpan S d := by
  refine (A.wordSpan_le_span_reduced S d).trans (Submodule.span_le.2 ?_)
  rintro x (hx : A.IsReduced S d x)
  cases hx with
  | vac =>
    exact Submodule.mem_sup_left
      (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
  | gen hs hd =>
    exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨hs, hd⟩))
  | dp h => exact Submodule.mem_sup_right (Submodule.subset_span h)

theorem genSpan_le_grade (S : Set V) (d : ℕ) : A.genSpan S d ≤ A.grade d :=
  Submodule.span_le.2 fun _ hx => hx.2

theorem genSpan_le_wordSpan (S : Set V) (d : ℕ) : A.genSpan S d ≤ A.wordSpan S d :=
  Submodule.span_le.2 fun _ hx => A.normalWord_mem_wordSpan (IsNormalWord.gen hx.1 hx.2)

/-- **Graded description in positive weight.** If every element of `S` is homogeneous and
`d ≠ 0`, the weight-`d` part of `𝒩(S)` is spanned by the generators lying in `V_d`, the
derivatives of weight-`(d-1)` normal elements, and the `(-1)`-products of two positive-weight
normal elements of total weight `d`. -/
theorem normalSpan_inf_grade_eq_sup {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {d : ℕ}
    (hd : d ≠ 0) :
    A.normalSpan S ⊓ A.grade d = A.genSpan S d ⊔ A.derivProdSpan S d := by
  rw [A.normalSpan_inf_grade hS]
  apply le_antisymm
  · intro x hx
    have hxd : x ∈ A.grade d := A.wordSpan_le_grade S d hx
    obtain ⟨y, hy, r, hr, rfl⟩ := Submodule.mem_sup.1 (A.wordSpan_le_sup S d hx)
    obtain ⟨v, hv, g, hg, rfl⟩ := Submodule.mem_sup.1 hy
    have hgd : g ∈ A.grade d := A.genSpan_le_grade S d hg
    have hrd : r ∈ A.grade d :=
      A.wordSpan_le_grade S d (A.derivProdSpan_le_wordSpan S d hr)
    have hvd : v ∈ A.grade d := by
      have h := Submodule.sub_mem _ (Submodule.sub_mem _ hxd hgd) hrd
      have e : v + g + r - g - r = v := by abel
      rwa [e] at h
    have hv0 : v ∈ A.grade 0 := by
      rw [A.grade_zero]
      exact hv
    rw [A.eq_zero_of_mem_grade_of_ne hv0 hvd (Ne.symm hd), zero_add]
    exact Submodule.add_mem_sup hg hr
  · exact sup_le (A.genSpan_le_wordSpan S d) (A.derivProdSpan_le_wordSpan S d)

/-! ### Weights zero and one -/

/-- Weight-zero normal elements are multiples of the vacuum. -/
theorem wordSpan_zero_le (S : Set V) : A.wordSpan S 0 ≤ k ∙ A.vac := by
  rw [← A.grade_zero]
  exact A.wordSpan_le_grade S 0

theorem normalSpan_inf_grade_zero (S : Set V) : A.normalSpan S ⊓ A.grade 0 = k ∙ A.vac := by
  rw [A.grade_zero]
  apply le_antisymm inf_le_right
  exact le_inf ((Submodule.span_singleton_le_iff_mem _ _).2 (A.vac_mem_normalSpan S)) le_rfl

/-- A normal word of weight one is, up to vacuum factors, a weight-one generator. -/
theorem normalWord_weight_one {S : Set V} {d : ℕ} {x : V} (h : A.IsNormalWord S d x) :
    d = 1 → x ∈ A.genSpan S 1 := by
  induction h with
  | vac =>
    intro hd
    exact absurd hd (by omega)
  | @gen d s hs hsd =>
    intro hd
    subst hd
    exact Submodule.subset_span ⟨hs, hsd⟩
  | @deriv d x hx _ =>
    intro hd
    obtain rfl : d = 0 := by omega
    obtain ⟨c, rfl⟩ := A.mem_grade_zero (A.normalWord_mem_grade hx)
    rw [map_smul, A.T_vac, smul_zero]
    exact Submodule.zero_mem _
  | @prod i j x y hx hy ihx ihy =>
    intro hd
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · obtain ⟨c, rfl⟩ := A.mem_grade_zero (A.normalWord_mem_grade hx)
      rw [A.mode_neg_one_smul_vac_left]
      exact Submodule.smul_mem _ c (ihy (by omega))
    · obtain rfl : j = 0 := by omega
      obtain ⟨c, rfl⟩ := A.mem_grade_zero (A.normalWord_mem_grade hy)
      rw [A.mode_neg_one_smul_vac_right]
      exact Submodule.smul_mem _ c (ihx (by omega))

theorem wordSpan_one (S : Set V) : A.wordSpan S 1 = A.genSpan S 1 := by
  apply le_antisymm
  · exact Submodule.span_le.2 fun _ hx => A.normalWord_weight_one hx rfl
  · refine Submodule.span_le.2 ?_
    rintro s ⟨hs, hd⟩
    exact A.normalWord_mem_wordSpan (IsNormalWord.gen hs hd)

/-- **Weight one.** If every element of `S` is homogeneous, the weight-one part of the normal
span is spanned by the weight-one generators. -/
theorem normalSpan_inf_grade_one {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) :
    A.normalSpan S ⊓ A.grade 1 = A.genSpan S 1 := by
  rw [A.normalSpan_inf_grade hS, A.wordSpan_one]

end VertexAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.VertexAlgebra.normalSpan_eq_span_words
#print axioms HaagerupIzumi.C8.VertexAlgebra.normalSpan_inf_grade
#print axioms HaagerupIzumi.C8.VertexAlgebra.wordSpan_le_span_reduced
#print axioms HaagerupIzumi.C8.VertexAlgebra.wordSpan_le_sup
#print axioms HaagerupIzumi.C8.VertexAlgebra.normalSpan_inf_grade_one
#print axioms HaagerupIzumi.C8.VertexAlgebra.normalSpan_inf_grade_zero
#print axioms HaagerupIzumi.C8.VertexAlgebra.normalSpan_inf_grade_eq_sup
