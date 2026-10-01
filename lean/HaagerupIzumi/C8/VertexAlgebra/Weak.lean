module

public import HaagerupIzumi.C8.VertexAlgebra.Recursive

@[expose] public section

/-!
# Weak vertex algebras: the normal-span machinery without the CFT-type axiom

`WeakVertexAlgebra k V` has all fields of the shared interface `VertexAlgebra` except the
CFT-type axiom `grade_zero : V_0 = k·1`, which is replaced by `vac ∈ V_0`.  The motivating
example is the product `V × V'` of two vertex algebras of CFT type (componentwise modes,
vacuum `(1, 1)`, grading `V_d × V'_d`), whose weight-zero space is two-dimensional; it is
used in `Diagonal.lean` for the uniqueness half of Proposition
`prop:pf13-finite-reconstruction` (lines 2815–2826 of `c8_expanded_20260929/haagerup_c8_expanded.tex`).

This file re-proves, for weak vertex algebras, the parts of `NormalWords.lean` and
`FilteredWick.lean` that are needed there (the proofs are the same; the only difference is that
weight-zero normal words are shown to be multiples of the vacuum from the hypothesis that no
nonzero generator has weight zero, instead of from `grade_zero`):

* `normalSpan_inf_grade`: `𝒩(S) ∩ V_d` is spanned by the normal words of weight `d`;
* `closes_of_lt`: Lemma `lem:filtered-wick` (a);
* `normalSpan_isClosed`: if all singular products of generators lie in `𝒩(S)`, then `𝒩(S)` is
  closed under all modes (characteristic zero);
* `subVertexAlgebra`: a subspace that contains the vacuum, is closed under `T` and all modes,
  is graded, and has one-dimensional weight-zero part is a `VertexAlgebra` (of CFT type).

No hypothesis is external.
-/

namespace HaagerupIzumi.C8

open scoped BigOperators

/-- All fields of `VertexAlgebra` except the CFT-type axiom, which is replaced by `vac ∈ V_0`. -/
structure WeakVertexAlgebra (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V] where
  mode : ℤ → V →ₗ[k] V →ₗ[k] V
  vac : V
  T : V →ₗ[k] V
  grade : ℕ → Submodule k V
  grade_internal : DirectSum.IsInternal grade
  vac_mem_grade_zero : vac ∈ grade 0
  mode_grade : ∀ {i j : ℕ} {a b : V} (n : ℤ), a ∈ grade i → b ∈ grade j →
    n + 1 ≤ (i : ℤ) + j → mode n a b ∈ grade ((i : ℤ) + j - n - 1).toNat
  mode_trunc : ∀ {i j : ℕ} {a b : V} (n : ℤ), a ∈ grade i → b ∈ grade j →
    (i : ℤ) + j ≤ n → mode n a b = 0
  T_grade : ∀ {i : ℕ} {a : V}, a ∈ grade i → T a ∈ grade (i + 1)
  vac_mode : ∀ (n : ℤ) (b : V), mode n vac b = if n = -1 then b else 0
  mode_vac_nonneg : ∀ (n : ℤ) (a : V), 0 ≤ n → mode n a vac = 0
  mode_vac_neg_one : ∀ a : V, mode (-1) a vac = a
  T_eq : ∀ a : V, T a = mode (-2) a vac
  mode_T : ∀ (n : ℤ) (a b : V), mode n (T a) b = -((n : k) • mode (n - 1) a b)
  T_mode : ∀ (n : ℤ) (a b : V), T (mode n a b) = mode n (T a) b + mode n a (T b)
  commutator : ∀ {i j : ℕ} {a b : V}, a ∈ grade i → b ∈ grade j → ∀ (m n : ℤ) (c : V),
    mode m a (mode n b c) - mode n b (mode m a c) =
      ∑ t ∈ Finset.range (i + j), zbinom k m t • mode (m + n - t) (mode t a b) c
  iterate : ∀ {i j l : ℕ} {a b c : V}, a ∈ grade i → b ∈ grade j → c ∈ grade l →
    ∀ m n : ℤ,
    mode n (mode m a b) c =
      ∑ t ∈ Finset.range (i + j + l + n.natAbs),
        ((-1 : k) ^ t * zbinom k m t) •
          (mode (m - t) a (mode (n + t) b c) - (-1 : k) ^ m • mode (m + n - t) b (mode t a c))
  skew : ∀ {i j : ℕ} {a b : V}, a ∈ grade i → b ∈ grade j → ∀ n : ℤ,
    mode n b a =
      ∑ t ∈ Finset.range (i + j + n.natAbs),
        ((-1 : k) ^ (n + t + 1) * ((t.factorial : k))⁻¹) • (T ^ t) (mode (n + t) a b)

namespace WeakVertexAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (A : WeakVertexAlgebra k V)

/-! ### The differential normal span -/

/-- The differential normal span (as in `VertexAlgebra.normalSpan`). -/
def normalSpan (S : Set V) : Submodule k V :=
  sInf {W : Submodule k V | A.vac ∈ W ∧ S ⊆ W ∧ (∀ x ∈ W, A.T x ∈ W) ∧
    ∀ x ∈ W, ∀ y ∈ W, A.mode (-1) x y ∈ W}

theorem vac_mem_normalSpan (S : Set V) : A.vac ∈ A.normalSpan S :=
  Submodule.mem_sInf.2 fun _ hW => hW.1

theorem subset_normalSpan (S : Set V) : S ⊆ A.normalSpan S :=
  fun _ hx => Submodule.mem_sInf.2 fun _ hW => hW.2.1 hx

theorem T_mem_normalSpan {S : Set V} {x : V} (hx : x ∈ A.normalSpan S) :
    A.T x ∈ A.normalSpan S :=
  Submodule.mem_sInf.2 fun _ hW => hW.2.2.1 _ (Submodule.mem_sInf.1 hx _ hW)

theorem prod_mem_normalSpan {S : Set V} {x y : V} (hx : x ∈ A.normalSpan S)
    (hy : y ∈ A.normalSpan S) : A.mode (-1) x y ∈ A.normalSpan S :=
  Submodule.mem_sInf.2 fun _ hW =>
    hW.2.2.2 _ (Submodule.mem_sInf.1 hx _ hW) _ (Submodule.mem_sInf.1 hy _ hW)

theorem normalSpan_le {S : Set V} {W : Submodule k V} (hvac : A.vac ∈ W) (hS : S ⊆ W)
    (hT : ∀ x ∈ W, A.T x ∈ W) (hprod : ∀ x ∈ W, ∀ y ∈ W, A.mode (-1) x y ∈ W) :
    A.normalSpan S ≤ W :=
  sInf_le ⟨hvac, hS, hT, hprod⟩

/-! ### Elementary mode identities -/

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

theorem mode_mem_grade' {i j e : ℕ} {a b : V} (n : ℤ) (ha : a ∈ A.grade i)
    (hb : b ∈ A.grade j) (he : (e : ℤ) = i + j - n - 1) : A.mode n a b ∈ A.grade e := by
  have h := A.mode_grade n ha hb (by omega)
  have h' : ((i : ℤ) + j - n - 1).toNat = e := by omega
  rwa [h'] at h

theorem eq_zero_of_mem_grade_of_ne {d e : ℕ} {x : V} (hd : x ∈ A.grade d)
    (he : x ∈ A.grade e) (hde : d ≠ e) : x = 0 := by
  have hdisj : Disjoint (A.grade d) (A.grade e) :=
    A.grade_internal.submodule_iSupIndep.pairwiseDisjoint hde
  exact Submodule.disjoint_def.1 hdisj x hd he

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

/-- Values of differential normal words of weight `d` (as `VertexAlgebra.IsNormalWord`). -/
inductive IsNormalWord (S : Set V) : ℕ → V → Prop
  | vac : IsNormalWord S 0 A.vac
  | gen {d : ℕ} {s : V} : s ∈ S → s ∈ A.grade d → IsNormalWord S d s
  | deriv {d : ℕ} {x : V} : IsNormalWord S d x → IsNormalWord S (d + 1) (A.T x)
  | prod {i j : ℕ} {x y : V} : IsNormalWord S i x → IsNormalWord S j y →
      IsNormalWord S (i + j) (A.mode (-1) x y)

def wordSpan (S : Set V) (d : ℕ) : Submodule k V :=
  Submodule.span k {x | A.IsNormalWord S d x}

inductive IsDerivOrProd (S : Set V) : ℕ → V → Prop
  | deriv {d : ℕ} {y : V} : y ∈ A.wordSpan S d → IsDerivOrProd S (d + 1) (A.T y)
  | prod {i j : ℕ} {y z : V} : 0 < i → 0 < j → y ∈ A.wordSpan S i → z ∈ A.wordSpan S j →
      IsDerivOrProd S (i + j) (A.mode (-1) y z)

inductive IsReduced (S : Set V) : ℕ → V → Prop
  | vac {d : ℕ} : IsReduced S d A.vac
  | gen {d : ℕ} {s : V} : s ∈ S → s ∈ A.grade d → IsReduced S d s
  | dp {d : ℕ} {x : V} : A.IsDerivOrProd S d x → IsReduced S d x

theorem normalWord_mem_grade {S : Set V} {d : ℕ} {x : V} (h : A.IsNormalWord S d x) :
    x ∈ A.grade d := by
  induction h with
  | vac => exact A.vac_mem_grade_zero
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

theorem isDerivOrProd_mem_wordSpan {S : Set V} {d : ℕ} {x : V} (h : A.IsDerivOrProd S d x) :
    x ∈ A.wordSpan S d := by
  cases h with
  | deriv hy => exact A.deriv_mem_wordSpan hy
  | prod _ _ hy hz => exact A.prod_mem_wordSpan hy hz

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

theorem normalSpan_eq_span_words {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) :
    A.normalSpan S = Submodule.span k {x | ∃ d, A.IsNormalWord S d x} := by
  rw [← A.iSup_wordSpan]
  exact le_antisymm (A.normalSpan_le_iSup_wordSpan hS)
    (iSup_le fun d => A.wordSpan_le_normalSpan S d)

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

/-- The normal span is the sum of its graded pieces. -/
theorem normalSpan_le_iSup_inf_grade {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) :
    A.normalSpan S ≤ ⨆ d, A.normalSpan S ⊓ A.grade d := by
  refine (A.normalSpan_le_iSup_wordSpan hS).trans (iSup_mono fun d => ?_)
  exact le_inf (A.wordSpan_le_normalSpan S d) (A.wordSpan_le_grade S d)

/-! ### Weight zero -/

/-- If no nonzero generator has weight zero, normal words of weight zero are multiples of the
vacuum. -/
theorem normalWord_weight_zero {S : Set V} (hS0 : ∀ s ∈ S, s ∈ A.grade 0 → s = 0) {d : ℕ}
    {x : V} (h : A.IsNormalWord S d x) : d = 0 → ∃ c : k, x = c • A.vac := by
  induction h with
  | vac => exact fun _ => ⟨1, (one_smul k _).symm⟩
  | @gen d s hs hsd =>
    intro hd
    subst hd
    exact ⟨0, by rw [hS0 s hs hsd, zero_smul]⟩
  | deriv _ _ => exact fun hd => absurd hd (by omega)
  | @prod i j x y hx hy ihx ihy =>
    intro hd
    obtain ⟨c, rfl⟩ := ihx (by omega)
    obtain ⟨c', rfl⟩ := ihy (by omega)
    exact ⟨c * c', by rw [A.mode_neg_one_smul_vac_left, smul_smul]⟩

theorem wordSpan_zero_le {S : Set V} (hS0 : ∀ s ∈ S, s ∈ A.grade 0 → s = 0) :
    A.wordSpan S 0 ≤ k ∙ A.vac := by
  refine Submodule.span_le.2 fun x hx => ?_
  obtain ⟨c, rfl⟩ := A.normalWord_weight_zero hS0 hx rfl
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)

theorem normalSpan_inf_grade_zero_le {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d)
    (hS0 : ∀ s ∈ S, s ∈ A.grade 0 → s = 0) : A.normalSpan S ⊓ A.grade 0 ≤ k ∙ A.vac := by
  rw [A.normalSpan_inf_grade hS]
  exact A.wordSpan_zero_le hS0

theorem normalWord_mem_span_reduced {S : Set V} (hS0 : ∀ s ∈ S, s ∈ A.grade 0 → s = 0)
    {d : ℕ} {x : V} (h : A.IsNormalWord S d x) :
    x ∈ Submodule.span k {y | A.IsReduced S d y} := by
  induction h with
  | vac => exact Submodule.subset_span IsReduced.vac
  | gen hs hd => exact Submodule.subset_span (IsReduced.gen hs hd)
  | deriv hx _ =>
    exact Submodule.subset_span
      (IsReduced.dp (IsDerivOrProd.deriv (A.normalWord_mem_wordSpan hx)))
  | @prod i j x y hx hy ihx ihy =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · obtain ⟨c, rfl⟩ := A.normalWord_weight_zero hS0 hx rfl
      rw [zero_add, A.mode_neg_one_smul_vac_left]
      exact Submodule.smul_mem _ c ihy
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · obtain ⟨c, rfl⟩ := A.normalWord_weight_zero hS0 hy rfl
      rw [add_zero, A.mode_neg_one_smul_vac_right]
      exact Submodule.smul_mem _ c ihx
    · exact Submodule.subset_span (IsReduced.dp (IsDerivOrProd.prod hi hj
        (A.normalWord_mem_wordSpan hx) (A.normalWord_mem_wordSpan hy)))

theorem wordSpan_le_span_reduced {S : Set V} (hS0 : ∀ s ∈ S, s ∈ A.grade 0 → s = 0) (d : ℕ) :
    A.wordSpan S d ≤ Submodule.span k {y | A.IsReduced S d y} :=
  Submodule.span_le.2 fun _ hx => A.normalWord_mem_span_reduced hS0 hx

/-! ### Filtered Wick reduction -/

def Closes (S : Set V) (i j : ℕ) : Prop :=
  ∀ x ∈ A.wordSpan S i, ∀ y ∈ A.wordSpan S j, ∀ n : ℕ, A.mode n x y ∈ A.normalSpan S

theorem closes_right_dp {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {m : ℕ}
    (IH : ∀ i j, i + j < m → A.Closes S i j) {i j : ℕ} (hm : i + j = m) {x y : V}
    (hx : x ∈ A.wordSpan S i) (hy : A.IsDerivOrProd S j y) (n : ℕ) :
    A.mode n x y ∈ A.normalSpan S := by
  have hxg : x ∈ A.grade i := A.wordSpan_le_grade S i hx
  cases hy with
  | @deriv j' y' hy' =>
    have key : A.mode n x (A.T y') =
        A.T (A.mode n x y') + (n : k) • A.mode ((n : ℤ) - 1) x y' := by
      rw [A.T_mode, A.mode_T, Int.cast_natCast]
      abel
    rw [key]
    refine Submodule.add_mem _ (A.T_mem_normalSpan (IH i j' (by omega) x hx y' hy' n)) ?_
    rcases n with _ | n
    · simp
    · refine Submodule.smul_mem _ _ ?_
      have e : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
      rw [e]
      exact IH i j' (by omega) x hx y' hy' n
  | @prod j₁ j₂ y₁ y₂ hj₁ hj₂ hy₁ hy₂ =>
    have hy₁g : y₁ ∈ A.grade j₁ := A.wordSpan_le_grade S j₁ hy₁
    have hcomm := A.commutator hxg hy₁g (n : ℤ) (-1) y₂
    rw [sub_eq_iff_eq_add] at hcomm
    rw [hcomm]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun t ht => ?_)
      (A.prod_mem_normalSpan (A.wordSpan_le_normalSpan S j₁ hy₁)
        (IH i j₂ (by omega) x hx y₂ hy₂ n))
    have ht' : t < i + j₁ := Finset.mem_range.1 ht
    have hzN : A.mode (t : ℤ) x y₁ ∈ A.normalSpan S := IH i j₁ (by omega) x hx y₁ hy₁ t
    have hzg : A.mode (t : ℤ) x y₁ ∈ A.grade (i + j₁ - t - 1) :=
      A.mode_mem_grade' (t : ℤ) hxg hy₁g (by omega)
    have hzW : A.mode (t : ℤ) x y₁ ∈ A.wordSpan S (i + j₁ - t - 1) :=
      A.mem_wordSpan_of_mem hS hzN hzg
    rcases lt_trichotomy t n with htn | htn | htn
    · refine Submodule.smul_mem _ _ ?_
      have e : (n : ℤ) + -1 - t = ((n - 1 - t : ℕ) : ℤ) := by omega
      rw [e]
      exact IH (i + j₁ - t - 1) j₂ (by omega) _ hzW y₂ hy₂ (n - 1 - t)
    · refine Submodule.smul_mem _ _ ?_
      have e : (n : ℤ) + -1 - t = -1 := by omega
      rw [e]
      exact A.prod_mem_normalSpan hzN (A.wordSpan_le_normalSpan S j₂ hy₂)
    · rw [zbinom_natCast_of_lt k htn, zero_smul]
      exact Submodule.zero_mem _

theorem closes_left_deriv {S : Set V} {m : ℕ} (IH : ∀ i j, i + j < m → A.Closes S i j)
    {i j : ℕ} (hm : i + 1 + j = m) {x y : V} (hx : x ∈ A.wordSpan S i)
    (hy : y ∈ A.wordSpan S j) (n : ℕ) : A.mode n (A.T x) y ∈ A.normalSpan S := by
  rw [A.mode_T]
  rcases n with _ | n
  · simp
  · refine Submodule.neg_mem _ (Submodule.smul_mem _ _ ?_)
    have e : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
    rw [e]
    exact IH i j (by omega) x hx y hy n

theorem closes_left_prod {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {m : ℕ}
    (IH : ∀ i j, i + j < m → A.Closes S i j) {i₁ i₂ j : ℕ} (hi₁ : 0 < i₁) (hi₂ : 0 < i₂)
    (hm : i₁ + i₂ + j = m) {x₁ x₂ y : V} (hx₁ : x₁ ∈ A.wordSpan S i₁)
    (hx₂ : x₂ ∈ A.wordSpan S i₂) (hy : y ∈ A.wordSpan S j) (n : ℕ) :
    A.mode n (A.mode (-1) x₁ x₂) y ∈ A.normalSpan S := by
  have hxg : A.mode (-1) x₁ x₂ ∈ A.grade (i₁ + i₂) :=
    A.wordSpan_le_grade S _ (A.prod_mem_wordSpan hx₁ hx₂)
  have hyg : y ∈ A.grade j := A.wordSpan_le_grade S j hy
  rw [A.skew hyg hxg (n : ℤ)]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
    (A.T_pow_mem (fun z hz => A.T_mem_normalSpan hz) t ?_)
  have e : (n : ℤ) + t = ((n + t : ℕ) : ℤ) := by push_cast; ring
  rw [e]
  exact A.closes_right_dp hS IH (by omega) hy (IsDerivOrProd.prod hi₁ hi₂ hx₁ hx₂) (n + t)

theorem closes_left_dp {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {m : ℕ}
    (IH : ∀ i j, i + j < m → A.Closes S i j) {i j : ℕ} (hm : i + j = m) {x y : V}
    (hx : A.IsDerivOrProd S i x) (hy : y ∈ A.wordSpan S j) (n : ℕ) :
    A.mode n x y ∈ A.normalSpan S := by
  cases hx with
  | deriv hx' => exact A.closes_left_deriv IH hm hx' hy n
  | prod hi₁ hi₂ hx₁ hx₂ => exact A.closes_left_prod hS IH hi₁ hi₂ hm hx₁ hx₂ hy n

theorem closes_step {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d)
    (hS0 : ∀ s ∈ S, s ∈ A.grade 0 → s = 0) {m : ℕ}
    (IH : ∀ i j, i + j < m → A.Closes S i j) {i j : ℕ} (hm : i + j = m)
    (hgen : ∀ s t, s ∈ S → s ∈ A.grade i → t ∈ S → t ∈ A.grade j →
      ∀ n : ℕ, A.mode n s t ∈ A.normalSpan S) :
    A.Closes S i j := by
  intro x hx y hy n
  refine bilin_mem_of_mem_span (A.mode n) ?_ (A.wordSpan_le_span_reduced hS0 i hx)
    (A.wordSpan_le_span_reduced hS0 j hy)
  rintro a (ha : A.IsReduced S i a) b (hb : A.IsReduced S j b)
  cases ha with
  | vac =>
    rw [A.vac_mode_natCast]
    exact Submodule.zero_mem _
  | gen hs hsg =>
    cases hb with
    | vac =>
      rw [A.mode_vac_natCast]
      exact Submodule.zero_mem _
    | gen ht htg => exact hgen _ _ hs hsg ht htg n
    | dp hb =>
      exact A.closes_right_dp hS IH hm
        (A.normalWord_mem_wordSpan (IsNormalWord.gen hs hsg)) hb n
  | dp ha =>
    cases hb with
    | vac =>
      rw [A.mode_vac_natCast]
      exact Submodule.zero_mem _
    | gen ht htg =>
      exact A.closes_left_dp hS IH hm ha
        (A.normalWord_mem_wordSpan (IsNormalWord.gen ht htg)) n
    | dp hb => exact A.closes_right_dp hS IH hm (A.isDerivOrProd_mem_wordSpan ha) hb n

/-- **Lemma `lem:filtered-wick` (a)** for weak vertex algebras. -/
theorem closes_of_lt {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d)
    (hS0 : ∀ s ∈ S, s ∈ A.grade 0 → s = 0) {w : ℕ}
    (hgen : ∀ i j s t, s ∈ S → s ∈ A.grade i → t ∈ S → t ∈ A.grade j → i + j < w →
      ∀ n : ℕ, A.mode n s t ∈ A.normalSpan S) :
    ∀ i j, i + j < w → A.Closes S i j := by
  suffices H : ∀ m, m < w → ∀ i j, i + j = m → A.Closes S i j from
    fun i j hij => H _ hij i j rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IHm =>
    intro hmw i j hm
    refine A.closes_step hS hS0 (fun i' j' h' => IHm _ h' (by omega) i' j' rfl) hm ?_
    intro s t hs hsg ht htg n
    exact hgen i j s t hs hsg ht htg (by omega) n

/-! ### Closure under all modes -/

/-- If all singular products of generators lie in `𝒩(S)`, so do all singular products of
elements of `𝒩(S)`. -/
theorem normalSpan_nonneg_closed {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d)
    (hS0 : ∀ s ∈ S, s ∈ A.grade 0 → s = 0)
    (hgen : ∀ s ∈ S, ∀ t ∈ S, ∀ n : ℕ, A.mode n s t ∈ A.normalSpan S)
    {x y : V} (hx : x ∈ A.normalSpan S) (hy : y ∈ A.normalSpan S) (n : ℕ) :
    A.mode n x y ∈ A.normalSpan S := by
  rw [A.normalSpan_eq_span_words hS] at hx hy
  refine bilin_mem_of_mem_span (A.mode n) ?_ hx hy
  rintro a ⟨i, ha⟩ b ⟨j, hb⟩
  refine A.closes_of_lt hS hS0 (w := i + j + 1) ?_ i j (by omega) a
    (A.normalWord_mem_wordSpan ha) b (A.normalWord_mem_wordSpan hb) n
  intro i' j' s t hs _ ht _ _ n'
  exact hgen s hs t ht n'

/-- Negative modes: `x_(-1-r) y = (r + 1)⁻¹ (T x)_(-r) y`. -/
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

/-- **Closure.** If all singular products of generators lie in `𝒩(S)` (generators homogeneous,
no nonzero generator of weight zero), then `𝒩(S)` is closed under every mode. -/
theorem normalSpan_isClosed [CharZero k] {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d)
    (hS0 : ∀ s ∈ S, s ∈ A.grade 0 → s = 0)
    (hgen : ∀ s ∈ S, ∀ t ∈ S, ∀ n : ℕ, A.mode n s t ∈ A.normalSpan S) (n : ℤ) :
    ∀ x ∈ A.normalSpan S, ∀ y ∈ A.normalSpan S, A.mode n x y ∈ A.normalSpan S := by
  intro x hx y hy
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact A.normalSpan_nonneg_closed hS hS0 hgen hx hy n
  · have e : n = -1 - ((-1 - n).toNat : ℤ) := by omega
    rw [e]
    exact A.neg_mode_mem (fun z hz => A.T_mem_normalSpan hz)
      (fun a ha b hb => A.prod_mem_normalSpan ha hb) _ x hx y hy

/-! ### Sub-vertex algebras of CFT type -/

section Sub

variable {D : Submodule k V} (hmode : ∀ (n : ℤ), ∀ x ∈ D, ∀ y ∈ D, A.mode n x y ∈ D)

/-- The modes restricted to a subspace closed under all modes. -/
def subMode (n : ℤ) : D →ₗ[k] D →ₗ[k] D :=
  LinearMap.mk₂ k (fun x y => ⟨A.mode n x y, hmode n x x.2 y y.2⟩)
    (fun x₁ x₂ y => Subtype.ext (by simp))
    (fun c x y => Subtype.ext (by simp))
    (fun x y₁ y₂ => Subtype.ext (by simp))
    (fun c x y => Subtype.ext (by simp))

theorem subMode_coe (n : ℤ) (x y : D) : (A.subMode hmode n x y : V) = A.mode n x y := rfl

theorem restrict_pow_coe {f : V →ₗ[k] V} (hf : ∀ x ∈ D, f x ∈ D) (t : ℕ) (x : D) :
    (((f.restrict hf) ^ t) x : V) = (f ^ t) x := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    simp only [pow_succ, Module.End.mul_apply, ih, LinearMap.coe_restrict_apply]

theorem sub_grade_internal (hgraded : D ≤ ⨆ d, D ⊓ A.grade d) :
    DirectSum.IsInternal (fun d => (A.grade d).comap D.subtype) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · intro d
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hle : (⨆ (e : ℕ) (_ : e ≠ d), (A.grade e).comap D.subtype) ≤
        (⨆ (e : ℕ) (_ : e ≠ d), A.grade e).comap D.subtype :=
      iSup₂_le fun e he => Submodule.comap_mono (le_iSup₂_of_le e he le_rfl)
    have h0 : (x : V) = 0 :=
      Submodule.disjoint_def.1 (A.grade_internal.submodule_iSupIndep d) _ hx (hle hx')
    exact Subtype.ext h0
  · rw [eq_top_iff]
    rintro x -
    have hx : (x : V) ∈ ⨆ d, D ⊓ A.grade d := hgraded x.2
    have hmap : Submodule.map D.subtype (⨆ d, (A.grade d).comap D.subtype) =
        ⨆ d, D ⊓ A.grade d := by
      rw [Submodule.map_iSup]
      simp only [Submodule.map_comap_subtype]
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 hx
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy

/-- **A sub-vertex algebra of CFT type.**  A subspace of a weak vertex algebra that contains the
vacuum, is closed under `T` and under all modes, is graded, and whose weight-zero part is
`k·1`, is a vertex algebra in the sense of the shared interface. -/
noncomputable def subVertexAlgebra (hvac : A.vac ∈ D) (hT : ∀ x ∈ D, A.T x ∈ D)
    (hgraded : D ≤ ⨆ d, D ⊓ A.grade d) (hzero : D ⊓ A.grade 0 ≤ k ∙ A.vac) :
    VertexAlgebra k D where
  mode := A.subMode hmode
  vac := ⟨A.vac, hvac⟩
  T := A.T.restrict hT
  grade := fun d => (A.grade d).comap D.subtype
  grade_internal := A.sub_grade_internal hgraded
  grade_zero := by
    ext x
    rw [Submodule.mem_comap, Submodule.mem_span_singleton]
    constructor
    · intro hx
      have hx' : (x : V) ∈ k ∙ A.vac := hzero ⟨x.2, hx⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx'
      exact ⟨c, Subtype.ext hc⟩
    · rintro ⟨c, rfl⟩
      exact Submodule.smul_mem _ c A.vac_mem_grade_zero
  mode_grade := fun n ha hb h =>
    Submodule.mem_comap.2 (A.mode_grade n (Submodule.mem_comap.1 ha) (Submodule.mem_comap.1 hb) h)
  mode_trunc := fun n ha hb h =>
    Subtype.ext (A.mode_trunc n (Submodule.mem_comap.1 ha) (Submodule.mem_comap.1 hb) h)
  T_grade := fun ha => Submodule.mem_comap.2 (A.T_grade (Submodule.mem_comap.1 ha))
  vac_mode := fun n b => by
    apply Subtype.ext
    show A.mode n A.vac (b : V) = ((if n = -1 then b else 0 : D) : V)
    rw [A.vac_mode]
    split_ifs <;> rfl
  mode_vac_nonneg := fun n a h => Subtype.ext (A.mode_vac_nonneg n a h)
  mode_vac_neg_one := fun a => Subtype.ext (A.mode_vac_neg_one a)
  T_eq := fun a => Subtype.ext (A.T_eq a)
  mode_T := fun n a b => Subtype.ext (A.mode_T n a b)
  T_mode := fun n a b => Subtype.ext (A.T_mode n a b)
  commutator := fun {i j a b} ha hb m n c => by
    have ha' : (a : V) ∈ A.grade i := ha
    have hb' : (b : V) ∈ A.grade j := hb
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, subMode_coe]
    exact A.commutator ha' hb' m n c
  iterate := fun {i j l a b c} ha hb hc m n => by
    have ha' : (a : V) ∈ A.grade i := ha
    have hb' : (b : V) ∈ A.grade j := hb
    have hc' : (c : V) ∈ A.grade l := hc
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, subMode_coe]
    exact A.iterate ha' hb' hc' m n
  skew := fun {i j a b} ha hb n => by
    have ha' : (a : V) ∈ A.grade i := ha
    have hb' : (b : V) ∈ A.grade j := hb
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, subMode_coe, restrict_pow_coe]
    exact A.skew ha' hb' n

end Sub

end WeakVertexAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.WeakVertexAlgebra.normalSpan_isClosed
#print axioms HaagerupIzumi.C8.WeakVertexAlgebra.subVertexAlgebra
#print axioms HaagerupIzumi.C8.WeakVertexAlgebra.normalSpan_inf_grade_zero_le
#print axioms HaagerupIzumi.C8.WeakVertexAlgebra.normalSpan_le_iSup_inf_grade
