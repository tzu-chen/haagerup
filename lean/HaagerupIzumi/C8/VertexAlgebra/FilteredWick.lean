module

public import HaagerupIzumi.C8.VertexAlgebra.NormalWords

@[expose] public section

/-!
# Filtered Wick reduction

Lemma `lem:filtered-wick` (line 2111 of `c8_expanded_20260929/haagerup_c8_expanded.tex`).
Let `S` be a set of homogeneous vectors of a vertex algebra `A` (interface
`HaagerupIzumi.C8.VertexAlgebra`) and write `𝒩 = A.normalSpan S`.  Fix `w` and suppose that
every singular product `s_(n) t` (`n ≥ 0`) of two generators `s ∈ S ∩ V_i`, `t ∈ S ∩ V_j`
with `i + j < w` lies in `𝒩`.  Then:

* (a) `closes_of_lt`, `filtered_wick_lt`: `x_(n) y ∈ 𝒩` for all normal elements `x ∈ 𝒩 ∩ V_i`,
  `y ∈ 𝒩 ∩ V_j` with `i + j < w` and all `n ≥ 0`;
* (b) `closes_derivProd_left`, `closes_derivProd_right`: the same holds at total weight
  `i + j = w` if one of the two inputs is a combination of derivatives `T u` of normal
  elements and of products `u_(-1) v` of two positive-weight normal elements
  (`derivProdSpan`).

The proof is the mode form of the manuscript's λ-bracket argument, by strong induction on the
total weight: vacuum factors have vanishing singular products; `x_(n) (T y) =
T (x_(n) y) + n x_(n-1) y` and `(T x)_(n) y = -n x_(n-1) y` remove derivatives; the
commutator formula
`x_(n) (y₁_(-1) y₂) = y₁_(-1) (x_(n) y₂) + ∑_{t ≤ n} (n choose t) (x_(t) y₁)_(n-1-t) y₂`
treats a product on the right (the coefficients `x_(t) y₁` are decomposed into normal words
of weight `wt x + wt y₁ - t - 1` by `normalSpan_inf_grade`); skew symmetry moves a product
on the left to the right at the same total weight.  Generators of weight zero are allowed
(they are multiples of the vacuum).  Only the interface fields are used; the only hypothesis
is the explicit closure of generator pairs below weight `w`.
-/

namespace HaagerupIzumi.C8

namespace VertexAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable (A : VertexAlgebra k V)

/-- `A.Closes S i j`: every singular product `x_(n) y` (`n ≥ 0`) of a normal element `x` of
weight `i` with a normal element `y` of weight `j` lies in the normal span. -/
def Closes (S : Set V) (i j : ℕ) : Prop :=
  ∀ x ∈ A.wordSpan S i, ∀ y ∈ A.wordSpan S j, ∀ n : ℕ, A.mode n x y ∈ A.normalSpan S

/-- A derivative or a product on the right, assuming closure at smaller total weight. -/
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

/-- A derivative on the left, assuming closure at smaller total weight. -/
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

/-- A product on the left: skew symmetry moves it to the right at the same total weight. -/
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

/-- A derivative or a product on the left, assuming closure at smaller total weight. -/
theorem closes_left_dp {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {m : ℕ}
    (IH : ∀ i j, i + j < m → A.Closes S i j) {i j : ℕ} (hm : i + j = m) {x y : V}
    (hx : A.IsDerivOrProd S i x) (hy : y ∈ A.wordSpan S j) (n : ℕ) :
    A.mode n x y ∈ A.normalSpan S := by
  cases hx with
  | deriv hx' => exact A.closes_left_deriv IH hm hx' hy n
  | prod hi₁ hi₂ hx₁ hx₂ => exact A.closes_left_prod hS IH hi₁ hi₂ hm hx₁ hx₂ hy n

/-- The induction step: closure at total weight `m` from closure below `m` and closure of the
generator pairs of weights `(i, j)`. -/
theorem closes_step {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {m : ℕ}
    (IH : ∀ i j, i + j < m → A.Closes S i j) {i j : ℕ} (hm : i + j = m)
    (hgen : ∀ s t, s ∈ S → s ∈ A.grade i → t ∈ S → t ∈ A.grade j →
      ∀ n : ℕ, A.mode n s t ∈ A.normalSpan S) :
    A.Closes S i j := by
  intro x hx y hy n
  refine bilin_mem_of_mem_span (A.mode n) ?_ (A.wordSpan_le_span_reduced S i hx)
    (A.wordSpan_le_span_reduced S j hy)
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

/-- **Lemma `lem:filtered-wick` (a), word form.** If all generator pairs of total weight `< w`
have singular products in `𝒩(S)`, then so do all pairs of normal elements of total weight
`< w`. -/
theorem closes_of_lt {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {w : ℕ}
    (hgen : ∀ i j s t, s ∈ S → s ∈ A.grade i → t ∈ S → t ∈ A.grade j → i + j < w →
      ∀ n : ℕ, A.mode n s t ∈ A.normalSpan S) :
    ∀ i j, i + j < w → A.Closes S i j := by
  suffices H : ∀ m, m < w → ∀ i j, i + j = m → A.Closes S i j from
    fun i j hij => H _ hij i j rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IHm =>
    intro hmw i j hm
    refine A.closes_step hS (fun i' j' h' => IHm _ h' (by omega) i' j' rfl) hm ?_
    intro s t hs hsg ht htg n
    exact hgen i j s t hs hsg ht htg (by omega) n

/-- **Lemma `lem:filtered-wick` (b), left input a derivative or a product.** -/
theorem closes_derivProd_left {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {w : ℕ}
    (hgen : ∀ i j s t, s ∈ S → s ∈ A.grade i → t ∈ S → t ∈ A.grade j → i + j < w →
      ∀ n : ℕ, A.mode n s t ∈ A.normalSpan S)
    {i j : ℕ} (hw : i + j = w) {x y : V} (hx : x ∈ A.derivProdSpan S i)
    (hy : y ∈ A.wordSpan S j) (n : ℕ) : A.mode n x y ∈ A.normalSpan S := by
  refine bilin_mem_of_mem_span (A.mode n) ?_ hx hy
  intro a ha b hb
  exact A.closes_left_dp hS (A.closes_of_lt hS hgen) hw ha (A.normalWord_mem_wordSpan hb) n

/-- **Lemma `lem:filtered-wick` (b), right input a derivative or a product.** -/
theorem closes_derivProd_right {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {w : ℕ}
    (hgen : ∀ i j s t, s ∈ S → s ∈ A.grade i → t ∈ S → t ∈ A.grade j → i + j < w →
      ∀ n : ℕ, A.mode n s t ∈ A.normalSpan S)
    {i j : ℕ} (hw : i + j = w) {x y : V} (hx : x ∈ A.wordSpan S i)
    (hy : y ∈ A.derivProdSpan S j) (n : ℕ) : A.mode n x y ∈ A.normalSpan S := by
  refine bilin_mem_of_mem_span (A.mode n) ?_ hx hy
  intro a ha b hb
  exact A.closes_right_dp hS (A.closes_of_lt hS hgen) hw (A.normalWord_mem_wordSpan ha) hb n

/-- **Lemma `lem:filtered-wick` (a).** Let `S` consist of homogeneous vectors and suppose that
every singular product of two generators of total weight `< w` lies in `𝒩(S)`.  Then
`x_(n) y ∈ 𝒩(S)` for all `x ∈ 𝒩(S) ∩ V_i`, `y ∈ 𝒩(S) ∩ V_j` with `i + j < w` and all
`n ≥ 0`. -/
theorem filtered_wick_lt {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {w : ℕ}
    (hgen : ∀ i j s t, s ∈ S → s ∈ A.grade i → t ∈ S → t ∈ A.grade j → i + j < w →
      ∀ n : ℕ, A.mode n s t ∈ A.normalSpan S)
    {i j : ℕ} (hij : i + j < w) {x y : V} (hx : x ∈ A.normalSpan S ⊓ A.grade i)
    (hy : y ∈ A.normalSpan S ⊓ A.grade j) (n : ℕ) : A.mode n x y ∈ A.normalSpan S := by
  rw [A.normalSpan_inf_grade hS] at hx hy
  exact A.closes_of_lt hS hgen i j hij x hx y hy n

/-- **Lemma `lem:filtered-wick` (b).** Under the hypothesis of (a), `x_(n) y ∈ 𝒩(S)` also at
total weight `i + j = w` when `x` or `y` is a combination of derivatives of normal elements and
of `(-1)`-products of two positive-weight normal elements. -/
theorem filtered_wick_eq {S : Set V} (hS : ∀ s ∈ S, ∃ d, s ∈ A.grade d) {w : ℕ}
    (hgen : ∀ i j s t, s ∈ S → s ∈ A.grade i → t ∈ S → t ∈ A.grade j → i + j < w →
      ∀ n : ℕ, A.mode n s t ∈ A.normalSpan S)
    {i j : ℕ} (hij : i + j = w) {x y : V} (hx : x ∈ A.normalSpan S ⊓ A.grade i)
    (hy : y ∈ A.normalSpan S ⊓ A.grade j)
    (hdp : x ∈ A.derivProdSpan S i ∨ y ∈ A.derivProdSpan S j) (n : ℕ) :
    A.mode n x y ∈ A.normalSpan S := by
  rw [A.normalSpan_inf_grade hS] at hx hy
  rcases hdp with hdp | hdp
  · exact A.closes_derivProd_left hS hgen hij hdp hy n
  · exact A.closes_derivProd_right hS hgen hij hx hdp n

end VertexAlgebra

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.VertexAlgebra.closes_of_lt
#print axioms HaagerupIzumi.C8.VertexAlgebra.filtered_wick_lt
#print axioms HaagerupIzumi.C8.VertexAlgebra.filtered_wick_eq
#print axioms HaagerupIzumi.C8.VertexAlgebra.closes_derivProd_left
#print axioms HaagerupIzumi.C8.VertexAlgebra.closes_derivProd_right
