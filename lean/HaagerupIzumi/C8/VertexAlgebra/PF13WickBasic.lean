module

public import HaagerupIzumi.C8.VertexAlgebra.PF13

@[expose] public section

/-!
# Filtered Wick probes: right-normed spanning and the probe lemma

General lemmas for the PF13 Wick claims `A_6, A_7, A_8, B_7` in the proof of Proposition
`prop:pf13-finite-reconstruction` (lines 2750–2811 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`).  The setting is a weak vertex algebra `P`
(`WeakVertexAlgebra`; intended instance the product `V × V'`) and the differential normal span
`𝒩 = P.normalSpan S` of a set `S` of homogeneous generators.

* `Rx P N x f`: every singular product `x_(m) y` with `y ∈ N ∩ P_f`, `m ≥ 0`, lies in `N`
  ("`x` closes against weight `f`").  `Rsub P N f` is the submodule of such `x`; it contains
  the vacuum and is stable under `T` (`T_mem_Rsub`), so skew symmetry (`PF13.rev_mem`) and the
  explicit rows of `PF13.lean` can be evaluated inside it.  `Cl P N p f`: every element of
  `N ∩ P_p` closes against weight `f`.
* `rnf` (**right-normed spanning**).  If all pairs of normal elements of total weight `< w`
  close, then for `1 ≤ D ≤ w` every element of `𝒩 ∩ P_D` is a linear combination of
  right-normed monomials `g_(-1-s) u` (`RNF`), with `g ∈ S` of weight `e > 0`, `u ∈ 𝒩 ∩ P_f`,
  `e + s + f = D`.  Normal words of arbitrary parenthesization are rewritten with the iterate
  formula; only closure below weight `w` is used.  This normal form replaces the manuscript's
  step "Virasoro creation operators can be moved to the outside of any normal word using
  already known commutators" (lines 2759–2760): instead of moving `L` outside, every normal
  word is brought into right-normed form.
* `probe` (**filtered Wick step for one probe vector `x`**).  `x` closes against weight `D` as
  soon as it closes against all lower weights, its products `x_(t) g` with the generators of
  weight `≤ D` lie in `𝒩`, and these products close against the weights `f ≤ D - wt g`.  The
  proof applies the commutator formula
  `x_(m) (g_(-1-s) u) = g_(-1-s) (x_(m) u) + ∑_t (m choose t) (x_(t) g)_(m-1-s-t) u`
  to right-normed monomials; it is the mode form of the noncommutative Wick identity
  (line 2781).  The term `g_(-1-s) (x_(m) u)` is the `:g [x_λ u]:` part; the terms
  `(x_(t) g)_(m-1-s-t) u` with negative mode `m-1-s-t < 0` are the `:[x_λ g] u:` part, and only
  those with nonnegative mode form the Wick integral.
* `Rx_of_top`, `Rx_of_gen`, `Cl_of_gens`: the forms used in `PF13Wick.lean`.  In each, the
  only inputs at the top total weight are listed explicitly; everything else is closure at
  lower total weight.
* `Rx_wt_zero`, `Rx_wt_one`: weight-zero normal elements are multiples of the vacuum, and the
  weight-one part of `𝒩` vanishes when no generator has weight one.

No hypothesis is external: only the fields of `WeakVertexAlgebra` are used.
-/

namespace HaagerupIzumi.C8

namespace PF13Wick

open scoped BigOperators

variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
variable (P : WeakVertexAlgebra k W)

section Closure

variable (N : Submodule k W)

/-- `Rx P N x f`: every singular product `x_(m) y` (`m ≥ 0`) with `y ∈ N ∩ P_f` lies in `N`. -/
def Rx (x : W) (f : ℕ) : Prop :=
  ∀ y ∈ N, y ∈ P.grade f → ∀ m : ℕ, P.mode m x y ∈ N

/-- The vectors that close against weight `f`, as a submodule. -/
def Rsub (f : ℕ) : Submodule k W where
  carrier := {x | Rx P N x f}
  add_mem' := by
    intro x x' hx hx'
    show Rx P N (x + x') f
    intro y hy hyf m
    rw [map_add, LinearMap.add_apply]
    exact N.add_mem ((hx : Rx P N x f) y hy hyf m) ((hx' : Rx P N x' f) y hy hyf m)
  zero_mem' := by
    show Rx P N 0 f
    intro y _ _ m
    rw [map_zero, LinearMap.zero_apply]
    exact N.zero_mem
  smul_mem' := by
    intro c x hx
    show Rx P N (c • x) f
    intro y hy hyf m
    rw [map_smul, LinearMap.smul_apply]
    exact N.smul_mem c ((hx : Rx P N x f) y hy hyf m)

theorem mem_Rsub {f : ℕ} {x : W} : x ∈ Rsub P N f ↔ Rx P N x f := Iff.rfl

theorem Rx_zero_vec (f : ℕ) : Rx P N 0 f :=
  (mem_Rsub P N).1 (Rsub P N f).zero_mem

/-- `Rsub P N f` is stable under translation: `(T x)_(m) y = -m x_(m-1) y`. -/
theorem T_mem_Rsub {f : ℕ} {x : W} (hx : x ∈ Rsub P N f) : P.T x ∈ Rsub P N f := by
  rw [mem_Rsub] at hx ⊢
  intro y hy hyf m
  rw [P.mode_T]
  rcases m with _ | m
  · simp
  · refine N.neg_mem (N.smul_mem _ ?_)
    have e : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
    rw [e]
    exact hx y hy hyf m

/-- The vacuum closes against every weight. -/
theorem vac_mem_Rsub (f : ℕ) : P.vac ∈ Rsub P N f := by
  rw [mem_Rsub]
  intro y _ _ m
  rw [P.vac_mode_natCast]
  exact N.zero_mem

/-- `Cl P N p f`: every `x ∈ N ∩ P_p` closes against weight `f`. -/
def Cl (p f : ℕ) : Prop := ∀ x ∈ N, x ∈ P.grade p → Rx P N x f

/-- Skew symmetry: closure of `(p, f)` gives closure of `(f, p)`. -/
theorem Cl_symm (hT : ∀ x ∈ N, P.T x ∈ N) {p f : ℕ} (h : Cl P N p f) : Cl P N f p := by
  intro y hy hyf x hx hxp m
  exact PF13.rev_mem P hT hxp hyf m fun n _ => h x hx hxp y hy hyf n

/-- A product `x_(t) g` of homogeneous vectors closes against weight `f` if it lies in `N`
and closure holds for its weight `e + eg - t - 1` (it vanishes for `t ≥ e + eg`). -/
theorem Rx_mode_of_Cl {x g : W} {e eg f : ℕ} (hx : x ∈ P.grade e) (hg : g ∈ P.grade eg)
    (t : ℕ) (hmem : P.mode t x g ∈ N) (hCl : t + 1 ≤ e + eg → Cl P N (e + eg - t - 1) f) :
    Rx P N (P.mode t x g) f := by
  rcases Nat.lt_or_ge t (e + eg) with ht | ht
  · exact hCl (by omega) _ hmem (P.mode_mem_grade' (t : ℤ) hx hg (by omega))
  · rw [P.mode_trunc (t : ℤ) hx hg (by omega)]
    exact Rx_zero_vec P N f

/-- The `A_r`-type instances consumed by the iterate identities: if `x` closes against all
weights `< wt y + wt z`, then `x_(m) (y_(j) z) ∈ N` for all `m, j ≥ 0`. -/
theorem claim_of_Rx {x y z : W} {ey ez : ℕ} (hy : y ∈ P.grade ey) (hz : z ∈ P.grade ez)
    (hrow : ∀ j : ℕ, P.mode j y z ∈ N) (hR : ∀ f, f < ey + ez → Rx P N x f) :
    ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m x (P.mode j y z) ∈ N := by
  intro m j hm hj
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hj
  rcases Nat.lt_or_ge j (ey + ez) with hjl | hjl
  · exact hR (ey + ez - j - 1) (by omega) _ (hrow j) (P.mode_mem_grade' _ hy hz (by omega)) m
  · rw [P.mode_trunc (j : ℤ) hy hz (by omega), map_zero]
    exact N.zero_mem

/-- Every mode `x_(n) y` (`n : ℤ`) of elements of a `T`-stable, `(-1)`-closed subspace lies in it
once the nonnegative ones do (characteristic zero). -/
theorem mode_mem_int [CharZero k] (hT : ∀ x ∈ N, P.T x ∈ N)
    (hprod : ∀ x ∈ N, ∀ y ∈ N, P.mode (-1) x y ∈ N) {x y : W} (hx : x ∈ N) (hy : y ∈ N)
    (n : ℤ) (h : ∀ m : ℕ, (m : ℤ) = n → P.mode m x y ∈ N) : P.mode n x y ∈ N := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact h m rfl
  · have e : n = -1 - ((-1 - n).toNat : ℤ) := by omega
    rw [e]
    exact P.neg_mode_mem hT hprod _ x hx y hy

end Closure

/-! ### Right-normed spanning -/

section RNF

variable {S : Set W}

/-- Right-normed monomials `g_(-1-s) u` of weight `D`: `g ∈ S` of weight `e > 0`,
`u ∈ 𝒩(S)` of weight `f`, `e + s + f = D`. -/
def RNF (S : Set W) (D : ℕ) : Set W :=
  {y | ∃ (g u : W) (e s f : ℕ), g ∈ S ∧ g ∈ P.grade e ∧ 0 < e ∧ u ∈ P.normalSpan S ∧
    u ∈ P.grade f ∧ e + s + f = D ∧ y = P.mode (-1 - (s : ℤ)) g u}

theorem Cl_of_closes (hS : ∀ s ∈ S, ∃ d, s ∈ P.grade d) {i j : ℕ} (h : P.Closes S i j) :
    Cl P (P.normalSpan S) i j :=
  fun x hx hxi y hy hyj m =>
    h x (P.mem_wordSpan_of_mem hS hx hxi) y (P.mem_wordSpan_of_mem hS hy hyj) m

/-- Weight-zero normal elements are multiples of the vacuum, so everything closes against
weight zero. -/
theorem Rx_wt_zero (hS : ∀ s ∈ S, ∃ d, s ∈ P.grade d) (hS0 : ∀ s ∈ S, s ∈ P.grade 0 → s = 0)
    (x : W) : Rx P (P.normalSpan S) x 0 := by
  intro y hy hy0 m
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1
    (P.normalSpan_inf_grade_zero_le hS hS0 (Submodule.mem_inf.2 ⟨hy, hy0⟩))
  rw [map_smul, P.mode_vac_natCast, smul_zero]
  exact Submodule.zero_mem _

/-- The second half of the right-normed spanning induction (target weight `D` fixed):
`u_(-1-r) Y` is right-normed for `u ∈ 𝒩 ∩ P_p`, `1 ≤ p < D`, `Y ∈ 𝒩 ∩ P_q`,
`p + q + r = D`, given right-normed spanning in the weights `1 ≤ p < D`. -/
theorem rnf_prod [CharZero k] (hS : ∀ s ∈ S, ∃ d, s ∈ P.grade d)
    (hS0 : ∀ s ∈ S, s ∈ P.grade 0 → s = 0) {w : ℕ}
    (hcl : ∀ i j, i + j < w → Cl P (P.normalSpan S) i j) {D : ℕ} (hDw : D ≤ w)
    (hi : ∀ p, 1 ≤ p → p < D → ∀ y ∈ P.normalSpan S, y ∈ P.grade p →
      y ∈ Submodule.span k (RNF P S p)) :
    ∀ p, 1 ≤ p → p < D → ∀ u ∈ P.normalSpan S, u ∈ P.grade p → ∀ q r : ℕ, p + q + r = D →
      ∀ Y ∈ P.normalSpan S, Y ∈ P.grade q →
        P.mode (-1 - (r : ℤ)) u Y ∈ Submodule.span k (RNF P S D) := by
  have hT : ∀ x ∈ P.normalSpan S, P.T x ∈ P.normalSpan S := fun _ h => P.T_mem_normalSpan h
  have hprod : ∀ x ∈ P.normalSpan S, ∀ y ∈ P.normalSpan S,
      P.mode (-1) x y ∈ P.normalSpan S :=
    fun _ hx _ hy => P.prod_mem_normalSpan hx hy
  intro p
  induction p using Nat.strong_induction_on with
  | _ p IH =>
  intro hp1 hpD u hu hup q r hpqr Y hY hYq
  refine P.mode_mem_of_mem_span_left ?_ (hi p hp1 hpD u hu hup)
  rintro _ ⟨g, v, e, s, f, hgS, hge, he, hv, hvf, hesf, rfl⟩
  rw [P.iterate hge hvf hYq (-1 - (s : ℤ)) (-1 - (r : ℤ))]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
    (Submodule.sub_mem _ ?_ (Submodule.smul_mem _ _ ?_))
  · -- the term `g_(-1-s-t) (v_(-1-r+t) Y)` is right-normed
    rcases Nat.lt_or_ge (f + q + r) t with htl | htl
    · rw [P.mode_trunc (-1 - (r : ℤ) + t) hvf hYq (by omega), map_zero]
      exact Submodule.zero_mem _
    · have hZN : P.mode (-1 - (r : ℤ) + t) v Y ∈ P.normalSpan S := by
        rcases Nat.lt_or_ge r t with hrt | hrt
        · have e1 : (-1 - (r : ℤ) + t) = ((t - r - 1 : ℕ) : ℤ) := by omega
          rw [e1]
          exact hcl f q (by omega) v hv hvf Y hY hYq (t - r - 1)
        · have e1 : (-1 - (r : ℤ) + t) = -1 - ((r - t : ℕ) : ℤ) := by omega
          rw [e1]
          exact P.neg_mode_mem hT hprod (r - t) v hv Y hY
      have hZg : P.mode (-1 - (r : ℤ) + t) v Y ∈ P.grade (f + q + r - t) :=
        P.mode_mem_grade' _ hvf hYq (by omega)
      have e2 : (-1 - (s : ℤ) - (t : ℤ)) = -1 - ((s + t : ℕ) : ℤ) := by push_cast; ring
      rw [e2]
      exact Submodule.subset_span ⟨g, _, e, s + t, f + q + r - t, hgS, hge, he, hZN, hZg,
        by omega, rfl⟩
  · -- the term `v_(-2-s-r-t) (g_(t) Y)`: induction on the weight of `v`
    rcases Nat.eq_zero_or_pos f with hf0 | hf1
    · rw [hf0] at hvf
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1
        (P.normalSpan_inf_grade_zero_le hS hS0 (Submodule.mem_inf.2 ⟨hv, hvf⟩))
      have hne : (-1 - (s : ℤ) + (-1 - (r : ℤ)) - (t : ℤ)) ≠ -1 := by omega
      rw [map_smul, LinearMap.smul_apply, P.vac_mode, if_neg hne, smul_zero]
      exact Submodule.zero_mem _
    · rcases Nat.lt_or_ge t (e + q) with hte | hte
      · have hZN : P.mode (t : ℤ) g Y ∈ P.normalSpan S :=
          hcl e q (by omega) g (P.subset_normalSpan S hgS) hge Y hY hYq t
        have hZg : P.mode (t : ℤ) g Y ∈ P.grade (e + q - t - 1) :=
          P.mode_mem_grade' _ hge hYq (by omega)
        have key := IH f (by omega) hf1 (by omega) v hv hvf (e + q - t - 1) (1 + s + r + t)
          (by omega) _ hZN hZg
        have e2 : (-1 - (s : ℤ) + (-1 - (r : ℤ)) - (t : ℤ)) =
            -1 - ((1 + s + r + t : ℕ) : ℤ) := by push_cast; ring
        rw [e2]
        exact key
      · rw [P.mode_trunc (t : ℤ) hge hYq (by omega), map_zero]
        exact Submodule.zero_mem _

/-- The first half of the right-normed spanning induction: normal words of weight `D ≥ 1` are
right-normed, given the second half at target weight `D`. -/
theorem rnf_word (hS0 : ∀ s ∈ S, s ∈ P.grade 0 → s = 0) {D : ℕ} (hD1 : 1 ≤ D)
    (hii : ∀ p, 1 ≤ p → p < D → ∀ u ∈ P.normalSpan S, u ∈ P.grade p → ∀ q r : ℕ,
      p + q + r = D → ∀ Y ∈ P.normalSpan S, Y ∈ P.grade q →
        P.mode (-1 - (r : ℤ)) u Y ∈ Submodule.span k (RNF P S D)) :
    ∀ {d : ℕ} {X : W}, P.IsNormalWord S d X → d = D → X ∈ Submodule.span k (RNF P S D) := by
  intro d X h
  induction h with
  | vac =>
    intro h0
    omega
  | @gen d s hs hsd =>
    intro hdD
    refine Submodule.subset_span ⟨s, P.vac, d, 0, 0, hs, hsd, by omega,
      P.vac_mem_normalSpan S, P.vac_mem_grade_zero, by omega, ?_⟩
    rw [Nat.cast_zero, sub_zero, P.mode_vac_neg_one]
  | @deriv d x hx _ =>
    intro hdD
    rcases Nat.eq_zero_or_pos d with hd0 | hd
    · rw [hd0] at hx
      obtain ⟨c, rfl⟩ := P.normalWord_weight_zero hS0 hx rfl
      have hT0 : P.T P.vac = 0 := by
        rw [P.T_eq, P.vac_mode]
        simp
      rw [map_smul, hT0, smul_zero]
      exact Submodule.zero_mem _
    · have key := hii d hd (by omega) x (P.normalWord_mem_normalSpan hx)
        (P.normalWord_mem_grade hx) 0 1 (by omega) P.vac (P.vac_mem_normalSpan S)
        P.vac_mem_grade_zero
      have e : (-1 - ((1 : ℕ) : ℤ)) = -2 := by norm_num
      rw [e] at key
      rw [P.T_eq]
      exact key
  | @prod i j x y hx hy ihx ihy =>
    intro hdD
    rcases Nat.eq_zero_or_pos i with hi0 | hi
    · rw [hi0] at hx
      obtain ⟨c, rfl⟩ := P.normalWord_weight_zero hS0 hx rfl
      rw [P.mode_neg_one_smul_vac_left]
      exact Submodule.smul_mem _ c (ihy (by omega))
    rcases Nat.eq_zero_or_pos j with hj0 | hj
    · rw [hj0] at hy
      obtain ⟨c, rfl⟩ := P.normalWord_weight_zero hS0 hy rfl
      rw [P.mode_neg_one_smul_vac_right]
      exact Submodule.smul_mem _ c (ihx (by omega))
    · have key := hii i hi (by omega) x (P.normalWord_mem_normalSpan hx)
        (P.normalWord_mem_grade hx) j 0 (by omega) y (P.normalWord_mem_normalSpan hy)
        (P.normalWord_mem_grade hy)
      rw [Nat.cast_zero, sub_zero] at key
      exact key

/-- **Right-normed spanning.**  If all pairs of normal elements of total weight `< w` close,
then for `1 ≤ D ≤ w` every element of `𝒩(S) ∩ P_D` is a linear combination of right-normed
monomials `g_(-1-s) u` (`RNF P S D`). -/
theorem rnf [CharZero k] (hS : ∀ s ∈ S, ∃ d, s ∈ P.grade d)
    (hS0 : ∀ s ∈ S, s ∈ P.grade 0 → s = 0) {w : ℕ}
    (hcl : ∀ i j, i + j < w → Cl P (P.normalSpan S) i j) :
    ∀ D, 1 ≤ D → D ≤ w → ∀ y ∈ P.normalSpan S, y ∈ P.grade D →
      y ∈ Submodule.span k (RNF P S D) := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D IH =>
  intro hD1 hDw y hy hyD
  have hii := rnf_prod P hS hS0 hcl hDw fun p hp1 hpD => IH p hpD hp1 (by omega)
  have hle : Submodule.span k {x | P.IsNormalWord S D x} ≤ Submodule.span k (RNF P S D) :=
    Submodule.span_le.2 fun X hX => rnf_word P hS0 hD1 hii hX rfl
  exact hle (P.mem_wordSpan_of_mem hS hy hyD)

/-- If no generator has weight one, `𝒩(S) ∩ P_1 = 0`. -/
theorem eq_zero_of_wt_one [CharZero k] (hS : ∀ s ∈ S, ∃ d, s ∈ P.grade d)
    (hS0 : ∀ s ∈ S, s ∈ P.grade 0 → s = 0) (hS1 : ∀ s ∈ S, s ∈ P.grade 1 → s = 0) {y : W}
    (hy : y ∈ P.normalSpan S) (hy1 : y ∈ P.grade 1) : y = 0 := by
  have hcl : ∀ i j, i + j < 1 → Cl P (P.normalSpan S) i j := by
    intro i j hij x _ _
    have hj : j = 0 := by omega
    rw [hj]
    exact Rx_wt_zero P hS hS0 x
  have hR := rnf P hS hS0 hcl 1 le_rfl le_rfl y hy hy1
  have hle : Submodule.span k (RNF P S 1) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨g, v, e, s, f, hgS, hge, he, hv, hvf, hesf, rfl⟩
    have he1 : e = 1 := by omega
    rw [he1] at hge
    rw [hS1 g hgS hge, map_zero, LinearMap.zero_apply]
    exact Submodule.zero_mem _
  simpa using hle hR

/-- Everything closes against weight one when no generator has weight one. -/
theorem Rx_wt_one [CharZero k] (hS : ∀ s ∈ S, ∃ d, s ∈ P.grade d)
    (hS0 : ∀ s ∈ S, s ∈ P.grade 0 → s = 0) (hS1 : ∀ s ∈ S, s ∈ P.grade 1 → s = 0) (x : W) :
    Rx P (P.normalSpan S) x 1 := by
  intro y hy hy1 m
  rw [eq_zero_of_wt_one P hS hS0 hS1 hy hy1, map_zero]
  exact Submodule.zero_mem _

/-! ### The probe lemma -/

/-- **Filtered Wick step for one probe vector `x`** (mode form of the noncommutative Wick
identity, line 2781).  Given right-normed spanning at weight `D`, `x` closes against weight `D`
if (a) it closes against all lower weights, (b) its products `x_(t) g` with the generators
`g ∈ S` of weight `eg ≤ D` lie in `𝒩`, and (c) these products close against every weight
`f ≤ D - eg`. -/
theorem probe [CharZero k] {x : W} {e D : ℕ} (hx : x ∈ P.grade e)
    (hRNF : ∀ y ∈ P.normalSpan S, y ∈ P.grade D → y ∈ Submodule.span k (RNF P S D))
    (ha : ∀ f < D, Rx P (P.normalSpan S) x f)
    (hb : ∀ g ∈ S, ∀ eg, g ∈ P.grade eg → 0 < eg → eg ≤ D → ∀ t : ℕ,
      P.mode t x g ∈ P.normalSpan S)
    (hc : ∀ g ∈ S, ∀ eg f, g ∈ P.grade eg → 0 < eg → eg + f ≤ D → ∀ t : ℕ,
      Rx P (P.normalSpan S) (P.mode t x g) f) :
    Rx P (P.normalSpan S) x D := by
  have hT : ∀ x ∈ P.normalSpan S, P.T x ∈ P.normalSpan S := fun _ h => P.T_mem_normalSpan h
  have hprod : ∀ x ∈ P.normalSpan S, ∀ y ∈ P.normalSpan S,
      P.mode (-1) x y ∈ P.normalSpan S :=
    fun _ hx _ hy => P.prod_mem_normalSpan hx hy
  intro y hy hyD m
  refine linear_mem_of_mem_span (P.mode m x) ?_ (hRNF y hy hyD)
  rintro _ ⟨g, u, eg, s, f, hgS, hge, heg, hu, huf, hesf, rfl⟩
  have hcomm := P.commutator hx hge (m : ℤ) (-1 - (s : ℤ)) u
  rw [sub_eq_iff_eq_add] at hcomm
  rw [hcomm]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_) ?_
  · refine mode_mem_int P _ hT hprod (hb g hgS eg hge heg (by omega) t) hu _ fun m' _ => ?_
    exact hc g hgS eg f hge heg (by omega) t u hu huf m'
  · exact P.neg_mode_mem hT hprod s g (P.subset_normalSpan S hgS) _ (ha f (by omega) u hu huf m)

/-- `probe` with the inputs sorted by total weight: below the top total weight `e + D - 1`
closure is assumed in general (`hcl`); at the top, the probe needs `x` against weight `D - 1`
(`hlow`) and the products `x_(0) g` against weight `D - wt g` (`htop`). -/
theorem Rx_of_top [CharZero k] {x : W} {e D : ℕ} (hD : 1 ≤ D) (hxN : x ∈ P.normalSpan S)
    (hx : x ∈ P.grade e)
    (hRNF : ∀ y ∈ P.normalSpan S, y ∈ P.grade D → y ∈ Submodule.span k (RNF P S D))
    (hcl : ∀ q f, q + f + 1 < e + D → Cl P (P.normalSpan S) q f)
    (hlow : Rx P (P.normalSpan S) x (D - 1))
    (hrow : ∀ g ∈ S, ∀ eg, g ∈ P.grade eg → 0 < eg → eg ≤ D → ∀ t : ℕ,
      P.mode t x g ∈ P.normalSpan S)
    (htop : ∀ g ∈ S, ∀ eg, g ∈ P.grade eg → 0 < eg → eg ≤ D →
      Rx P (P.normalSpan S) (P.mode ((0 : ℕ) : ℤ) x g) (D - eg)) :
    Rx P (P.normalSpan S) x D := by
  refine probe P hx hRNF (fun f hf => ?_) hrow fun g hg eg f hge heg hle t => ?_
  · rcases Nat.lt_or_ge (f + 1) D with h | h
    · exact hcl e f (by omega) x hxN hx
    · have hf' : f = D - 1 := by omega
      rw [hf']
      exact hlow
  · by_cases htf : t = 0 ∧ f = D - eg
    · obtain ⟨ht, hf⟩ := htf
      rw [ht, hf]
      exact htop g hg eg hge heg (by omega)
    · exact Rx_mode_of_Cl P _ hx hge t (hrow g hg eg hge heg (by omega) t) fun _ =>
        hcl _ _ (by omega)

/-- `probe` for a vector whose products with the generators are known, when closure holds
in general below the total weight `e + D`. -/
theorem Rx_of_gen [CharZero k] {x : W} {e D : ℕ} (hD : 1 ≤ D) (hxN : x ∈ P.normalSpan S)
    (hx : x ∈ P.grade e)
    (hRNF : ∀ y ∈ P.normalSpan S, y ∈ P.grade D → y ∈ Submodule.span k (RNF P S D))
    (hrow : ∀ g ∈ S, ∀ eg, g ∈ P.grade eg → 0 < eg → eg ≤ D → ∀ t : ℕ,
      P.mode t x g ∈ P.normalSpan S)
    (hcl : ∀ q f, q + f < e + D → Cl P (P.normalSpan S) q f) :
    Rx P (P.normalSpan S) x D :=
  Rx_of_top P hD hxN hx hRNF (fun q f h => hcl q f (by omega))
    (hcl e (D - 1) (by omega) x hxN hx) hrow fun g hg eg hge heg hle =>
      Rx_mode_of_Cl P _ hx hge 0 (hrow g hg eg hge heg hle 0) fun _ => hcl _ _ (by omega)

/-- **Closure of `(p, D)` from the generators of weight `≤ D`.**  If every generator `g` of
weight `≤ D` closes against weight `p`, and closure holds in general below the total weight
`p + D`, then every element of `𝒩 ∩ P_p` closes against weight `D` (skew symmetry gives the
products `u_(t) g`, and `probe` does the rest). -/
theorem Cl_of_gens [CharZero k] {p D : ℕ} (hD : 1 ≤ D)
    (hRNF : ∀ y ∈ P.normalSpan S, y ∈ P.grade D → y ∈ Submodule.span k (RNF P S D))
    (hgen : ∀ g ∈ S, ∀ eg, g ∈ P.grade eg → 0 < eg → eg ≤ D → Rx P (P.normalSpan S) g p)
    (hcl : ∀ q f, q + f < p + D → Cl P (P.normalSpan S) q f) :
    Cl P (P.normalSpan S) p D := by
  intro u hu hup
  refine Rx_of_gen P hD hu hup hRNF ?_ hcl
  intro g hg eg hge heg hle t
  exact PF13.rev_mem P (fun _ h => P.T_mem_normalSpan h) hge hup t fun n _ =>
    hgen g hg eg hge heg hle u hu hup n

end RNF

end PF13Wick

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.PF13Wick.rnf
#print axioms HaagerupIzumi.C8.PF13Wick.probe
#print axioms HaagerupIzumi.C8.PF13Wick.Rx_of_top
#print axioms HaagerupIzumi.C8.PF13Wick.Rx_of_gen
#print axioms HaagerupIzumi.C8.PF13Wick.Cl_of_gens
#print axioms HaagerupIzumi.C8.PF13Wick.Rx_wt_one
