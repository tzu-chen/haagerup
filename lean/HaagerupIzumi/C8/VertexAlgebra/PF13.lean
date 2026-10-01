module

public import HaagerupIzumi.C8.VertexAlgebra.Diagonal
public import HaagerupIzumi.C8.VertexAlgebra.Borcherds
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# PF13: recovery of the generator rows (first half of `prop:pf13-finite-reconstruction`)

Manuscript lines 2732–2813 of `c8_expanded_20260929/haagerup_c8_expanded.tex`.  The setting is
a weak vertex algebra `P` (all interface fields except the CFT-type axiom; the intended instance
is the product `Diagonal.prodWeak A A'` of the two algebras `V`, `V'`) and a subspace `N`
containing the vacuum and closed under translation and `(-1)`-products (the intended instance is
the diagonal normal span `D`).  The generators are `L` (weight 2), `a` (weight 3),
`b = a_(1) a` (weight 4), `d = a_(1) b` (weight 5).

Proved here, from the stated hypotheses:

* `rev_mem` (skew symmetry): if `x_(m) y ∈ N` for all `m ≥ n`, then `y_(n) x ∈ N`;
* `iterate_one_mem` (equation `eq:pf13-b-iterate`, the iterate formula with `m = 1`):
  `(x_(1) y)_(n) s = x_1 (y_n s) - x_0 (y_{n+1} s) + y_{n+1} (x_0 s) - y_n (x_1 s)`;
* `vir_a1`: `L_(n) (a_(1) X) = a_(1) (L_(n) X) + (2n - 1) a_(n) X` (commutator formula, `a`
  primary of weight 3), whence `Lb_eq`: `L(m) b = (2m+1) a_{m+1} a` for `m ≥ 1` (line 2753);
* the Virasoro rows `row_LL`, `row_La`, `row_Lb`, `row_Ld` (lines 2752–2756);
* `all_pairs`: every ordered pair of generators has all singular products in `N`.

**Conditional on unformalized manuscript claims.**  `all_pairs` takes four families of
memberships as hypotheses, `claimA6`, `claimA7`, `claimA8`, `claimB7`:
`a_(m) (a_(j) b)`, `a_(m) (a_(j) d)`, `a_(m) (b_(j) d)`, `b_(m) (a_(j) d) ∈ N`.
These are **not certificate inputs**: they are instances of the manuscript's own intermediate
claims `A_6`, `A_7`, `A_8`, `B_7` (lines 2777–2811: "`a_n P` [resp. `b_n P`] lies in the normal
span for every normal polynomial `P` of weight at most `r`"), namely the instances consumed by
the iterate identities for `b_n b`, `b_n d`, `d_n d`.  The manuscript proves them by a
core-by-core filtered Wick verification through weight eight (using the self-row
`a_0 a = ½Tb − (1/12)T³L`, `a_n b = 0` for `n ≥ 4`, `a_3 b ∈ k·a`, `a_2 b ∈ k·Ta`); that
verification is **not yet formalized**.  So `all_pairs`, and everything built on it, is the
recovery *conditional on* `A_6, A_7, A_8, B_7`.  Everything else in the recovery (Virasoro
rows, skew reversal, iterate reductions) is proved.
-/

namespace HaagerupIzumi.C8

namespace PF13

open scoped BigOperators

variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]
variable (P : WeakVertexAlgebra k W)

theorem zbinom_one_of_two_le {t : ℕ} (ht : 2 ≤ t) : zbinom k 1 t = 0 := by
  have h := zbinom_natCast_of_lt k (n := 1) (t := t) (by omega)
  rwa [Nat.cast_one] at h

/-- **Skew symmetry.** If `x_(m) y ∈ N` for every `m ≥ n`, then `y_(n) x ∈ N`. -/
theorem rev_mem {N : Submodule k W} (hT : ∀ x ∈ N, P.T x ∈ N) {i j : ℕ} {x y : W}
    (hx : x ∈ P.grade i) (hy : y ∈ P.grade j) (n : ℕ)
    (h : ∀ m : ℕ, n ≤ m → P.mode m x y ∈ N) : P.mode n y x ∈ N := by
  rw [P.skew hx hy (n : ℤ)]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (P.T_pow_mem hT t ?_)
  have e : (n : ℤ) + t = ((n + t : ℕ) : ℤ) := by push_cast; ring
  rw [e]
  exact h (n + t) (by omega)

/-- **Equation `eq:pf13-b-iterate`** (iterate formula with `m = 1`), in membership form:
`(x_(1) y)_(n) s = x_1 (y_n s) - x_0 (y_{n+1} s) + y_{n+1} (x_0 s) - y_n (x_1 s)`. -/
theorem iterate_one_mem {N : Submodule k W} {i j l : ℕ} {x y s : W} (hx : x ∈ P.grade i)
    (hy : y ∈ P.grade j) (hs : s ∈ P.grade l)
    (hA : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m x (P.mode j y s) ∈ N)
    (hB : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m y (P.mode j x s) ∈ N) (n : ℕ) :
    P.mode n (P.mode 1 x y) s ∈ N := by
  rw [P.iterate hx hy hs 1 n]
  refine Submodule.sum_mem _ fun t _ => ?_
  rcases Nat.lt_or_ge t 2 with ht | ht
  · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hA _ _ (by omega) (by omega))
      (Submodule.smul_mem _ _ (hB _ _ (by omega) (by omega))))
  · rw [zbinom_one_of_two_le ht, mul_zero, zero_smul]
    exact Submodule.zero_mem _

variable {N : Submodule k W} {L a b d : W} {c : k}
variable (hT : ∀ x ∈ N, P.T x ∈ N) (hvacN : P.vac ∈ N)
variable (hLN : L ∈ N) (haN : a ∈ N) (hbN : b ∈ N) (hdN : d ∈ N)
variable (hLg : L ∈ P.grade 2) (hag : a ∈ P.grade 3) (hbg : b ∈ P.grade 4) (hdg : d ∈ P.grade 5)
variable (hb : b = P.mode 1 a a) (hd : d = P.mode 1 a b)
variable (hLm1 : ∀ x, P.mode 0 L x = P.T x)
variable (hL0 : ∀ {n : ℕ} {x : W}, x ∈ P.grade n → P.mode 1 L x = (n : k) • x)
variable (hLL2 : P.mode 2 L L = 0) (hLL3 : P.mode 3 L L = (c / 2) • P.vac)
variable (hLa : ∀ m : ℤ, 2 ≤ m → P.mode m L a = 0)
variable (haa2 : P.mode 2 a a = P.T L) (haa3 : P.mode 3 a a = (2 : k) • L)
variable (haa4 : P.mode 4 a a = 0) (haa5 : P.mode 5 a a = (c / 3) • P.vac)
variable (raa : ∀ n : ℕ, P.mode n a a ∈ N) (rab : ∀ n : ℕ, P.mode n a b ∈ N)
variable (rad : ∀ n : ℕ, P.mode n a d ∈ N)
variable (claimA6 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m a (P.mode j a b) ∈ N)
variable (claimA7 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m a (P.mode j a d) ∈ N)
variable (claimA8 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m a (P.mode j b d) ∈ N)
variable (claimB7 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m b (P.mode j a d) ∈ N)

include hLg hag hLm1 hL0 hLa in
/-- `L_(n) (a_(1) X) = a_(1) (L_(n) X) + (2n - 1) a_(n) X` for `a` primary of weight 3
(commutator formula; `L(m) = L_(m+1)`). -/
theorem vir_a1 (n : ℕ) (X : W) :
    P.mode n L (P.mode 1 a X) =
      P.mode 1 a (P.mode n L X) + (2 * (n : k) - 1) • P.mode n a X := by
  have hcomm := P.commutator hLg hag (n : ℤ) 1 X
  have hsum : ∑ t ∈ Finset.range (2 + 3),
      zbinom k (n : ℤ) t • P.mode ((n : ℤ) + 1 - t) (P.mode t L a) X =
      zbinom k (n : ℤ) 0 • P.mode ((n : ℤ) + 1 - ((0 : ℕ) : ℤ)) (P.mode ((0 : ℕ) : ℤ) L a) X +
      zbinom k (n : ℤ) 1 • P.mode ((n : ℤ) + 1 - ((1 : ℕ) : ℤ)) (P.mode ((1 : ℕ) : ℤ) L a) X :=
    sum_range_eq_two_terms (by norm_num) fun t ht => by
      rw [hLa t (by exact_mod_cast ht), map_zero, LinearMap.zero_apply, smul_zero]
  have h3 : P.mode 1 L a = (3 : k) • a := by
    have := hL0 hag
    simpa using this
  rw [sub_eq_iff_eq_add', hsum] at hcomm
  rw [hcomm]
  congr 1
  simp only [Nat.cast_zero, Nat.cast_one, sub_zero, add_sub_cancel_right, zbinom_zero_right,
    zbinom_one_right, one_smul, hLm1, h3, P.mode_T, map_smul, LinearMap.smul_apply,
    Int.cast_natCast, Int.cast_add, Int.cast_one]
  module

include hb hLg hag hLm1 hL0 hLa in
/-- `L(m) b = (2m+1) a_{m+1} a` for `m ≥ 1` (line 2753), i.e. `L_(n) b = (2n-1) a_(n) a`
for `n ≥ 2`. -/
theorem Lb_eq (n : ℕ) (hn : 2 ≤ n) :
    P.mode n L b = (2 * (n : k) - 1) • P.mode n a a := by
  rw [hb, vir_a1 P hLg hag hLm1 hL0 hLa, hLa n (by exact_mod_cast hn), map_zero, zero_add]

include hT hvacN hLN hLg hLm1 hL0 hLL2 hLL3 in
/-- The Virasoro row `L_(n) L`. -/
theorem row_LL (n : ℕ) : P.mode n L L ∈ N := by
  rcases Nat.lt_or_ge n 4 with hn | hn
  · obtain rfl | rfl | rfl | rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
    · rw [Nat.cast_zero, hLm1]
      exact hT _ hLN
    · rw [Nat.cast_one, hL0 hLg]
      exact Submodule.smul_mem _ _ hLN
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, hLL2]
      exact Submodule.zero_mem _
    · rw [show ((3 : ℕ) : ℤ) = 3 from rfl, hLL3]
      exact Submodule.smul_mem _ _ hvacN
  · rw [P.mode_trunc (n : ℤ) hLg hLg (by omega)]
    exact Submodule.zero_mem _

include hT haN hag hLm1 hL0 hLa in
/-- The Virasoro row `L_(n) a` (`a` primary of weight 3). -/
theorem row_La (n : ℕ) : P.mode n L a ∈ N := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · rw [Nat.cast_zero, hLm1]
      exact hT _ haN
    · rw [Nat.cast_one, hL0 hag]
      exact Submodule.smul_mem _ _ haN
  · rw [hLa n (by exact_mod_cast hn)]
    exact Submodule.zero_mem _

include hT hbN hLg hag hbg hb hLm1 hL0 hLa raa in
/-- The Virasoro row `L_(n) b`. -/
theorem row_Lb (n : ℕ) : P.mode n L b ∈ N := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · rw [Nat.cast_zero, hLm1]
      exact hT _ hbN
    · rw [Nat.cast_one, hL0 hbg]
      exact Submodule.smul_mem _ _ hbN
  · rw [Lb_eq P hLg hag hb hLm1 hL0 hLa n hn]
    exact Submodule.smul_mem _ _ (raa n)

include hT haN hLg hag hLm1 hL0 hLa in
/-- The reversed row `a_(n) L` (skew symmetry). -/
theorem row_aL (n : ℕ) : P.mode n a L ∈ N :=
  rev_mem P hT hLg hag n fun m _ => row_La P hT haN hag hLm1 hL0 hLa m

include hT haN hLg hag hLm1 hL0 hLa haa2 haa3 haa4 haa5 in
/-- `a_(1) (a_(n) a) ∈ N` for `n ≥ 2`, from the self-row. -/
theorem a1_aa_mem (n : ℕ) (hn : 2 ≤ n) : P.mode 1 a (P.mode n a a) ∈ N := by
  have aL := row_aL P hT haN hLg hag hLm1 hL0 hLa
  rcases Nat.lt_or_ge n 6 with h6 | h6
  · obtain rfl | rfl | rfl | rfl : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, haa2]
      have e : P.mode 1 a (P.T L) = P.T (P.mode 1 a L) - P.mode 1 (P.T a) L := by
        rw [P.T_mode]
        abel
      rw [e, P.mode_T]
      have h1 : P.T (P.mode 1 a L) ∈ N := by simpa using hT _ (aL 1)
      have h0 : P.mode (1 - 1) a L ∈ N := by simpa using aL 0
      exact Submodule.sub_mem _ h1 (Submodule.neg_mem _ (Submodule.smul_mem _ _ h0))
    · rw [show ((3 : ℕ) : ℤ) = 3 from rfl, haa3, map_smul]
      exact Submodule.smul_mem _ _ (by simpa using aL 1)
    · rw [show ((4 : ℕ) : ℤ) = 4 from rfl, haa4, map_zero]
      exact Submodule.zero_mem _
    · rw [show ((5 : ℕ) : ℤ) = 5 from rfl, haa5, map_smul, P.mode_vac_nonneg 1 a zero_le_one,
        smul_zero]
      exact Submodule.zero_mem _
  · rw [P.mode_trunc (n : ℤ) hag hag (by omega), map_zero]
    exact Submodule.zero_mem _

include hT haN hdN hLg hag hdg hb hd hLm1 hL0 hLa haa2 haa3 haa4 haa5 rab in
/-- The Virasoro row `L_(n) d`, from `L(m) d = (2m+1) a_{m+1} b + a_1 L(m) b` (line 2754). -/
theorem row_Ld (n : ℕ) : P.mode n L d ∈ N := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · rw [Nat.cast_zero, hLm1]
      exact hT _ hdN
    · rw [Nat.cast_one, hL0 hdg]
      exact Submodule.smul_mem _ _ hdN
  · rw [hd, vir_a1 P hLg hag hLm1 hL0 hLa, Lb_eq P hLg hag hb hLm1 hL0 hLa n hn, map_smul]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _
        (a1_aa_mem P hT haN hLg hag hLm1 hL0 hLa haa2 haa3 haa4 haa5 n hn))
      (Submodule.smul_mem _ _ (rab n))

include hT hvacN hLN haN hbN hdN hLg hag hbg hdg hb hd hLm1 hL0 hLL2 hLL3 hLa haa2 haa3 haa4
  haa5 raa rab rad claimA6 claimA7 claimA8 claimB7 in
/-- **All generator rows, conditional on the manuscript claims `A_6, A_7, A_8, B_7`.**  Every
ordered pair of generators `x, y ∈ {L, a, b, d}` has all singular products `x_(n) y` (`n ≥ 0`)
in `N`, given the Virasoro and self-row hypotheses, the input rows `a_(n) a`, `a_(n) b`,
`a_(n) d ∈ N`, and the hypotheses `claimA6`, `claimA7`, `claimA8`, `claimB7`, which are instances
of the manuscript's intermediate claims `A_6`, `A_7`, `A_8`, `B_7` (not certificate inputs, not yet
formalized). -/
theorem all_pairs : ∀ x ∈ ({L, a, b, d} : Set W), ∀ y ∈ ({L, a, b, d} : Set W), ∀ n : ℕ,
    P.mode n x y ∈ N := by
  have LL := row_LL P hT hvacN hLN hLg hLm1 hL0 hLL2 hLL3
  have La := row_La P hT haN hag hLm1 hL0 hLa
  have Lb := row_Lb P hT hbN hLg hag hbg hb hLm1 hL0 hLa raa
  have Ld := row_Ld P hT haN hdN hLg hag hdg hb hd hLm1 hL0 hLa haa2 haa3 haa4 haa5 rab
  have aL := row_aL P hT haN hLg hag hLm1 hL0 hLa
  have bL : ∀ n : ℕ, P.mode n b L ∈ N := fun n => rev_mem P hT hLg hbg n fun m _ => Lb m
  have dL : ∀ n : ℕ, P.mode n d L ∈ N := fun n => rev_mem P hT hLg hdg n fun m _ => Ld m
  have ba : ∀ n : ℕ, P.mode n b a ∈ N := fun n => rev_mem P hT hag hbg n fun m _ => rab m
  have da : ∀ n : ℕ, P.mode n d a ∈ N := fun n => rev_mem P hT hag hdg n fun m _ => rad m
  have bb : ∀ n : ℕ, P.mode n b b ∈ N := by
    intro n
    have key := iterate_one_mem P hag hag hbg claimA6 claimA6 n
    rwa [← hb] at key
  have bd : ∀ n : ℕ, P.mode n b d ∈ N := by
    intro n
    have key := iterate_one_mem P hag hag hdg claimA7 claimA7 n
    rwa [← hb] at key
  have db : ∀ n : ℕ, P.mode n d b ∈ N := fun n => rev_mem P hT hbg hdg n fun m _ => bd m
  have dd : ∀ n : ℕ, P.mode n d d ∈ N := by
    intro n
    have key := iterate_one_mem P hag hbg hdg claimA8 claimB7 n
    rwa [← hd] at key
  intro x hx y hy n
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy]
  · exact LL n
  · exact La n
  · exact Lb n
  · exact Ld n
  · exact aL n
  · exact raa n
  · exact rab n
  · exact rad n
  · exact bL n
  · exact ba n
  · exact bb n
  · exact bd n
  · exact dL n
  · exact da n
  · exact db n
  · exact dd n

end PF13

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.PF13.all_pairs
#print axioms HaagerupIzumi.C8.PF13.vir_a1
#print axioms HaagerupIzumi.C8.PF13.row_Ld
