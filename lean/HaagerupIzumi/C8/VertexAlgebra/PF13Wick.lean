module

public import HaagerupIzumi.C8.VertexAlgebra.PF13WickBasic
public import HaagerupIzumi.C8.VertexAlgebra.PF13Product

@[expose] public section

/-!
# PF13: the Wick claims `A_6, A_7, A_8, B_7` and the unconditional reconstruction

This file proves the intermediate claims of the proof of Proposition
`prop:pf13-finite-reconstruction` (manuscript lines 2777–2811 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) that `PF13.all_pairs` and
`PF13.pf13_reconstruction` took as hypotheses, and removes them from the reconstruction.

Setting (`Data`): a weak vertex algebra `P` (intended instance `V × V'`), a generating set
`S = {L, a, b, d}` (weights `2, 3, 4, 5`, `b = a_(1) a`, `d = a_(1) b`), the differential normal
span `𝒩 = P.normalSpan S`, and the hypotheses of the proposition: `L(-1) = T`, `L(0) =` weight,
`L_2 L = 0`, `L_3 L = (c/2)·1`, `a` primary, the self-row
`a_0 a = ½Tb − (1/12)T³L`, `a_2 a = TL`, `a_3 a = 2L`, `a_4 a = 0`, `a_5 a = (c/3)·1`, and the
rows `a_(n) b, a_(n) d ∈ 𝒩` (the checked parafermion records).

Write `Rx x f` for "`x_(m) y ∈ 𝒩` for every `y ∈ 𝒩` of weight exactly `f`" and `Cl p f` for
closure of all pairs of weights `(p, f)`.  The manuscript's `A_r` (weight **at most** `r`) is
`Rx a f` for all `f ≤ r` (e.g. `RxA_lt7` is `A_6`, `RxA_lt8` is `A_7`, `RxA_lt9` is `A_8`), and
`B_r` is the same for `b` (`RxB_lt8` is `B_7`); the theorems `RxA6`, `RxA7`, `RxA8`, `RxB6`,
`RxB7` are the top-weight pieces.  The proof follows the manuscript's acyclic order, made
precise as follows.

* Stage 0 (all generator pairs of total weight `≤ 7` are known): `Cl` below total weight 8
  (`cl7`, filtered Wick), right-normed spanning through weight 8 (`rnf8`), `L` against
  weight 6, `a` against weight 5, `Cl 6 2`, and **`A_6`** (`RxA6`).
* `b_(n) b` from the iterate identity `eq:pf13-b-iterate` (`rbb`).  Then `Cl` below 9.
* `L` against weight 7, `Cl 6 3`, `Cl 7 2`, **`A_7`** (`RxA7`), then `b_(n) d` (`rbd`) and
  `d_(n) b`.  Then `Cl` below 10.
* **`B_6`** (`RxB6`), `L` against weight 8, `Cl 6 4`, `Cl 7 3`, `Cl 8 2`, **`A_8`** (`RxA8`),
  **`B_7`** (`RxB7`).
* The instances consumed by the iterate identities: `claimA6`, `claimA7`, `claimA8`, `claimB7`.

Each `A_r`/`B_r` step is `probe` applied to right-normed monomials `g_(-1-s) u`; the only
products at the top total weight are `x_(0) g` against weight `r - wt g`, supplied by the
explicit Virasoro/self-row formulas (`Rx_aL`, `Rx_aa`, `Rx_bL`), by the previously
established `Cl 6 r'`, `Cl 7 r'`, `Cl 8 2`, or, for `a_(0) d` against weight one at `A_6`, by
the vanishing of `𝒩 ∩ P_1` (`Rx1`).

Main results:
* `Data.claims`: the four families of hypotheses of `PF13.all_pairs`;
* `Data.all_pairs`: every ordered pair of generators has all singular products in `𝒩`;
* `pf13_reconstruction'`: `PF13.pf13_reconstruction` **without** the hypotheses
  `claimA6_a0b`, `claimA7`, `claimA8`, `claimB7`;
* `pf13_reconstruction_of_rows`: the same without the hypotheses
  `a_n b = 0 (n ≥ 4)`, `a_3 b ∈ k·a`, `a_2 b ∈ k·Ta`, which turn out to be unnecessary.

No hypothesis is external or a certificate input beyond those of the proposition itself.
-/

namespace HaagerupIzumi.C8

namespace PF13Wick

open scoped BigOperators

variable {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

/-- The hypotheses of `prop:pf13-finite-reconstruction` inside a weak vertex algebra `P`, for
the normal span of `S = {L, a, b, d}`. -/
structure Data (P : WeakVertexAlgebra k W) (S : Set W) (L a b d : W) (c : k) : Prop where
  hS4 : ∀ s ∈ S, s = L ∨ s = a ∨ s = b ∨ s = d
  L_mem : L ∈ S
  a_mem : a ∈ S
  b_mem : b ∈ S
  d_mem : d ∈ S
  hLg : L ∈ P.grade 2
  hag : a ∈ P.grade 3
  hbg : b ∈ P.grade 4
  hdg : d ∈ P.grade 5
  hb : b = P.mode 1 a a
  hd : d = P.mode 1 a b
  hLm1 : ∀ x, P.mode 0 L x = P.T x
  hL0 : ∀ {n : ℕ} {x : W}, x ∈ P.grade n → P.mode 1 L x = (n : k) • x
  hLL2 : P.mode 2 L L = 0
  hLL3 : P.mode 3 L L = (c / 2) • P.vac
  hLa : ∀ m : ℤ, 2 ≤ m → P.mode m L a = 0
  haa0 : P.mode 0 a a = (1 / 2 : k) • P.T b - (1 / 12 : k) • (P.T ^ 3) L
  haa2 : P.mode 2 a a = P.T L
  haa3 : P.mode 3 a a = (2 : k) • L
  haa4 : P.mode 4 a a = 0
  haa5 : P.mode 5 a a = (c / 3) • P.vac
  rab : ∀ n : ℕ, P.mode n a b ∈ P.normalSpan S
  rad : ∀ n : ℕ, P.mode n a d ∈ P.normalSpan S

namespace Data

variable {P : WeakVertexAlgebra k W} {S : Set W} {L a b d : W} {c : k}

section Basic

variable (H : Data P S L a b d c)
include H

theorem gen_cases {s : W} {i : ℕ} (hs : s ∈ S) (hsi : s ∈ P.grade i) :
    (s = L ∧ i = 2) ∨ (s = a ∧ i = 3) ∨ (s = b ∧ i = 4) ∨ (s = d ∧ i = 5) ∨ s = 0 := by
  rcases H.hS4 s hs with h | h | h | h
  · by_cases hi : i = 2
    · exact Or.inl ⟨h, hi⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (P.eq_zero_of_mem_grade_of_ne hsi (by rw [h]; exact H.hLg) hi))))
  · by_cases hi : i = 3
    · exact Or.inr (Or.inl ⟨h, hi⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (P.eq_zero_of_mem_grade_of_ne hsi (by rw [h]; exact H.hag) hi))))
  · by_cases hi : i = 4
    · exact Or.inr (Or.inr (Or.inl ⟨h, hi⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (P.eq_zero_of_mem_grade_of_ne hsi (by rw [h]; exact H.hbg) hi))))
  · by_cases hi : i = 5
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, hi⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        (P.eq_zero_of_mem_grade_of_ne hsi (by rw [h]; exact H.hdg) hi))))

theorem homog : ∀ s ∈ S, ∃ e, s ∈ P.grade e := by
  intro s hs
  rcases H.hS4 s hs with h | h | h | h <;> rw [h]
  exacts [⟨2, H.hLg⟩, ⟨3, H.hag⟩, ⟨4, H.hbg⟩, ⟨5, H.hdg⟩]

theorem wt_zero : ∀ s ∈ S, s ∈ P.grade 0 → s = 0 := by
  intro s hs h0
  rcases H.gen_cases hs h0 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact h

theorem wt_one : ∀ s ∈ S, s ∈ P.grade 1 → s = 0 := by
  intro s hs h1
  rcases H.gen_cases hs h1 with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | h
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact h

omit H in
theorem hTN : ∀ x ∈ P.normalSpan S, P.T x ∈ P.normalSpan S := fun _ h => P.T_mem_normalSpan h

theorem LN : L ∈ P.normalSpan S := P.subset_normalSpan S H.L_mem
theorem aN : a ∈ P.normalSpan S := P.subset_normalSpan S H.a_mem
theorem bN : b ∈ P.normalSpan S := P.subset_normalSpan S H.b_mem
theorem dN : d ∈ P.normalSpan S := P.subset_normalSpan S H.d_mem

/-! #### The known rows -/

theorem raa : ∀ n : ℕ, P.mode n a a ∈ P.normalSpan S :=
  PF13.raa_of_selfrow P hTN (P.vac_mem_normalSpan S) H.LN H.bN H.hag H.hb H.haa0 H.haa2
    H.haa3 H.haa4 H.haa5

theorem rLL : ∀ n : ℕ, P.mode n L L ∈ P.normalSpan S :=
  PF13.row_LL P hTN (P.vac_mem_normalSpan S) H.LN H.hLg H.hLm1 H.hL0 H.hLL2 H.hLL3

theorem rLa : ∀ n : ℕ, P.mode n L a ∈ P.normalSpan S :=
  PF13.row_La P hTN H.aN H.hag H.hLm1 H.hL0 H.hLa

theorem rLb : ∀ n : ℕ, P.mode n L b ∈ P.normalSpan S :=
  PF13.row_Lb P hTN H.bN H.hLg H.hag H.hbg H.hb H.hLm1 H.hL0 H.hLa H.raa

theorem rLd : ∀ n : ℕ, P.mode n L d ∈ P.normalSpan S :=
  PF13.row_Ld P hTN H.aN H.dN H.hLg H.hag H.hdg H.hb H.hd H.hLm1 H.hL0 H.hLa H.haa2 H.haa3
    H.haa4 H.haa5 H.rab

theorem raL : ∀ n : ℕ, P.mode n a L ∈ P.normalSpan S :=
  PF13.row_aL P hTN H.aN H.hLg H.hag H.hLm1 H.hL0 H.hLa

theorem rbL : ∀ n : ℕ, P.mode n b L ∈ P.normalSpan S :=
  fun n => PF13.rev_mem P hTN H.hLg H.hbg n fun m _ => H.rLb m

theorem rdL : ∀ n : ℕ, P.mode n d L ∈ P.normalSpan S :=
  fun n => PF13.rev_mem P hTN H.hLg H.hdg n fun m _ => H.rLd m

theorem rba : ∀ n : ℕ, P.mode n b a ∈ P.normalSpan S :=
  fun n => PF13.rev_mem P hTN H.hag H.hbg n fun m _ => H.rab m

theorem rda : ∀ n : ℕ, P.mode n d a ∈ P.normalSpan S :=
  fun n => PF13.rev_mem P hTN H.hag H.hdg n fun m _ => H.rad m

/-- The generator-pair hypothesis of the filtered Wick lemma below total weight `w`, from the
known rows (the rows `b b`, `b d`, `d b`, `d d` are needed only from total weight 8, 9, 9, 10
on). -/
theorem hgen {w : ℕ}
    (rbb : 8 < w → ∀ n : ℕ, P.mode n b b ∈ P.normalSpan S)
    (rbd : 9 < w → ∀ n : ℕ, P.mode n b d ∈ P.normalSpan S)
    (rdb : 9 < w → ∀ n : ℕ, P.mode n d b ∈ P.normalSpan S)
    (rdd : 10 < w → ∀ n : ℕ, P.mode n d d ∈ P.normalSpan S) :
    ∀ i j s t, s ∈ S → s ∈ P.grade i → t ∈ S → t ∈ P.grade j → i + j < w →
      ∀ n : ℕ, P.mode n s t ∈ P.normalSpan S := by
  intro i j s t hs hsi ht htj hij n
  rcases H.gen_cases hs hsi with ⟨hs', hi⟩ | ⟨hs', hi⟩ | ⟨hs', hi⟩ | ⟨hs', hi⟩ | hs' <;>
    rcases H.gen_cases ht htj with ⟨ht', hj⟩ | ⟨ht', hj⟩ | ⟨ht', hj⟩ | ⟨ht', hj⟩ | ht' <;>
    rw [hs', ht']
  all_goals first
    | exact H.rLL n | exact H.rLa n | exact H.rLb n | exact H.rLd n
    | exact H.raL n | exact H.raa n | exact H.rab n | exact H.rad n
    | exact H.rbL n | exact H.rba n | exact rbb (by omega) n | exact rbd (by omega) n
    | exact H.rdL n | exact H.rda n | exact rdb (by omega) n | exact rdd (by omega) n
    | simp

/-- Stage 0: closure below total weight 8 (filtered Wick lemma). -/
theorem cl7 : ∀ i j, i + j < 8 → Cl P (P.normalSpan S) i j := fun i j hij =>
  Cl_of_closes P H.homog (P.closes_of_lt H.homog H.wt_zero
    (H.hgen (w := 8) (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))
      (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))) i j hij)

/-! #### Bookkeeping over the four generators -/

theorem rows4 {x : W} {D : ℕ} (hL : ∀ t : ℕ, P.mode t x L ∈ P.normalSpan S)
    (ha : ∀ t : ℕ, P.mode t x a ∈ P.normalSpan S) (hb : ∀ t : ℕ, P.mode t x b ∈ P.normalSpan S)
    (hd : ∀ t : ℕ, P.mode t x d ∈ P.normalSpan S) :
    ∀ g ∈ S, ∀ eg, g ∈ P.grade eg → 0 < eg → eg ≤ D → ∀ t : ℕ,
      P.mode t x g ∈ P.normalSpan S := by
  intro g hg _ _ _ _ t
  rcases H.hS4 g hg with h | h | h | h <;> rw [h]
  exacts [hL t, ha t, hb t, hd t]

theorem gens4 {p D : ℕ} (hL : 2 ≤ D → Rx P (P.normalSpan S) L p)
    (ha : 3 ≤ D → Rx P (P.normalSpan S) a p) (hb : 4 ≤ D → Rx P (P.normalSpan S) b p)
    (hd : 5 ≤ D → Rx P (P.normalSpan S) d p) :
    ∀ g ∈ S, ∀ eg, g ∈ P.grade eg → 0 < eg → eg ≤ D → Rx P (P.normalSpan S) g p := by
  intro g hg eg hge _ hle
  rcases H.gen_cases hg hge with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h <;> rw [h]
  · exact hL (by omega)
  · exact ha (by omega)
  · exact hb (by omega)
  · exact hd (by omega)
  · exact Rx_zero_vec P _ p

theorem top4 {x : W} {D : ℕ}
    (hL : 2 ≤ D → Rx P (P.normalSpan S) (P.mode ((0 : ℕ) : ℤ) x L) (D - 2))
    (ha : 3 ≤ D → Rx P (P.normalSpan S) (P.mode ((0 : ℕ) : ℤ) x a) (D - 3))
    (hb : 4 ≤ D → Rx P (P.normalSpan S) (P.mode ((0 : ℕ) : ℤ) x b) (D - 4))
    (hd : 5 ≤ D → Rx P (P.normalSpan S) (P.mode ((0 : ℕ) : ℤ) x d) (D - 5)) :
    ∀ g ∈ S, ∀ eg, g ∈ P.grade eg → 0 < eg → eg ≤ D →
      Rx P (P.normalSpan S) (P.mode ((0 : ℕ) : ℤ) x g) (D - eg) := by
  intro g hg eg hge _ hle
  rcases H.gen_cases hg hge with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | h <;> rw [h]
  · rw [h']
    exact hL (by omega)
  · rw [h']
    exact ha (by omega)
  · rw [h']
    exact hb (by omega)
  · rw [h']
    exact hd (by omega)
  · rw [map_zero]
    exact Rx_zero_vec P _ _

/-! #### The explicit products at the top weight -/

/-- `a_(t) L` (skew symmetry of `L_(n) a ∈ {Ta, 3a, 0}`) closes wherever `a` does. -/
theorem Rx_aL {f : ℕ} (haf : Rx P (P.normalSpan S) a f) (t : ℕ) :
    Rx P (P.normalSpan S) (P.mode t a L) f := by
  have hT' : ∀ x ∈ Rsub P (P.normalSpan S) f, P.T x ∈ Rsub P (P.normalSpan S) f :=
    fun _ hx => T_mem_Rsub P _ hx
  refine (mem_Rsub P _).1 (PF13.rev_mem P hT' H.hLg H.hag t fun m _ => ?_)
  exact PF13.row_La P hT' ((mem_Rsub P _).2 haf) H.hag H.hLm1 H.hL0 H.hLa m

/-- `a_(t) a` (the self-row: vacuum and derivatives of `L`, `b`) closes wherever `b` and `L`
do. -/
theorem Rx_aa {f : ℕ} (hbf : Rx P (P.normalSpan S) b f) (hLf : Rx P (P.normalSpan S) L f)
    (t : ℕ) : Rx P (P.normalSpan S) (P.mode t a a) f :=
  (mem_Rsub P _).1 (PF13.raa_of_selfrow P (fun _ hx => T_mem_Rsub P _ hx) (vac_mem_Rsub P _ f)
    ((mem_Rsub P _).2 hLf) ((mem_Rsub P _).2 hbf) H.hag H.hb H.haa0 H.haa2 H.haa3 H.haa4
    H.haa5 t)

/-- `b_(t) L` (skew symmetry of `L_(n) b`, linear in `b`, `L`, `1` and derivatives) closes
wherever `b` and `L` do. -/
theorem Rx_bL {f : ℕ} (hbf : Rx P (P.normalSpan S) b f) (hLf : Rx P (P.normalSpan S) L f)
    (t : ℕ) : Rx P (P.normalSpan S) (P.mode t b L) f := by
  have hT' : ∀ x ∈ Rsub P (P.normalSpan S) f, P.T x ∈ Rsub P (P.normalSpan S) f :=
    fun _ hx => T_mem_Rsub P _ hx
  have raa' : ∀ n : ℕ, P.mode n a a ∈ Rsub P (P.normalSpan S) f :=
    fun n => (mem_Rsub P _).2 (H.Rx_aa hbf hLf n)
  refine (mem_Rsub P _).1 (PF13.rev_mem P hT' H.hLg H.hbg t fun m _ => ?_)
  exact PF13.row_Lb P hT' ((mem_Rsub P _).2 hbf) H.hLg H.hag H.hbg H.hb H.hLm1 H.hL0 H.hLa
    raa' m

end Basic

section Stages

variable [CharZero k] (H : Data P S L a b d c)
include H

theorem rnf8 : ∀ D, 1 ≤ D → D ≤ 8 → ∀ y ∈ P.normalSpan S, y ∈ P.grade D →
    y ∈ Submodule.span k (RNF P S D) :=
  rnf P H.homog H.wt_zero H.cl7

theorem Rx1 (x : W) : Rx P (P.normalSpan S) x 1 := Rx_wt_one P H.homog H.wt_zero H.wt_one x

/-! #### Stage 0 -/

theorem RxL6 : Rx P (P.normalSpan S) L 6 :=
  Rx_of_gen P (by norm_num) H.LN H.hLg (H.rnf8 6 (by norm_num) (by norm_num))
    (H.rows4 H.rLL H.rLa H.rLb H.rLd) fun q f h => H.cl7 q f (by omega)

theorem RxA5 : Rx P (P.normalSpan S) a 5 :=
  Rx_of_gen P (by norm_num) H.aN H.hag (H.rnf8 5 (by norm_num) (by norm_num))
    (H.rows4 H.raL H.raa H.rab H.rad) fun q f h => H.cl7 q f (by omega)

theorem Cl62 : Cl P (P.normalSpan S) 6 2 :=
  Cl_of_gens P (by norm_num) (H.rnf8 2 (by norm_num) (by norm_num))
    (H.gens4 (fun _ => H.RxL6) (fun h => absurd h (by norm_num))
      (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num)))
    fun q f h => H.cl7 q f (by omega)

/-- **Claim `A_6`, top-weight piece**: `a_(m) P ∈ 𝒩` for every normal polynomial `P` of weight
exactly six (the full claim `A_6`, weight `≤ 6`, is `RxA_lt7`). -/
theorem RxA6 : Rx P (P.normalSpan S) a 6 :=
  Rx_of_top P (by norm_num) H.aN H.hag (H.rnf8 6 (by norm_num) (by norm_num))
    (fun q f h => H.cl7 q f (by omega)) H.RxA5 (H.rows4 H.raL H.raa H.rab H.rad)
    (H.top4 (fun _ => H.Rx_aL (H.cl7 3 4 (by norm_num) a H.aN H.hag) 0)
      (fun _ => H.Rx_aa (H.cl7 4 3 (by norm_num) b H.bN H.hbg)
        (H.cl7 2 3 (by norm_num) L H.LN H.hLg) 0)
      (fun _ => Rx_mode_of_Cl P _ H.hag H.hbg 0 (H.rab 0) fun _ => H.Cl62)
      (fun _ => H.Rx1 _))

theorem RxA_lt7 : ∀ f, f < 7 → Rx P (P.normalSpan S) a f := by
  intro f hf
  rcases Nat.lt_or_ge f 5 with h | h
  · exact H.cl7 3 f (by omega) a H.aN H.hag
  · obtain rfl | rfl : f = 5 ∨ f = 6 := by omega
    exacts [H.RxA5, H.RxA6]

/-- The instances `a_(m) (a_(j) b) ∈ 𝒩` of `A_6`. -/
theorem claimA6 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m a (P.mode j a b) ∈ P.normalSpan S :=
  claim_of_Rx P _ H.hag H.hbg H.rab H.RxA_lt7

/-- The row `b_(n) b` (iterate identity `eq:pf13-b-iterate` with `s = b`). -/
theorem rbb : ∀ n : ℕ, P.mode n b b ∈ P.normalSpan S := by
  intro n
  have key := PF13.iterate_one_mem P H.hag H.hag H.hbg H.claimA6 H.claimA6 n
  rwa [← H.hb] at key

/-! #### Stage 1 -/

theorem cl8 : ∀ i j, i + j < 9 → Cl P (P.normalSpan S) i j := fun i j hij =>
  Cl_of_closes P H.homog (P.closes_of_lt H.homog H.wt_zero
    (H.hgen (w := 9) (fun _ => H.rbb) (fun h => absurd h (by norm_num))
      (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num))) i j hij)

theorem RxL7 : Rx P (P.normalSpan S) L 7 :=
  Rx_of_gen P (by norm_num) H.LN H.hLg (H.rnf8 7 (by norm_num) (by norm_num))
    (H.rows4 H.rLL H.rLa H.rLb H.rLd) fun q f h => H.cl8 q f (by omega)

theorem Cl63 : Cl P (P.normalSpan S) 6 3 :=
  Cl_of_gens P (by norm_num) (H.rnf8 3 (by norm_num) (by norm_num))
    (H.gens4 (fun _ => H.RxL6) (fun _ => H.RxA6) (fun h => absurd h (by norm_num))
      (fun h => absurd h (by norm_num)))
    fun q f h => H.cl8 q f (by omega)

theorem Cl72 : Cl P (P.normalSpan S) 7 2 :=
  Cl_of_gens P (by norm_num) (H.rnf8 2 (by norm_num) (by norm_num))
    (H.gens4 (fun _ => H.RxL7) (fun h => absurd h (by norm_num))
      (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num)))
    fun q f h => H.cl8 q f (by omega)

/-- **Claim `A_7`, top-weight piece**: `a_(m) P ∈ 𝒩` for every normal polynomial `P` of weight
exactly seven (the full claim `A_7`, weight `≤ 7`, is `RxA_lt8`). -/
theorem RxA7 : Rx P (P.normalSpan S) a 7 :=
  Rx_of_top P (by norm_num) H.aN H.hag (H.rnf8 7 (by norm_num) (by norm_num))
    (fun q f h => H.cl8 q f (by omega)) H.RxA6 (H.rows4 H.raL H.raa H.rab H.rad)
    (H.top4 (fun _ => H.Rx_aL H.RxA5 0)
      (fun _ => H.Rx_aa (H.cl8 4 4 (by norm_num) b H.bN H.hbg)
        (H.cl8 2 4 (by norm_num) L H.LN H.hLg) 0)
      (fun _ => Rx_mode_of_Cl P _ H.hag H.hbg 0 (H.rab 0) fun _ => H.Cl63)
      (fun _ => Rx_mode_of_Cl P _ H.hag H.hdg 0 (H.rad 0) fun _ => H.Cl72))

theorem RxA_lt8 : ∀ f, f < 8 → Rx P (P.normalSpan S) a f := by
  intro f hf
  rcases Nat.lt_or_ge f 7 with h | h
  · exact H.RxA_lt7 f h
  · obtain rfl : f = 7 := by omega
    exact H.RxA7

/-- The instances `a_(m) (a_(j) d) ∈ 𝒩` of `A_7`. -/
theorem claimA7 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m a (P.mode j a d) ∈ P.normalSpan S :=
  claim_of_Rx P _ H.hag H.hdg H.rad H.RxA_lt8

/-- The row `b_(n) d` (iterate identity with `s = d`). -/
theorem rbd : ∀ n : ℕ, P.mode n b d ∈ P.normalSpan S := by
  intro n
  have key := PF13.iterate_one_mem P H.hag H.hag H.hdg H.claimA7 H.claimA7 n
  rwa [← H.hb] at key

theorem rdb : ∀ n : ℕ, P.mode n d b ∈ P.normalSpan S :=
  fun n => PF13.rev_mem P hTN H.hbg H.hdg n fun m _ => H.rbd m

/-! #### Stage 2 -/

theorem cl9 : ∀ i j, i + j < 10 → Cl P (P.normalSpan S) i j := fun i j hij =>
  Cl_of_closes P H.homog (P.closes_of_lt H.homog H.wt_zero
    (H.hgen (w := 10) (fun _ => H.rbb) (fun _ => H.rbd) (fun _ => H.rdb)
      (fun h => absurd h (by norm_num))) i j hij)

/-- **Claim `B_6`, top-weight piece**: `b_(m) P ∈ 𝒩` for every normal polynomial `P` of weight
exactly six (weights `≤ 5` are generic closure, `cl9`). -/
theorem RxB6 : Rx P (P.normalSpan S) b 6 :=
  Rx_of_gen P (by norm_num) H.bN H.hbg (H.rnf8 6 (by norm_num) (by norm_num))
    (H.rows4 H.rbL H.rba H.rbb H.rbd) fun q f h => H.cl9 q f (by omega)

theorem RxL8 : Rx P (P.normalSpan S) L 8 :=
  Rx_of_gen P (by norm_num) H.LN H.hLg (H.rnf8 8 (by norm_num) (by norm_num))
    (H.rows4 H.rLL H.rLa H.rLb H.rLd) fun q f h => H.cl9 q f (by omega)

theorem Cl64 : Cl P (P.normalSpan S) 6 4 :=
  Cl_of_gens P (by norm_num) (H.rnf8 4 (by norm_num) (by norm_num))
    (H.gens4 (fun _ => H.RxL6) (fun _ => H.RxA6) (fun _ => H.RxB6)
      (fun h => absurd h (by norm_num)))
    fun q f h => H.cl9 q f (by omega)

theorem Cl73 : Cl P (P.normalSpan S) 7 3 :=
  Cl_of_gens P (by norm_num) (H.rnf8 3 (by norm_num) (by norm_num))
    (H.gens4 (fun _ => H.RxL7) (fun _ => H.RxA7) (fun h => absurd h (by norm_num))
      (fun h => absurd h (by norm_num)))
    fun q f h => H.cl9 q f (by omega)

theorem Cl82 : Cl P (P.normalSpan S) 8 2 :=
  Cl_of_gens P (by norm_num) (H.rnf8 2 (by norm_num) (by norm_num))
    (H.gens4 (fun _ => H.RxL8) (fun h => absurd h (by norm_num))
      (fun h => absurd h (by norm_num)) (fun h => absurd h (by norm_num)))
    fun q f h => H.cl9 q f (by omega)

/-- **Claim `A_8`, top-weight piece**: `a_(m) P ∈ 𝒩` for every normal polynomial `P` of weight
exactly eight (the full claim `A_8`, weight `≤ 8`, is `RxA_lt9`). -/
theorem RxA8 : Rx P (P.normalSpan S) a 8 :=
  Rx_of_top P (by norm_num) H.aN H.hag (H.rnf8 8 (by norm_num) (by norm_num))
    (fun q f h => H.cl9 q f (by omega)) H.RxA7 (H.rows4 H.raL H.raa H.rab H.rad)
    (H.top4 (fun _ => H.Rx_aL H.RxA6 0)
      (fun _ => H.Rx_aa (H.cl9 4 5 (by norm_num) b H.bN H.hbg)
        (H.cl9 2 5 (by norm_num) L H.LN H.hLg) 0)
      (fun _ => Rx_mode_of_Cl P _ H.hag H.hbg 0 (H.rab 0) fun _ => H.Cl64)
      (fun _ => Rx_mode_of_Cl P _ H.hag H.hdg 0 (H.rad 0) fun _ => H.Cl73))

/-- **Claim `B_7`, top-weight piece**: `b_(m) P ∈ 𝒩` for every normal polynomial `P` of weight
exactly seven (the full claim `B_7`, weight `≤ 7`, is `RxB_lt8`). -/
theorem RxB7 : Rx P (P.normalSpan S) b 7 :=
  Rx_of_top P (by norm_num) H.bN H.hbg (H.rnf8 7 (by norm_num) (by norm_num))
    (fun q f h => H.cl9 q f (by omega)) H.RxB6 (H.rows4 H.rbL H.rba H.rbb H.rbd)
    (H.top4 (fun _ => H.Rx_bL (H.cl9 4 5 (by norm_num) b H.bN H.hbg)
        (H.cl9 2 5 (by norm_num) L H.LN H.hLg) 0)
      (fun _ => Rx_mode_of_Cl P _ H.hbg H.hag 0 (H.rba 0) fun _ => H.Cl64)
      (fun _ => Rx_mode_of_Cl P _ H.hbg H.hbg 0 (H.rbb 0) fun _ => H.Cl73)
      (fun _ => Rx_mode_of_Cl P _ H.hbg H.hdg 0 (H.rbd 0) fun _ => H.Cl82))

theorem RxA_lt9 : ∀ f, f < 9 → Rx P (P.normalSpan S) a f := by
  intro f hf
  rcases Nat.lt_or_ge f 8 with h | h
  · exact H.RxA_lt8 f h
  · obtain rfl : f = 8 := by omega
    exact H.RxA8

theorem RxB_lt8 : ∀ f, f < 8 → Rx P (P.normalSpan S) b f := by
  intro f hf
  rcases Nat.lt_or_ge f 6 with h | h
  · exact H.cl9 4 f (by omega) b H.bN H.hbg
  · obtain rfl | rfl : f = 6 ∨ f = 7 := by omega
    exacts [H.RxB6, H.RxB7]

/-- The instances `a_(m) (b_(j) d) ∈ 𝒩` of `A_8`. -/
theorem claimA8 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m a (P.mode j b d) ∈ P.normalSpan S :=
  claim_of_Rx P _ H.hbg H.hdg H.rbd H.RxA_lt9

/-- The instances `b_(m) (a_(j) d) ∈ 𝒩` of `B_7`. -/
theorem claimB7 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m b (P.mode j a d) ∈ P.normalSpan S :=
  claim_of_Rx P _ H.hag H.hdg H.rad H.RxB_lt8

/-- **The PF13 Wick claims.**  The hypotheses `claimA6` (here also in the form on `a_0 b` used
by `PF13.pf13_reconstruction`), `claimA7`, `claimA8`, `claimB7` of `PF13.all_pairs` hold. -/
theorem claims :
    (∀ m : ℕ, P.mode m a (P.mode 0 a b) ∈ P.normalSpan S) ∧
    (∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m a (P.mode j a b) ∈ P.normalSpan S) ∧
    (∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m a (P.mode j a d) ∈ P.normalSpan S) ∧
    (∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m a (P.mode j b d) ∈ P.normalSpan S) ∧
    (∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m b (P.mode j a d) ∈ P.normalSpan S) :=
  ⟨fun m => H.claimA6 m 0 (by omega) le_rfl, H.claimA6, H.claimA7, H.claimA8, H.claimB7⟩

/-- **All generator rows, unconditionally.**  Every ordered pair of generators
`x, y ∈ {L, a, b, d}` has all singular products `x_(n) y` (`n ≥ 0`) in `𝒩`. -/
theorem all_pairs : ∀ x ∈ ({L, a, b, d} : Set W), ∀ y ∈ ({L, a, b, d} : Set W), ∀ n : ℕ,
    P.mode n x y ∈ P.normalSpan S :=
  PF13.all_pairs P hTN (P.vac_mem_normalSpan S) H.LN H.aN H.bN H.dN H.hLg H.hag H.hbg H.hdg
    H.hb H.hd H.hLm1 H.hL0 H.hLL2 H.hLL3 H.hLa H.haa2 H.haa3 H.haa4 H.haa5 H.raa H.rab H.rad
    H.claimA6 H.claimA7 H.claimA8 H.claimB7

end Stages

end Data

/-! ### The reconstruction in `V × V'` -/

section Product

variable {V V' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']

/-- The data of the proposition in the product `V × V'`. -/
theorem prodData (A : VertexAlgebra k V) (A' : VertexAlgebra k V')
    {L a b d : V} {L' a' b' d' : V'} {c : k}
    (hLg : L ∈ A.grade 2) (hag : a ∈ A.grade 3) (hbg : b ∈ A.grade 4) (hdg : d ∈ A.grade 5)
    (hLg' : L' ∈ A'.grade 2) (hag' : a' ∈ A'.grade 3) (hbg' : b' ∈ A'.grade 4)
    (hdg' : d' ∈ A'.grade 5)
    (hb : b = A.mode 1 a a) (hd : d = A.mode 1 a b)
    (hb' : b' = A'.mode 1 a' a') (hd' : d' = A'.mode 1 a' b')
    (hLm1 : ∀ x, A.mode 0 L x = A.T x) (hLm1' : ∀ x, A'.mode 0 L' x = A'.T x)
    (hL0 : ∀ {n : ℕ} {x : V}, x ∈ A.grade n → A.mode 1 L x = (n : k) • x)
    (hL0' : ∀ {n : ℕ} {x : V'}, x ∈ A'.grade n → A'.mode 1 L' x = (n : k) • x)
    (hLL2 : A.mode 2 L L = 0) (hLL2' : A'.mode 2 L' L' = 0)
    (hLL3 : A.mode 3 L L = (c / 2) • A.vac) (hLL3' : A'.mode 3 L' L' = (c / 2) • A'.vac)
    (hLa : ∀ m : ℤ, 2 ≤ m → A.mode m L a = 0) (hLa' : ∀ m : ℤ, 2 ≤ m → A'.mode m L' a' = 0)
    (haa2 : A.mode 2 a a = A.T L) (haa2' : A'.mode 2 a' a' = A'.T L')
    (haa3 : A.mode 3 a a = (2 : k) • L) (haa3' : A'.mode 3 a' a' = (2 : k) • L')
    (haa4 : A.mode 4 a a = 0) (haa4' : A'.mode 4 a' a' = 0)
    (haa5 : A.mode 5 a a = (c / 3) • A.vac) (haa5' : A'.mode 5 a' a' = (c / 3) • A'.vac)
    (haa0 : A.mode 0 a a = (1 / 2 : k) • A.T b - (1 / 12 : k) • (A.T ^ 3) L)
    (haa0' : A'.mode 0 a' a' = (1 / 2 : k) • A'.T b' - (1 / 12 : k) • (A'.T ^ 3) L')
    (rab : ∀ n : ℕ, ((A.mode n a b, A'.mode n a' b') : V × V') ∈
      Diagonal.diagonalSpan A A' (PF13.gens L a b d) (PF13.gens L' a' b' d'))
    (rad : ∀ n : ℕ, ((A.mode n a d, A'.mode n a' d') : V × V') ∈
      Diagonal.diagonalSpan A A' (PF13.gens L a b d) (PF13.gens L' a' b' d')) :
    Data (Diagonal.prodWeak A A')
      (Diagonal.diagGens (PF13.gens L a b d) (PF13.gens L' a' b' d'))
      (L, L') (a, a') (b, b') (d, d') c := by
  have gr : ∀ {n : ℕ} {x : V} {x' : V'}, x ∈ A.grade n → x' ∈ A'.grade n →
      ((x, x') : V × V') ∈ (Diagonal.prodWeak A A').grade n :=
    fun hx hx' => (Diagonal.mem_prodWeak_grade A A').2 ⟨hx, hx'⟩
  have hpow : ((Diagonal.prodWeak A A').T ^ 3) (L, L') = ((A.T ^ 3) L, (A'.T ^ 3) L') :=
    Diagonal.prodMap_pow_apply A.T A'.T 3 (L, L')
  have haa0P : (Diagonal.prodWeak A A').mode 0 (a, a') (a, a') =
      (1 / 2 : k) • (Diagonal.prodWeak A A').T (b, b') -
        (1 / 12 : k) • ((Diagonal.prodWeak A A').T ^ 3) (L, L') := by
    rw [hpow]
    exact Prod.ext haa0 haa0'
  exact
    { hS4 := by
        rintro _ ⟨i, rfl⟩
        cases i
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))
      L_mem := ⟨PF13.Gen.L, rfl⟩
      a_mem := ⟨PF13.Gen.a, rfl⟩
      b_mem := ⟨PF13.Gen.b, rfl⟩
      d_mem := ⟨PF13.Gen.d, rfl⟩
      hLg := gr hLg hLg'
      hag := gr hag hag'
      hbg := gr hbg hbg'
      hdg := gr hdg hdg'
      hb := Prod.ext hb hb'
      hd := Prod.ext hd hd'
      hLm1 := fun x => Prod.ext (hLm1 x.1) (hLm1' x.2)
      hL0 := fun hx => Prod.ext (hL0 ((Diagonal.mem_prodWeak_grade A A').1 hx).1)
        (hL0' ((Diagonal.mem_prodWeak_grade A A').1 hx).2)
      hLL2 := Prod.ext hLL2 hLL2'
      hLL3 := Prod.ext hLL3 hLL3'
      hLa := fun m hm => Prod.ext (hLa m hm) (hLa' m hm)
      haa0 := haa0P
      haa2 := Prod.ext haa2 haa2'
      haa3 := Prod.ext haa3 haa3'
      haa4 := Prod.ext haa4 haa4'
      haa5 := Prod.ext haa5 haa5'
      rab := rab
      rad := rad }

/-- **Proposition `prop:pf13-finite-reconstruction`, without the claims `A_6`, `A_7`, `A_8`,
`B_7`.**  The hypotheses are exactly those of `PF13.pf13_reconstruction` except
`claimA6_a0b`, `claimA7`, `claimA8`, `claimB7`, which are now proved (`Data.claims`).  All
remaining hypotheses are the proposition's own: Virasoro/primary data, the self-row, the
checked rows `(a_n b, a'_n b')`, `(a_n d, a'_n d') ∈ D`, simplicity and generation. -/
theorem pf13_reconstruction' [CharZero k] (A : VertexAlgebra k V) (A' : VertexAlgebra k V')
    {L a b d : V} {L' a' b' d' : V'} {c : k}
    (hLg : L ∈ A.grade 2) (hag : a ∈ A.grade 3) (hbg : b ∈ A.grade 4) (hdg : d ∈ A.grade 5)
    (hLg' : L' ∈ A'.grade 2) (hag' : a' ∈ A'.grade 3) (hbg' : b' ∈ A'.grade 4)
    (hdg' : d' ∈ A'.grade 5)
    (hb : b = A.mode 1 a a) (hd : d = A.mode 1 a b)
    (hb' : b' = A'.mode 1 a' a') (hd' : d' = A'.mode 1 a' b')
    (hLm1 : ∀ x, A.mode 0 L x = A.T x) (hLm1' : ∀ x, A'.mode 0 L' x = A'.T x)
    (hL0 : ∀ {n : ℕ} {x : V}, x ∈ A.grade n → A.mode 1 L x = (n : k) • x)
    (hL0' : ∀ {n : ℕ} {x : V'}, x ∈ A'.grade n → A'.mode 1 L' x = (n : k) • x)
    (hLL2 : A.mode 2 L L = 0) (hLL2' : A'.mode 2 L' L' = 0)
    (hLL3 : A.mode 3 L L = (c / 2) • A.vac) (hLL3' : A'.mode 3 L' L' = (c / 2) • A'.vac)
    (hLa : ∀ m : ℤ, 2 ≤ m → A.mode m L a = 0) (hLa' : ∀ m : ℤ, 2 ≤ m → A'.mode m L' a' = 0)
    (haa2 : A.mode 2 a a = A.T L) (haa2' : A'.mode 2 a' a' = A'.T L')
    (haa3 : A.mode 3 a a = (2 : k) • L) (haa3' : A'.mode 3 a' a' = (2 : k) • L')
    (haa4 : A.mode 4 a a = 0) (haa4' : A'.mode 4 a' a' = 0)
    (haa5 : A.mode 5 a a = (c / 3) • A.vac) (haa5' : A'.mode 5 a' a' = (c / 3) • A'.vac)
    (haa0 : A.mode 0 a a = (1 / 2 : k) • A.T b - (1 / 12 : k) • (A.T ^ 3) L)
    (haa0' : A'.mode 0 a' a' = (1 / 2 : k) • A'.T b' - (1 / 12 : k) • (A'.T ^ 3) L')
    (hab4 : ∀ j : ℤ, 4 ≤ j → A.mode j a b = 0) (hab4' : ∀ j : ℤ, 4 ≤ j → A'.mode j a' b' = 0)
    {c2 c3 : k} (hab2 : A.mode 2 a b = c2 • A.T a) (hab2' : A'.mode 2 a' b' = c2 • A'.T a')
    (hab3 : A.mode 3 a b = c3 • a) (hab3' : A'.mode 3 a' b' = c3 • a')
    (rab : ∀ n : ℕ, ((A.mode n a b, A'.mode n a' b') : V × V') ∈
      Diagonal.diagonalSpan A A' (PF13.gens L a b d) (PF13.gens L' a' b' d'))
    (rad : ∀ n : ℕ, ((A.mode n a d, A'.mode n a' d') : V × V') ∈
      Diagonal.diagonalSpan A A' (PF13.gens L a b d) (PF13.gens L' a' b' d'))
    (simple : SimpleQuotient.IsSimple A) (simple' : SimpleQuotient.IsSimple A')
    (gen : A.generated ({L, a} : Set V) = ⊤) (gen' : A'.generated ({L', a'} : Set V') = ⊤) :
    ∃ φ : V ≃ₗ[k] V', φ L = L' ∧ φ a = a' ∧ φ b = b' ∧ φ d = d' ∧ φ A.vac = A'.vac ∧
      ∀ (n : ℤ) (x y : V), φ (A.mode n x y) = A'.mode n (φ x) (φ y) := by
  have H := prodData A A' hLg hag hbg hdg hLg' hag' hbg' hdg' hb hd hb' hd' hLm1 hLm1' hL0 hL0'
    hLL2 hLL2' hLL3 hLL3' hLa hLa' haa2 haa2' haa3 haa3' haa4 haa4' haa5 haa5' haa0 haa0' rab rad
  obtain ⟨h6, -, h7, h8, hB7⟩ := H.claims
  exact PF13.pf13_reconstruction A A' hLg hag hbg hdg hLg' hag' hbg' hdg' hb hd hb' hd' hLm1
    hLm1' hL0 hL0' hLL2 hLL2' hLL3 hLL3' hLa hLa' haa2 haa2' haa3 haa3' haa4 haa4' haa5 haa5'
    haa0 haa0' hab4 hab4' hab2 hab2' hab3 hab3' rab rad h6 h7 h8 hB7 simple simple' gen gen'

/-- **Proposition `prop:pf13-finite-reconstruction` from the rows alone.**  As
`pf13_reconstruction'`, but without the hypotheses `a_n b = 0` (`n ≥ 4`), `a_3 b ∈ k·a`,
`a_2 b ∈ k·Ta`: given that the full rows `a_n b` lie in `D`, these explicit forms are not used
anywhere in the recovery (the claim `A_6` is proved on all of `𝒩 ∩ P_6`, not only on
`a_0 b`). -/
theorem pf13_reconstruction_of_rows [CharZero k] (A : VertexAlgebra k V)
    (A' : VertexAlgebra k V') {L a b d : V} {L' a' b' d' : V'} {c : k}
    (hLg : L ∈ A.grade 2) (hag : a ∈ A.grade 3) (hbg : b ∈ A.grade 4) (hdg : d ∈ A.grade 5)
    (hLg' : L' ∈ A'.grade 2) (hag' : a' ∈ A'.grade 3) (hbg' : b' ∈ A'.grade 4)
    (hdg' : d' ∈ A'.grade 5)
    (hb : b = A.mode 1 a a) (hd : d = A.mode 1 a b)
    (hb' : b' = A'.mode 1 a' a') (hd' : d' = A'.mode 1 a' b')
    (hLm1 : ∀ x, A.mode 0 L x = A.T x) (hLm1' : ∀ x, A'.mode 0 L' x = A'.T x)
    (hL0 : ∀ {n : ℕ} {x : V}, x ∈ A.grade n → A.mode 1 L x = (n : k) • x)
    (hL0' : ∀ {n : ℕ} {x : V'}, x ∈ A'.grade n → A'.mode 1 L' x = (n : k) • x)
    (hLL2 : A.mode 2 L L = 0) (hLL2' : A'.mode 2 L' L' = 0)
    (hLL3 : A.mode 3 L L = (c / 2) • A.vac) (hLL3' : A'.mode 3 L' L' = (c / 2) • A'.vac)
    (hLa : ∀ m : ℤ, 2 ≤ m → A.mode m L a = 0) (hLa' : ∀ m : ℤ, 2 ≤ m → A'.mode m L' a' = 0)
    (haa2 : A.mode 2 a a = A.T L) (haa2' : A'.mode 2 a' a' = A'.T L')
    (haa3 : A.mode 3 a a = (2 : k) • L) (haa3' : A'.mode 3 a' a' = (2 : k) • L')
    (haa4 : A.mode 4 a a = 0) (haa4' : A'.mode 4 a' a' = 0)
    (haa5 : A.mode 5 a a = (c / 3) • A.vac) (haa5' : A'.mode 5 a' a' = (c / 3) • A'.vac)
    (haa0 : A.mode 0 a a = (1 / 2 : k) • A.T b - (1 / 12 : k) • (A.T ^ 3) L)
    (haa0' : A'.mode 0 a' a' = (1 / 2 : k) • A'.T b' - (1 / 12 : k) • (A'.T ^ 3) L')
    (rab : ∀ n : ℕ, ((A.mode n a b, A'.mode n a' b') : V × V') ∈
      Diagonal.diagonalSpan A A' (PF13.gens L a b d) (PF13.gens L' a' b' d'))
    (rad : ∀ n : ℕ, ((A.mode n a d, A'.mode n a' d') : V × V') ∈
      Diagonal.diagonalSpan A A' (PF13.gens L a b d) (PF13.gens L' a' b' d'))
    (simple : SimpleQuotient.IsSimple A) (simple' : SimpleQuotient.IsSimple A')
    (gen : A.generated ({L, a} : Set V) = ⊤) (gen' : A'.generated ({L', a'} : Set V') = ⊤) :
    ∃ φ : V ≃ₗ[k] V', φ L = L' ∧ φ a = a' ∧ φ b = b' ∧ φ d = d' ∧ φ A.vac = A'.vac ∧
      ∀ (n : ℤ) (x y : V), φ (A.mode n x y) = A'.mode n (φ x) (φ y) := by
  have H := prodData A A' hLg hag hbg hdg hLg' hag' hbg' hdg' hb hd hb' hd' hLm1 hLm1' hL0 hL0'
    hLL2 hLL2' hLL3 hLL3' hLa hLa' haa2 haa2' haa3 haa3' haa4 haa4' haa5 haa5' haa0 haa0' rab rad
  have hall := H.all_pairs
  have hsub : ∀ i, ((PF13.gens L a b d i, PF13.gens L' a' b' d' i) : V × V') ∈
      ({(L, L'), (a, a'), (b, b'), (d, d')} : Set (V × V')) := by
    intro i
    cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hcert : ∀ i j (n : ℕ), ((A.mode n (PF13.gens L a b d i) (PF13.gens L a b d j),
      A'.mode n (PF13.gens L' a' b' d' i) (PF13.gens L' a' b' d' j)) : V × V') ∈
      Diagonal.diagonalSpan A A' (PF13.gens L a b d) (PF13.gens L' a' b' d') :=
    fun i j n => hall _ (hsub i) _ (hsub j) n
  have hw : ∀ i, 0 < PF13.wts i := by
    intro i
    cases i <;> decide
  have hg : ∀ i, PF13.gens L a b d i ∈ A.grade (PF13.wts i) := by
    intro i
    cases i
    exacts [hLg, hag, hbg, hdg]
  have hg' : ∀ i, PF13.gens L' a' b' d' i ∈ A'.grade (PF13.wts i) := by
    intro i
    cases i
    exacts [hLg', hag', hbg', hdg']
  have hgen : A.generated (Set.range (PF13.gens L a b d)) = ⊤ := by
    refine PF13.generated_eq_top_of_le A ?_ gen
    rintro x (rfl | rfl)
    exacts [⟨PF13.Gen.L, rfl⟩, ⟨PF13.Gen.a, rfl⟩]
  have hgen' : A'.generated (Set.range (PF13.gens L' a' b' d')) = ⊤ := by
    refine PF13.generated_eq_top_of_le A' ?_ gen'
    rintro x (rfl | rfl)
    exacts [⟨PF13.Gen.L, rfl⟩, ⟨PF13.Gen.a, rfl⟩]
  obtain ⟨φ, hφ, hvac, hmode⟩ := Diagonal.diagonal_reconstruction hw hg hg' hcert simple
    simple' hgen hgen'
  exact ⟨φ, hφ PF13.Gen.L, hφ PF13.Gen.a, hφ PF13.Gen.b, hφ PF13.Gen.d, hvac, hmode⟩

end Product

end PF13Wick

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.PF13Wick.Data.claims
#print axioms HaagerupIzumi.C8.PF13Wick.Data.all_pairs
#print axioms HaagerupIzumi.C8.PF13Wick.Data.RxA6
#print axioms HaagerupIzumi.C8.PF13Wick.Data.RxA8
#print axioms HaagerupIzumi.C8.PF13Wick.Data.RxB7
#print axioms HaagerupIzumi.C8.PF13Wick.pf13_reconstruction'
#print axioms HaagerupIzumi.C8.PF13Wick.pf13_reconstruction_of_rows
