module

public import HaagerupIzumi.C8.VertexAlgebra.PF13

@[expose] public section

/-!
# PF13: the reconstruction statement in `V × V'`

Proposition `prop:pf13-finite-reconstruction` (lines 2732–2827 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`), assembled from `PF13.all_pairs` (recovery of
the generator rows inside the diagonal normal span `D ⊂ V × V'`) and
`Diagonal.diagonal_reconstruction` (uniqueness of the simple quotient).

`pf13_reconstruction`: let `V`, `V'` be simple vertex algebras of CFT type (characteristic
zero) with `L, a, b = a_(1) a, d = a_(1) b` (weights 2, 3, 4, 5) and `L', a', b', d'`, such that
`L`, `L'` act by `L(-1) = T`, `L(0) = weight`, satisfy the Virasoro relations `L_2 L = 0`,
`L_3 L = (c/2)·1`, `a`, `a'` are primary of weight 3, the self-row values
`a_2 a = TL`, `a_3 a = 2L`, `a_4 a = 0`, `a_5 a = (c/3)·1` hold in both, and `L, a` generate.
If the rows `(a_n b, a'_n b')`, `(a_n d, a'_n d')` lie in `D` (the checked PF13 records; the
`a, a` row follows from the self-row, `raa_of_selfrow`), the remaining self-row facts
`a_0 a = ½Tb − (1/12)T³L`, `a_n b = 0` (`n ≥ 4`), `a_3 b ∈ k·a`, `a_2 b ∈ k·Ta` hold, **and the
manuscript's intermediate claims `A_6` (only on `a_0 b`, by `hA6_of_a0b`), `A_7`, `A_8`, `B_7` hold
(hypotheses `claimA6_a0b`, `claimA7`, `claimA8`, `claimB7`: not certificate inputs)**, then
`V ≅ V'` identifying `L, a, b, d`.  The four claims are proved in `VertexAlgebra/PF13Wick.lean`;
the unconditional statements are `PF13Wick.pf13_reconstruction'` and
`PF13Wick.pf13_reconstruction_of_rows` (the latter also without `a_n b = 0` (`n ≥ 4`),
`a_3 b ∈ k·a`, `a_2 b ∈ k·Ta`, which are not used).
-/

namespace HaagerupIzumi.C8

namespace PF13

/-- Indices of the four named generators. -/
inductive Gen
  | L
  | a
  | b
  | d

/-- The generator family `L, a, b, d`. -/
def gens {X : Type*} (L a b d : X) : Gen → X
  | .L => L
  | .a => a
  | .b => b
  | .d => d

/-- Their weights `2, 3, 4, 5`. -/
def wts : Gen → ℕ
  | .L => 2
  | .a => 3
  | .b => 4
  | .d => 5

variable {k : Type*} [Field k] {V V' : Type*} [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V']

theorem generated_eq_top_of_le (A : VertexAlgebra k V) {G G' : Set V} (hGG' : G ⊆ G')
    (hG : A.generated G = ⊤) : A.generated G' = ⊤ := by
  rw [eq_top_iff, ← hG]
  exact A.generated_le (A.generated_isSubalgebra G')
    (fun x hx => A.subset_generated G' (hGG' hx))

section Reduce

variable {W : Type*} [AddCommGroup W] [Module k W] (P : WeakVertexAlgebra k W)
  {N : Submodule k W} {a b d : W}

/-- **The `A_6` instances reduce to `a_(0) b`.**  Using the self-row facts `a_n b = 0` (`n ≥ 4`),
`a_3 b ∈ k·a`, `a_2 b ∈ k·Ta` and `a_1 b = d`, the hypothesis `claimA6` of `all_pairs`
(`a_(m) (a_(j) b) ∈ N`) follows from its single genuinely new family `a_(m) (a_(0) b) ∈ N`
(hypothesis `h0`), `a_0 b` being of weight six.  `h0` is an instance of the manuscript's claim
`A_6`; it is not a certificate input and is not formalized here. -/
theorem hA6_of_a0b (hT : ∀ x ∈ N, P.T x ∈ N) (hd : d = P.mode 1 a b)
    (raa : ∀ n : ℕ, P.mode n a a ∈ N) (rad : ∀ n : ℕ, P.mode n a d ∈ N)
    (hab4 : ∀ j : ℤ, 4 ≤ j → P.mode j a b = 0) {c2 c3 : k}
    (hab2 : P.mode 2 a b = c2 • P.T a) (hab3 : P.mode 3 a b = c3 • a)
    (h0 : ∀ m : ℕ, P.mode m a (P.mode 0 a b) ∈ N) :
    ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → P.mode m a (P.mode j a b) ∈ N := by
  intro m j hm hj
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hm
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ 4 ≤ j) with rfl | rfl | rfl | rfl | hj4
  · exact h0 m
  · rw [← hd]
    exact rad m
  · rw [hab2, map_smul]
    refine Submodule.smul_mem _ _ ?_
    have e : P.mode m a (P.T a) = P.T (P.mode m a a) - P.mode m (P.T a) a := by
      rw [P.T_mode]
      abel
    rw [e, P.mode_T]
    refine Submodule.sub_mem _ (hT _ (raa m)) (Submodule.neg_mem _ ?_)
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · simp
    · refine Submodule.smul_mem _ _ ?_
      have e1 : ((m : ℕ) : ℤ) - 1 = ((m - 1 : ℕ) : ℤ) := by omega
      rw [e1]
      exact raa (m - 1)
  · rw [hab3, map_smul]
    exact Submodule.smul_mem _ _ (raa m)
  · rw [hab4 j hj4, map_zero]
    exact Submodule.zero_mem _

/-- **The `a, a` row follows from the self-row.**  If `a_0 a = ½ T b - (1/12) T³ L`, `a_1 a = b`,
`a_2 a = T L`, `a_3 a = 2L`, `a_4 a = 0`, `a_5 a = (c/3)·1`, then `a_(n) a ∈ N` for all `n ≥ 0`. -/
theorem raa_of_selfrow {L : W} {c : k} (hT : ∀ x ∈ N, P.T x ∈ N) (hvacN : P.vac ∈ N)
    (hLN : L ∈ N) (hbN : b ∈ N) (hag : a ∈ P.grade 3) (hb : b = P.mode 1 a a)
    (haa0 : P.mode 0 a a = (1 / 2 : k) • P.T b - (1 / 12 : k) • (P.T ^ 3) L)
    (haa2 : P.mode 2 a a = P.T L) (haa3 : P.mode 3 a a = (2 : k) • L)
    (haa4 : P.mode 4 a a = 0) (haa5 : P.mode 5 a a = (c / 3) • P.vac) :
    ∀ n : ℕ, P.mode n a a ∈ N := by
  intro n
  rcases Nat.lt_or_ge n 6 with hn | hn
  · obtain rfl | rfl | rfl | rfl | rfl | rfl :
        n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
    · rw [Nat.cast_zero, haa0]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hT _ hbN))
        (Submodule.smul_mem _ _ (P.T_pow_mem hT 3 hLN))
    · rw [Nat.cast_one, ← hb]
      exact hbN
    · rw [show ((2 : ℕ) : ℤ) = 2 from rfl, haa2]
      exact hT _ hLN
    · rw [show ((3 : ℕ) : ℤ) = 3 from rfl, haa3]
      exact Submodule.smul_mem _ _ hLN
    · rw [show ((4 : ℕ) : ℤ) = 4 from rfl, haa4]
      exact Submodule.zero_mem _
    · rw [show ((5 : ℕ) : ℤ) = 5 from rfl, haa5]
      exact Submodule.smul_mem _ _ hvacN
  · rw [P.mode_trunc (n : ℤ) hag hag (by omega)]
    exact Submodule.zero_mem _

end Reduce

/-- **Proposition `prop:pf13-finite-reconstruction`, given the manuscript claims
`A_6` (on `a_0 b`), `A_7`, `A_8`, `B_7`.**  The hypotheses `claimA6_a0b`, `claimA7`, `claimA8`,
`claimB7` are instances of the manuscript's intermediate claims `A_r`/`B_r` (lines 2777–2811),
not certificate inputs; they are proved in `PF13Wick.Data.claims`, and
`PF13Wick.pf13_reconstruction'` is this theorem without them.  All other hypotheses are the proposition's own: Virasoro/primary data, the self-row
(`a_0 a = ½Tb − (1/12)T³L`, `a_2 a = TL`, `a_3 a = 2L`, `a_4 a = 0`, `a_5 a = (c/3)·1`,
`a_n b = 0` for `n ≥ 4`, `a_3 b ∈ k·a`, `a_2 b ∈ k·Ta`, with the same constants in `V` and
`V'`), the certificate rows `(a_n b, a'_n b')`, `(a_n d, a'_n d') ∈ D` (the `a, a` row is derived
from the self-row), simplicity, and generation by `L, a`. -/
theorem pf13_reconstruction [CharZero k] (A : VertexAlgebra k V) (A' : VertexAlgebra k V')
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
      Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d'))
    (rad : ∀ n : ℕ, ((A.mode n a d, A'.mode n a' d') : V × V') ∈
      Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d'))
    (claimA6_a0b : ∀ m : ℕ, ((A.mode m a (A.mode 0 a b),
      A'.mode m a' (A'.mode 0 a' b')) : V × V') ∈
      Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d'))
    (claimA7 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → ((A.mode m a (A.mode j a d),
      A'.mode m a' (A'.mode j a' d')) : V × V') ∈
      Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d'))
    (claimA8 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → ((A.mode m a (A.mode j b d),
      A'.mode m a' (A'.mode j b' d')) : V × V') ∈
      Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d'))
    (claimB7 : ∀ m j : ℤ, 0 ≤ m → 0 ≤ j → ((A.mode m b (A.mode j a d),
      A'.mode m b' (A'.mode j a' d')) : V × V') ∈
      Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d'))
    (simple : SimpleQuotient.IsSimple A) (simple' : SimpleQuotient.IsSimple A')
    (gen : A.generated ({L, a} : Set V) = ⊤) (gen' : A'.generated ({L', a'} : Set V') = ⊤) :
    ∃ φ : V ≃ₗ[k] V', φ L = L' ∧ φ a = a' ∧ φ b = b' ∧ φ d = d' ∧ φ A.vac = A'.vac ∧
      ∀ (n : ℤ) (x y : V), φ (A.mode n x y) = A'.mode n (φ x) (φ y) := by
  have mem := Diagonal.diag_mem_diagonalSpan A A' (gens L a b d) (gens L' a' b' d')
  have gr : ∀ {n : ℕ} {x : V} {x' : V'}, x ∈ A.grade n → x' ∈ A'.grade n →
      ((x, x') : V × V') ∈ (Diagonal.prodWeak A A').grade n :=
    fun hx hx' => (Diagonal.mem_prodWeak_grade A A').2 ⟨hx, hx'⟩
  have hT : ∀ x ∈ Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d'),
      (Diagonal.prodWeak A A').T x ∈ Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d') :=
    fun _ hx => (Diagonal.prodWeak A A').T_mem_normalSpan hx
  have hpow : ((Diagonal.prodWeak A A').T ^ 3) (L, L') = ((A.T ^ 3) L, (A'.T ^ 3) L') :=
    Diagonal.prodMap_pow_apply A.T A'.T 3 (L, L')
  have haa0P : (Diagonal.prodWeak A A').mode 0 (a, a') (a, a') =
      (1 / 2 : k) • (Diagonal.prodWeak A A').T (b, b') -
        (1 / 12 : k) • ((Diagonal.prodWeak A A').T ^ 3) (L, L') := by
    rw [hpow]
    exact Prod.ext haa0 haa0'
  have raa := raa_of_selfrow (Diagonal.prodWeak A A')
    (N := Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d'))
    (a := (a, a')) (b := (b, b')) (L := (L, L')) (c := c) hT
    ((Diagonal.prodWeak A A').vac_mem_normalSpan _) (mem Gen.L) (mem Gen.b) (gr hag hag')
    (Prod.ext hb hb') haa0P (Prod.ext haa2 haa2') (Prod.ext haa3 haa3') (Prod.ext haa4 haa4')
    (Prod.ext haa5 haa5')
  have hA6 := hA6_of_a0b (Diagonal.prodWeak A A')
    (N := Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d'))
    (a := (a, a')) (b := (b, b')) (d := (d, d')) hT (Prod.ext hd hd') raa rad
    (fun j hj => Prod.ext (hab4 j hj) (hab4' j hj)) (Prod.ext hab2 hab2') (Prod.ext hab3 hab3')
    claimA6_a0b
  have hall := all_pairs (Diagonal.prodWeak A A')
    (N := Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d'))
    (L := (L, L')) (a := (a, a')) (b := (b, b')) (d := (d, d')) (c := c)
    hT ((Diagonal.prodWeak A A').vac_mem_normalSpan _)
    (mem Gen.L) (mem Gen.a) (mem Gen.b) (mem Gen.d)
    (gr hLg hLg') (gr hag hag') (gr hbg hbg') (gr hdg hdg')
    (Prod.ext hb hb') (Prod.ext hd hd')
    (fun x => Prod.ext (hLm1 x.1) (hLm1' x.2))
    (fun hx => Prod.ext (hL0 ((Diagonal.mem_prodWeak_grade A A').1 hx).1)
      (hL0' ((Diagonal.mem_prodWeak_grade A A').1 hx).2))
    (Prod.ext hLL2 hLL2') (Prod.ext hLL3 hLL3')
    (fun m hm => Prod.ext (hLa m hm) (hLa' m hm))
    (Prod.ext haa2 haa2') (Prod.ext haa3 haa3') (Prod.ext haa4 haa4') (Prod.ext haa5 haa5')
    raa rab rad hA6 claimA7 claimA8 claimB7
  have hsub : ∀ i, ((gens L a b d i, gens L' a' b' d' i) : V × V') ∈
      ({(L, L'), (a, a'), (b, b'), (d, d')} : Set (V × V')) := by
    intro i
    cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  have hcert : ∀ i j (n : ℕ), ((A.mode n (gens L a b d i) (gens L a b d j),
      A'.mode n (gens L' a' b' d' i) (gens L' a' b' d' j)) : V × V') ∈
      Diagonal.diagonalSpan A A' (gens L a b d) (gens L' a' b' d') :=
    fun i j n => hall _ (hsub i) _ (hsub j) n
  have hw : ∀ i, 0 < wts i := by
    intro i
    cases i <;> decide
  have hg : ∀ i, gens L a b d i ∈ A.grade (wts i) := by
    intro i
    cases i
    exacts [hLg, hag, hbg, hdg]
  have hg' : ∀ i, gens L' a' b' d' i ∈ A'.grade (wts i) := by
    intro i
    cases i
    exacts [hLg', hag', hbg', hdg']
  have hgen : A.generated (Set.range (gens L a b d)) = ⊤ := by
    refine generated_eq_top_of_le A ?_ gen
    rintro x (rfl | rfl)
    exacts [⟨Gen.L, rfl⟩, ⟨Gen.a, rfl⟩]
  have hgen' : A'.generated (Set.range (gens L' a' b' d')) = ⊤ := by
    refine generated_eq_top_of_le A' ?_ gen'
    rintro x (rfl | rfl)
    exacts [⟨Gen.L, rfl⟩, ⟨Gen.a, rfl⟩]
  obtain ⟨φ, hφ, hvac, hmode⟩ := Diagonal.diagonal_reconstruction hw hg hg' hcert simple simple'
    hgen hgen'
  exact ⟨φ, hφ Gen.L, hφ Gen.a, hφ Gen.b, hφ Gen.d, hvac, hmode⟩


end PF13

end HaagerupIzumi.C8

#print axioms HaagerupIzumi.C8.PF13.pf13_reconstruction
#print axioms HaagerupIzumi.C8.PF13.hA6_of_a0b
#print axioms HaagerupIzumi.C8.PF13.raa_of_selfrow
