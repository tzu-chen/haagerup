module

public import HaagerupIzumi.C8.ProofMap
public import HaagerupIzumi.C8.VertexAlgebra.PF13Wick

@[expose] public section

/-!
# The parafermion arrow of the proof map, made concrete

`ProofMap.L_pf13 : certStructural → pf13Factor` is Proposition `prop:pf13-finite-reconstruction`
(lines 2733–2836 of `c8_expanded_20260929/haagerup_c8_expanded.tex`) applied to the exact
parafermion records: "The exact parafermion records instantiate this proposition at `c = 8/5`
… Thus the proposition transports the checked polynomial identities to an identification with
the parafermion algebra" (lines 2813–2836).

The concrete objects (`PF13Data`) are the actual vertex algebra `A` generated inside `U` by the
parafermion conformal vector `L` and the weight-three primary `a` (with `b = a_(1) a`,
`d = a_(1) b`), and the parafermion algebra `A' = K(𝔰𝔩₂, 13)` with its fields `L', a', b', d'`.
`pf13Nodes R P` overrides two nodes of `R : Nodes`:

* `certStructural`: `R.certStructural`, and the PF13 records hold for the actual algebra: the
  grades, `b = a_(1) a`, `d = a_(1) b`, `L_(0) = T`, `L_(1) =` weight, `L_(2) L = 0`,
  `L_(3) L = (c/2)·𝟏`, `a` primary, and the self-row `a_(n) a` (`PF13SelfRow`);
* `pf13Factor`: there is a linear isomorphism `A ≅ A'` of vertex algebras identifying
  `L, a, b, d` with `L', a', b', d'`, i.e. the embedded factor is `K(𝔰𝔩₂, 13)`.

`pf13_arrow` proves `L_pf13` for these nodes through `PF13Wick.pf13_reconstruction_of_rows`
(the proposition with the Wick claims `A₆, A₇, A₈, B₇` proved).  The remaining inputs are the
fields of `PF13Inputs`, tagged **[external]**, **[certificate]**, **[definitional]** or
**[manuscript step]**: the same identities for `K(𝔰𝔩₂, 13)` at the same `c` (external: DLY,
Linshaw), the rows `a_(n) b`, `a_(n) d` as common differential normal polynomials in both
algebras (certificate item 2, lines 2660–2667, together with Linshaw's formulas), simplicity of
`A` (manuscript step from PCT stability, lines 2838–2839, by a CKLW-type argument that the
manuscript does not cite) and of `K(𝔰𝔩₂, 13)` (external), and generation by `L, a`
(definitional for `A`, external for `K(𝔰𝔩₂, 13)`).
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8

variable {k : Type*} [Field k] {W W' : Type*} [AddCommGroup W] [Module k W] [AddCommGroup W']
  [Module k W']

/-- The one-sided hypotheses of Proposition `prop:pf13-finite-reconstruction` (lines 2735–2745):
grades `2, 3, 4, 5` of `L, a, b, d`, `b = a_(1) a`, `d = a_(1) b`, `L` is a conformal vector of
central charge `c` (`L_(0) = T`, `L_(1)` is the weight, `L_(2) L = 0`, `L_(3) L = (c/2)·𝟏`), `a` is
primary, and the self-row `a_(5) a = (c/3)·𝟏`, `a_(4) a = 0`, `a_(3) a = 2L`, `a_(2) a = TL`,
`a_(0) a = ½ Tb − (1/12) T³L`. -/
structure PF13SelfRow (A : VertexAlgebra k W) (L a b d : W) (c : k) : Prop where
  hLg : L ∈ A.grade 2
  hag : a ∈ A.grade 3
  hbg : b ∈ A.grade 4
  hdg : d ∈ A.grade 5
  hb : b = A.mode 1 a a
  hd : d = A.mode 1 a b
  hLm1 : ∀ x, A.mode 0 L x = A.T x
  hL0 : ∀ {n : ℕ} {x : W}, x ∈ A.grade n → A.mode 1 L x = (n : k) • x
  hLL2 : A.mode 2 L L = 0
  hLL3 : A.mode 3 L L = (c / 2) • A.vac
  hLa : ∀ m : ℤ, 2 ≤ m → A.mode m L a = 0
  haa2 : A.mode 2 a a = A.T L
  haa3 : A.mode 3 a a = (2 : k) • L
  haa4 : A.mode 4 a a = 0
  haa5 : A.mode 5 a a = (c / 3) • A.vac
  haa0 : A.mode 0 a a = (1 / 2 : k) • A.T b - (1 / 12 : k) • (A.T ^ 3) L

/-- The concrete objects of the parafermion arrow. -/
structure PF13Data (k : Type*) [Field k] (W W' : Type*) [AddCommGroup W] [Module k W]
    [AddCommGroup W'] [Module k W'] where
  /-- The actual vertex algebra generated inside `U` by `L` and `a`. -/
  A : VertexAlgebra k W
  /-- The parafermion algebra `K(𝔰𝔩₂, 13)`. -/
  A' : VertexAlgebra k W'
  L : W
  a : W
  b : W
  d : W
  L' : W'
  a' : W'
  b' : W'
  d' : W'
  /-- The common central charge (`8/5`). -/
  c : k

/-- The proof map with `certStructural` (its PF13 part) and `pf13Factor` made concrete. -/
def pf13Nodes (R : Nodes) (P : PF13Data k W W') : Nodes :=
  { R with
    certStructural := R.certStructural ∧ PF13SelfRow P.A P.L P.a P.b P.d P.c
    pf13Factor := ∃ φ : W ≃ₗ[k] W', φ P.L = P.L' ∧ φ P.a = P.a' ∧ φ P.b = P.b' ∧
      φ P.d = P.d' ∧ φ P.A.vac = P.A'.vac ∧
      ∀ (n : ℤ) (x y : W), φ (P.A.mode n x y) = P.A'.mode n (φ x) (φ y) }

/-- The remaining inputs of `L_pf13`, tagged. -/
structure PF13Inputs (P : PF13Data k W W') : Prop where
  /-- [external] Dong–Lam–Yamada decoupling and Linshaw's recursive first rows: `K(𝔰𝔩₂, 13)`
  satisfies the same one-sided identities at the same `c = 8/5`. -/
  row' : PF13SelfRow P.A' P.L' P.a' P.b' P.d' P.c
  /-- [certificate] (item 2, lines 2660–2667) with [external] Linshaw (5.4), (5.7), (A.2): the
  rows `a_(n) b` are common differential normal polynomials in both algebras. -/
  rab : ∀ n : ℕ, ((P.A.mode n P.a P.b, P.A'.mode n P.a' P.b') : W × W') ∈
    Diagonal.diagonalSpan P.A P.A' (PF13.gens P.L P.a P.b P.d) (PF13.gens P.L' P.a' P.b' P.d')
  /-- [certificate], [external] The same for the rows `a_(n) d`. -/
  rad : ∀ n : ℕ, ((P.A.mode n P.a P.d, P.A'.mode n P.a' P.d') : W × W') ∈
    Diagonal.diagonalSpan P.A P.A' (PF13.gens P.L P.a P.b P.d) (PF13.gens P.L' P.a' P.b' P.d')
  /-- [manuscript step] The actual generated algebra is simple, from its PCT stability
  (lines 2838–2839; a CKLW-type argument, not cited). -/
  simple : SimpleQuotient.IsSimple P.A
  /-- [external] `K(𝔰𝔩₂, 13)` is simple. -/
  simple' : SimpleQuotient.IsSimple P.A'
  /-- [definitional] `A` is the algebra generated by `L, a`. -/
  gen : P.A.generated ({P.L, P.a} : Set W) = ⊤
  /-- [external] `K(𝔰𝔩₂, 13)` is generated by `L', a'`. -/
  gen' : P.A'.generated ({P.L', P.a'} : Set W') = ⊤

/-- **`L_pf13`** (Proposition `prop:pf13-finite-reconstruction` with the PF13 records).

* Concrete nodes: `certStructural` (the PF13 records for the actual algebra), `pf13Factor`.
* Concrete theorem: `PF13Wick.pf13_reconstruction_of_rows` (OPE recovery through the proved Wick
  claims `A₆, A₇, A₈, B₇`, then `Diagonal.diagonal_reconstruction` /
  `SimpleQuotient.simple_quotient_unique`).
* Remaining inputs: the fields of `PF13Inputs` (tagged there). -/
theorem pf13_arrow [CharZero k] (R : Nodes) (P : PF13Data k W W') (H : PF13Inputs P) :
    (pf13Nodes R P).certStructural → (pf13Nodes R P).pf13Factor := by
  rintro ⟨-, S⟩
  obtain ⟨hrow', rab, rad, simple, simple', gen, gen'⟩ := H
  exact PF13Wick.pf13_reconstruction_of_rows P.A P.A' S.hLg S.hag S.hbg S.hdg hrow'.hLg
    hrow'.hag hrow'.hbg hrow'.hdg S.hb S.hd hrow'.hb hrow'.hd S.hLm1 hrow'.hLm1 S.hL0 hrow'.hL0
    S.hLL2 hrow'.hLL2 S.hLL3 hrow'.hLL3 S.hLa hrow'.hLa S.haa2 hrow'.haa2 S.haa3 hrow'.haa3
    S.haa4 hrow'.haa4 S.haa5 hrow'.haa5 S.haa0 hrow'.haa0 rab rad simple simple' gen gen'

#print axioms pf13_arrow

end HaagerupIzumi.C8.ProofMap
