module

public import HaagerupIzumi.C8.ProofMap
public import HaagerupIzumi.C8.Fusion.Rank6Iso
public import HaagerupIzumi.C8.Fusion.AutInvertible
public import HaagerupIzumi.C8.Fusion.Center
public import HaagerupIzumi.C8.NumberTheory.LarsonProof
public import HaagerupIzumi.C8.FormalCodegrees
public import HaagerupIzumi.C8.Branching

@[expose] public section

/-!
# The boundary fusion ring branch of the proof map, made concrete

`ProofMap.lean` states Appendix G with opaque nodes.  Here the nodes of the boundary-ring
branch are given concrete meanings in terms of the concrete objects of that branch
(`BoundaryData`):

* `F : BasedRing ι` — the fusion ring `K₀(𝓕)` of the boundary category `𝓕 = Rep(U)_H`;
* `a : ι` — the invertible simple attached to the order-three automorphism of `H/B`;
* `d : ι → ℝ` — the (positive, spherical = Frobenius–Perron) dimensions, `s = FPdim B`,
  `d_X`, `d_Y`;
* the numerical invariants of the center `Z(𝓕)` used in Lemma `lem:rank6-induction`: the
  twists `θC j` and multiplicities `b j = [F(C_j) : ρ]` of the three simple summands of `I(a)`,
  the residual central simples `Z_j` (`j : κ`) with `F(Z_j) = n_j R` and twists `θ j`,
  `ε = ν₂(ρ)` and `ν₃ = ν₃(a)`.

`boundaryNodes R B` overrides the following fields of an arbitrary `R : Nodes`
(manuscript line numbers refer to `c8_expanded_20260929/haagerup_c8_expanded.tex`):

| node | concrete statement |
|---|---|
| `lagrangianCenter` | `R.lagrangianCenter`, and `d` is a positive dimension character with `d_{x*} = d_x`, `∑ d_i² = Dim 𝓕 = 3s`, `d_X = s - 1` (lines 3243–3260) |
| `rankFork` | `R.rankFork`, and `rank 𝓕 = card ι ∈ {4, 6}` |
| `invertiblesContainZ3` | `a` is invertible, `a ≠ 𝟙`, `a ⊗ a = a*` |
| `noSignExtension` | `R.noSignExtension`, and `d_X ≠ 1` |
| `threeInvertibles` | the invertible simples are exactly `𝟙, a, a* = a ⊗ a` |
| `untwistedPointed` | `R.untwistedPointed`, and `ν₃(a) = 1` |
| `notRankFour` | `R.notRankFour`, and `card ι ≠ 4` |
| `rankSixRing` | `F` is eq:rank6-ring for some `m ≥ 1` (`IsHIRing`) |
| `rankSixMoments` | the conclusions of Lemma `lem:rank6-induction`: `d_ρ = (3m+√Δ)/2`, `C`-twists `1, ζ₃, ζ₃²` with `b_j = m`, `n_j > 0`, `∑ n_j² = 4m²+2`, eq:indicator-first, eq:indicator-second, `ε = ±1` |
| `multiplicityOne` | `F` is eq:rank6-ring with `m = 1` (the ring `HI(ℤ/3)`) |
| `twelveTwists` | `m = 1`, `d_ρ = (3+√13)/2`, `C`-twists `1, ζ₃, ζ₃²`, six residual simples with `n_j = 1` whose twists are the six nonresidue thirteenth roots, each once, and `ε = 1` |

Where a node of `ProofMap` carries categorical content beyond these objects (an equivalence of
categories, an associator class, an isomorphism type), and the node is *not* the conclusion of
an arrow proved here, the opaque field of `R` is kept as a conjunct; only nodes concluded by the
arrows below are replaced outright.

`boundary_arrows` proves the six arrows `L_autInvertible`, `L_threeInvertibles`,
`L_rankSixRing`, `L_rankSixMoments`, `L_multiplicityOne`, `L_twelveTwists` for these nodes.  The
remaining inputs are explicit hypotheses of the individual arrow theorems, tagged as
**[external]** (a cited theorem), **[certificate]** (lattice data of the ledger),
**[definitional]** (what a concrete parameter means), or **[manuscript step]** (an argument of the
manuscript that is not formalized here):

* `L_autInvertible` (`AutExpansion`, conditional on `certDiscriminant`, which supplies the
  order-three automorphism `g` of `H = B ⊕ J ⊕ J²`): coefficients `0` or `d_a`
  ([manuscript step] `f ∗ f = f` for algebra automorphisms, lines 3283–3289, with [external] BJ:
  the primitive convolution idempotents are `d_a [a]`), composition is fusion multiplication
  ([external] BJ, Lemma 3.1, Cor. 3.4), `g ≠ id` and `a` is the invertible attached to `g`
  ([definitional]);
* `L_rankSixRing` (`hΨ`): at rank six, `K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` ([external] BJ, Cor. 3.4:
  `End_𝒞(H) ≅ K₀(𝓕) ⊗ ℂ`; [manuscript step] `End_𝒞(1 ⊕ X ⊕ 2Y) ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)`,
  lines 3794–3800).  The rank six is supplied by the nodes `rankFork` and `notRankFour`;
* `L_rankSixMoments` (`InductionFormulas`): the twist-trace formula of Ng–Schauenburg, the
  induction–codegree correspondence of Ostrik, Vafa's theorem, the Frobenius–Schur indicator
  `ν₂(ρ) = ±1` and `Dim Z(𝓕) = (Dim 𝓕)²` ([external]), each *evaluated* on the decomposition
  `I(1) = 1 + X + 2Y` (`θ_X = θ_Y = 1`), `I(a) = C₀ + C₁ + C₂`, `F(C_j) = a + a² + b_j R`,
  `I(ρ) = mX + mY + ∑ b_j C_j + ∑ n_j Z_j`, together with the exhaustion of the center simples by
  `1, X, Y, C_j, Z_j` ([manuscript step], lines 3870–3906); see the field docstrings;
* `L_multiplicityOne`: none; Larson's Theorem 1.3 (`NumberTheory.larsonRootCount`) and Lemma
  `lem:conductor40` (`NumberTheory.conductor40Bound`) are proved;
* `L_twelveTwists`: none; the Galois-averaging step of Lemma `lem:six-residual-twists` is proved
  (`NumberTheory.nonresidueOrbitStep`).

The index types are not linked to the other branches: `ι` indexes the simples of `𝓕`, `κ` the
residual simples of `Z(𝓕) ≃ Rep(U)` (which correspond to the labels `d₁, …, d₆` of
`Characters.Label`); nothing in the model identifies them with those labels.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8.Fusion HaagerupIzumi.C8.NumberTheory HaagerupIzumi.C8.CubeRootTwists

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-! ### The concrete objects -/

/-- The concrete data of the boundary category `𝓕 = Rep(U)_H` and of its center `Z(𝓕) ≃ Rep(U)`
that Appendix G works with. -/
structure BoundaryData (ι κ : Type*) [Fintype ι] [DecidableEq ι] where
  /-- The fusion ring `K₀(𝓕)`. -/
  F : BasedRing ι
  /-- The invertible simple attached to the order-three automorphism of `H/B`. -/
  a : ι
  /-- Dimensions of the simples of `𝓕`. -/
  d : ι → ℝ
  /-- `s = FPdim B`. -/
  s : ℝ
  /-- `d_X` for the summand `X` of `B↓U = U ⊕ X` (also a summand of `I(1) = H`). -/
  dX : ℝ
  /-- `d_Y` for the summand `Y` of `H↓U`. -/
  dY : ℝ
  /-- Twists of the three simple summands `C₀, C₁, C₂` of `I(a)`. -/
  θC : Fin 3 → ℂ
  /-- `b_j = [F(C_j) : ρ]`. -/
  b : Fin 3 → ℕ
  /-- The residual central simples `Z_j` have forgetful images `F(Z_j) = n_j R`. -/
  n : κ → ℕ
  /-- The twists of the residual central simples. -/
  θ : κ → ℂ
  /-- `ε = ν₂(ρ)`. -/
  ε : ℤ
  /-- `ν₃(a)`. -/
  ν₃ : ℂ

/-- `a` generates a copy of `ℤ/3` among the invertible simples: `a` is invertible, `a ≠ 𝟙` and
`a ⊗ a = a*` (so `a³ = 𝟙`). -/
def Z3Generator (F : BasedRing ι) (a : ι) : Prop :=
  F.IsInvertible a ∧ a ≠ F.unit ∧ ∀ l, F.N a a l = if l = F.dual a then 1 else 0

/-- Pseudo-unitarity, as used in Appendix G (lines 3256–3260): the dimension function is a
positive character of the fusion ring, invariant under duality. -/
def PositiveDims (F : BasedRing ι) (d : ι → ℝ) : Prop :=
  F.IsCharacter d ∧ (∀ i, 0 < d i) ∧ ∀ i, d (F.dual i) = d i

/-- The `C`-part of Lemma `lem:rank6-induction`: `b_j = m` and the twists of `C₀, C₁, C₂` are
`1, ζ₃, ζ₃²`, once each. -/
def CTwists (m : ℕ) (B : BoundaryData ι κ) : Prop :=
  (∀ j, B.b j = m) ∧
    ∃ e : Fin 3 → Fin 3, (e 0 ≠ e 1 ∧ e 0 ≠ e 2 ∧ e 1 ≠ e 2) ∧ ∀ j, B.θC j = zeta3 ^ (e j : ℕ)

/-- The residual part of Lemma `lem:rank6-induction` (lines 3842–3858), with
`Δ = 9m² + 4`. -/
structure ResidualMoments (m : ℕ) (B : BoundaryData ι κ) : Prop where
  n_pos : ∀ j, 0 < B.n j
  root : ∀ j, IsRootOfUnity (B.θ j)
  sum_sq : ∑ j, B.n j ^ 2 = 4 * m ^ 2 + 2
  /-- eq:indicator-first. -/
  first : ∑ j, (B.n j : ℂ) ^ 2 * B.θ j =
    -((m : ℂ) ^ 2 + (m : ℂ) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2
  eps : B.ε = 1 ∨ B.ε = -1
  /-- eq:indicator-second. -/
  second : ∑ j, (B.n j : ℂ) ^ 2 * B.θ j ^ 2 =
    (-(m : ℂ) ^ 2 + (2 * (B.ε : ℂ) - m) * (Real.sqrt (9 * (m : ℝ) ^ 2 + 4) : ℂ)) / 2

/-- The residual part of the twelve-simple list of line 4053 (Lemma `lem:six-residual-twists`):
six residual central simples, each with `n_j = 1`, whose twists are exactly the six nonresidue
thirteenth roots of unity, each once, and `ε = ν₂(ρ) = 1`. -/
structure SixResidualTwists (B : BoundaryData ι κ) : Prop where
  card : Fintype.card κ = 6
  n_one : ∀ j, B.n j = 1
  injective : Function.Injective B.θ
  nonresidue : ∀ j, ∃ e ∈ nonresidues13, B.θ j = zeta13 ^ e
  onto : ∀ e ∈ nonresidues13, ∃ j, B.θ j = zeta13 ^ e
  eps_one : B.ε = 1

/-- The external inputs of Lemma `lem:rank6-induction` (lines 3842–3914), *evaluated* on the
decomposition of the induced objects, for the ring eq:rank6-ring with multiplicity `m` and
`δ = d_ρ`; `Dim 𝓕 = 3(1 + δ²)`.  The induced objects are `I(1) = 1 + X + 2Y`,
`I(a) = C₀ + C₁ + C₂` with `F(C_j) = a + a² + b_j R` (so `d_{C_j} = 2 + 3 b_j δ`), and
`I(ρ) = mX + mY + ∑ b_j C_j + ∑ n_j Z_j` with `d_{Z_j} = 3 n_j δ` and `θ_X = θ_Y = 1`. -/
structure InductionFormulas (m : ℕ) (δ : ℝ) (B : BoundaryData ι κ) : Prop where
  /-- [external] Ostrik (Theorems 2.5, 2.13): `d_X = Dim 𝓕 / f`, `f = 3 + 3(-1/δ)²` the formal
  codegree of the character `a ↦ 1, ρ ↦ -δ⁻¹`. -/
  codegree_X : B.dX = 3 * (1 + δ ^ 2) / (3 + 3 * (-1 / δ) ^ 2)
  /-- [external] Ostrik: `d_Y = Dim 𝓕 / 3`; [manuscript step] `3` is the formal codegree of the
  two-dimensional representation (line 3864). -/
  codegree_Y : B.dY = 3 * (1 + δ ^ 2) / 3
  /-- [external] Vafa: the twists of `C_j` are roots of unity. -/
  rootC : ∀ j, IsRootOfUnity (B.θC j)
  /-- [external] Vafa: the residual twists are roots of unity. -/
  root : ∀ j, IsRootOfUnity (B.θ j)
  /-- [manuscript step] The residual simples have nonzero forgetful images `n_j R`, `n_j > 0`. -/
  n_pos : ∀ j, 0 < B.n j
  /-- [manuscript step] Adjunction: `[F I(a) : ρ] = 3m` (lines 3877–3880). -/
  sum_b : B.b 0 + B.b 1 + B.b 2 = 3 * m
  /-- [external] Ng–Schauenburg for `V = a`, `n = 1`, on [manuscript step] `I(a) = ∑ C_j`:
  `∑ d_{C_j} θ_{C_j} = Dim 𝓕 · ν₁(a) = 0`. -/
  nu1_a : ∑ j, ((2 + 3 * (B.b j : ℝ) * δ : ℝ) : ℂ) * B.θC j = 0
  /-- [external] Ng–Schauenburg for `V = a`, `n = 3`, on [manuscript step] `I(a) = ∑ C_j`:
  `∑ d_{C_j} θ_{C_j}³ = Dim 𝓕 · ν₃(a)`. -/
  nu3_a : ∑ j, ((2 + 3 * (B.b j : ℝ) * δ : ℝ) : ℂ) * B.θC j ^ 3 =
    B.ν₃ * ((3 * (1 + δ ^ 2) : ℝ) : ℂ)
  /-- [external] Ng–Schauenburg for `V = ρ`, `n = 1`, on [manuscript step] the decomposition of
  `I(ρ)` with `θ_X = θ_Y = 1`: `∑ [I(ρ) : Z] d_Z θ_Z = Dim 𝓕 · ν₁(ρ) = 0`. -/
  nu1_ρ : (m : ℂ) * (B.dX : ℂ) + (m : ℂ) * (B.dY : ℂ) +
      ∑ j, (B.b j : ℂ) * ((2 + 3 * (B.b j : ℝ) * δ : ℝ) : ℂ) * B.θC j +
      ∑ j, (B.n j : ℂ) * ((3 * (B.n j : ℝ) * δ : ℝ) : ℂ) * B.θ j = 0
  /-- [external] Ng–Schauenburg for `V = ρ`, `n = 2`, on [manuscript step] the same
  decomposition: `∑ [I(ρ) : Z] d_Z θ_Z² = Dim 𝓕 · ν₂(ρ)`. -/
  nu2_ρ : (m : ℂ) * (B.dX : ℂ) + (m : ℂ) * (B.dY : ℂ) +
      ∑ j, (B.b j : ℂ) * ((2 + 3 * (B.b j : ℝ) * δ : ℝ) : ℂ) * B.θC j ^ 2 +
      ∑ j, (B.n j : ℂ) * ((3 * (B.n j : ℝ) * δ : ℝ) : ℂ) * B.θ j ^ 2 =
      (B.ε : ℂ) * ((3 * (1 + δ ^ 2) : ℝ) : ℂ)
  /-- [external] The second Frobenius–Schur indicator of the self-dual simple `ρ` is `±1`. -/
  eps : B.ε = 1 ∨ B.ε = -1
  /-- [external] `Dim Z(𝓕) = (Dim 𝓕)²`, summed over [manuscript step] the complete list of
  center simples `1, X, Y, C_j, Z_j` (lines 3897–3904). -/
  center_dim : (3 * (1 + δ ^ 2)) ^ 2 = 1 + B.dX ^ 2 + B.dY ^ 2 +
      ∑ j, (2 + 3 * (B.b j : ℝ) * δ) ^ 2 + ∑ j, (3 * (B.n j : ℝ) * δ) ^ 2

/-! ### The concrete nodes -/

/-- The proof map with the nodes of the boundary-ring branch made concrete (see the module
docstring for the table). -/
def boundaryNodes (R : Nodes) (B : BoundaryData ι κ) : Nodes :=
  { R with
    lagrangianCenter := R.lagrangianCenter ∧ PositiveDims B.F B.d ∧
      ∑ i, B.d i ^ 2 = 3 * B.s ∧ B.dX = B.s - 1
    rankFork := R.rankFork ∧ (Fintype.card ι = 4 ∨ Fintype.card ι = 6)
    invertiblesContainZ3 := Z3Generator B.F B.a
    noSignExtension := R.noSignExtension ∧ B.dX ≠ 1
    threeInvertibles := Z3Generator B.F B.a ∧
      ∀ x, B.F.IsInvertible x → x = B.F.unit ∨ x = B.a ∨ x = B.F.dual B.a
    untwistedPointed := R.untwistedPointed ∧ B.ν₃ = 1
    notRankFour := R.notRankFour ∧ Fintype.card ι ≠ 4
    rankSixRing := ∃ ρ ρ₁ ρ₂ m, IsHIRing B.F B.a ρ ρ₁ ρ₂ m
    rankSixMoments := ∃ ρ ρ₁ ρ₂ m, IsHIRing B.F B.a ρ ρ₁ ρ₂ m ∧
      B.d ρ = (3 * m + Real.sqrt (9 * (m : ℝ) ^ 2 + 4)) / 2 ∧ CTwists m B ∧ ResidualMoments m B
    multiplicityOne := ∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1
    twelveTwists := ∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1 ∧
      B.d ρ = (3 + Real.sqrt 13) / 2 ∧ CTwists 1 B ∧ SixResidualTwists B }

/-! ### Based-ring lemmas -/

/-- For a positive duality-invariant dimension character, invertible simples have dimension one. -/
theorem PositiveDims.eq_one_of_isInvertible {F : BasedRing ι} {d : ι → ℝ}
    (hP : PositiveDims F d) {x : ι} (hx : F.IsInvertible x) : d x = 1 := by
  obtain ⟨hFP, hpos, hdual⟩ := hP
  have h := hFP.map_mul x (F.dual x)
  have hsum : ∑ l, (F.N x (F.dual x) l : ℝ) * d l = 1 := by
    rw [Fintype.sum_eq_single F.unit, hx F.unit, if_pos rfl, Nat.cast_one, one_mul,
      hFP.map_unit]
    intro l hl
    rw [hx l, if_neg hl, Nat.cast_zero, zero_mul]
  rw [hsum, hdual] at h
  have h2 : d x ^ 2 = 1 := by rw [sq]; exact h
  exact (pow_eq_one_iff_of_nonneg (hpos x).le two_ne_zero).mp h2

/-- If `g ⊗ y = y` for invertible `g, y`, then `g = 𝟙`. -/
theorem eq_unit_of_lmul_eq {F : BasedRing ι} {g y : ι} (hg : F.IsInvertible g)
    (hy : F.IsInvertible y) (h : F.lmul g y = y) : g = F.unit := by
  have h1 : F.N g y y ≠ 0 := by
    rw [hg.N_lmul, if_pos h.symm]
    exact one_ne_zero
  rw [F.frob_right, hy] at h1
  by_contra hne
  exact h1 (if_neg hne)

/-- An invertible simple outside `{𝟙, a, a*}` gives six distinct invertible-generated simples
`𝟙, a, a*, x, a x, a* x`; in rank at most six they exhaust the simples, all of dimension one. -/
theorem dims_eq_one_of_extra_invertible {F : BasedRing ι} {a : ι} {d : ι → ℝ}
    (hZ : Z3Generator F a) (hP : PositiveDims F d) (hcard : Fintype.card ι ≤ 6) {x : ι}
    (hx : F.IsInvertible x) (hxu : x ≠ F.unit) (hxa : x ≠ a) (hxb : x ≠ F.dual a) :
    Fintype.card ι = 6 ∧ ∀ i, d i = 1 := by
  obtain ⟨ha, ha1, haa⟩ := hZ
  have Z := Z3.of F ha ha1 haa
  have ua : F.unit ≠ a := Z.ua
  have ub : F.unit ≠ F.dual a := Z.ub
  have ab : a ≠ F.dual a := Z.ab
  have ux : F.unit ≠ x := fun h => hxu h.symm
  have ax : a ≠ x := fun h => hxa h.symm
  have bx : F.dual a ≠ x := fun h => hxb h.symm
  have uax : F.unit ≠ F.lmul a x := fun h => hxb (by rw [← Z.LbLa x, ← h, Z.Lbu])
  have aax : a ≠ F.lmul a x := fun h => hxu (by rw [← Z.LbLa x, ← h, Z.Lba])
  have bax : F.dual a ≠ F.lmul a x := fun h => hxa (by rw [← Z.LbLa x, ← h, Z.Lbb])
  have xax : x ≠ F.lmul a x := fun h => ha1 (eq_unit_of_lmul_eq ha hx h.symm)
  have ubx : F.unit ≠ F.lmul (F.dual a) x := fun h => hxa (by rw [← Z.LaLb x, ← h, Z.Lau])
  have abx : a ≠ F.lmul (F.dual a) x := fun h => hxb (by rw [← Z.LaLb x, ← h, Z.Laa])
  have bbx : F.dual a ≠ F.lmul (F.dual a) x := fun h => hxu (by rw [← Z.LaLb x, ← h, Z.Lab])
  have xbx : x ≠ F.lmul (F.dual a) x := fun h => Z.ub (eq_unit_of_lmul_eq Z.hb hx h.symm).symm
  have axbx : F.lmul a x ≠ F.lmul (F.dual a) x := by
    intro h
    have h' := congrArg (F.lmul (F.dual a)) h
    rw [Z.LbLa, Z.LbLb] at h'
    exact ha1 (eq_unit_of_lmul_eq ha hx h'.symm)
  have hnd : [F.unit, a, F.dual a, x, F.lmul a x, F.lmul (F.dual a) x].Nodup := by
    simp [ua, ub, ab, ux, ax, bx, uax, aax, bax, xax, ubx, abx, bbx, xbx, axbx]
  have h6 : Fintype.card ι = 6 := by
    have hle := Finset.card_le_univ
      [F.unit, a, F.dual a, x, F.lmul a x, F.lmul (F.dual a) x].toFinset
    rw [List.toFinset_card_of_nodup hnd] at hle
    simp at hle
    omega
  have huniv : [F.unit, a, F.dual a, x, F.lmul a x, F.lmul (F.dual a) x].toFinset =
      Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hnd, h6]; simp)
  have hlmul : ∀ {g : ι}, F.IsInvertible g → d (F.lmul g x) = 1 := fun hg => by
    rw [← hP.1.map_lmul hg x, hP.eq_one_of_isInvertible hg, hP.eq_one_of_isInvertible hx,
      one_mul]
  refine ⟨h6, fun i => ?_⟩
  have hi : i ∈ [F.unit, a, F.dual a, x, F.lmul a x, F.lmul (F.dual a) x].toFinset := by
    rw [huniv]
    exact Finset.mem_univ i
  have hi' : i = F.unit ∨ i = a ∨ i = F.dual a ∨ i = x ∨ i = F.lmul a x ∨
      i = F.lmul (F.dual a) x := by
    simpa using hi
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hP.1.map_unit
  · exact hP.eq_one_of_isInvertible ha
  · exact hP.eq_one_of_isInvertible ha.dual
  · exact hP.eq_one_of_isInvertible hx
  · exact hlmul ha
  · exact hlmul ha.dual

/-- `N_{(a x)(a x)} = N_{x x}` when `x a = a* x`. -/
theorem N_lmul_sq {F : BasedRing ι} {a x : ι} (ha : F.IsInvertible a)
    (hx : F.rmul x a = F.lmul (F.dual a) x) (l : ι) :
    F.N (F.lmul a x) (F.lmul a x) l = F.N x x l := by
  rw [ha.N_lmul_left, ha.N_lmul_right, hx, ha.dual.N_lmul_left, F.dual_dual,
    ha.lmul_lmul_dual]

/-- The multiplicity `m` of eq:rank6-ring is determined by the ring (and `a`): any two
presentations have the same `m`. -/
theorem mult_eq_of_isHIRing {F : BasedRing ι} {a ρ ρ₁ ρ₂ ρ' ρ₁' ρ₂' : ι} {m m' : ℕ}
    (H : IsHIRing F a ρ ρ₁ ρ₂ m) (H' : IsHIRing F a ρ' ρ₁' ρ₂' m') : m = m' := by
  have ha := H.a_inv
  have hρu : ρ ≠ F.unit := fun h => by
    have hnd := H.nodup
    rw [h] at hnd
    simp at hnd
  have hρ₁u : ρ₁ ≠ F.unit := fun h => by
    have hnd := H.nodup
    rw [h] at hnd
    simp at hnd
  have hρ₂u : ρ₂ ≠ F.unit := fun h => by
    have hnd := H.nodup
    rw [h] at hnd
    simp at hnd
  have hu' : ρ' ≠ F.unit := fun h => by
    have hnd := H'.nodup
    rw [h] at hnd
    simp at hnd
  have ha' : ρ' ≠ a := fun h => by
    have hnd := H'.nodup
    rw [h] at hnd
    simp at hnd
  have hb' : ρ' ≠ F.dual a := fun h => by
    have hnd := H'.nodup
    rw [h] at hnd
    simp at hnd
  have hm' : F.N ρ' ρ' ρ' = m' := by
    rw [H'.ρ_mul_ρ, if_neg hu', if_pos (Or.inl rfl), zero_add]
  have hm : ∀ y, y = ρ ∨ y = ρ₁ ∨ y = ρ₂ → F.N ρ ρ y = m := by
    intro y hy
    have hyu : y ≠ F.unit := by
      rcases hy with rfl | rfl | rfl <;> assumption
    rw [H.ρ_mul_ρ, if_neg hyu, if_pos hy, zero_add]
  have hl1 : F.lmul a ρ = ρ₁ := ha.lmul_eq (by rw [H.a_mul_ρ, if_pos rfl]; exact one_ne_zero)
  have hl2 : F.lmul (F.dual a) ρ = ρ₂ :=
    ha.dual.lmul_eq (by rw [H.a2_mul_ρ, if_pos rfl]; exact one_ne_zero)
  have hr : F.rmul ρ a = ρ₂ := ha.rmul_eq (by rw [H.ρ_mul_a, if_pos rfl]; exact one_ne_zero)
  have hlaa : F.lmul a a = F.dual a :=
    ha.lmul_eq (by rw [H.a_mul_a, if_pos rfl]; exact one_ne_zero)
  have sq1 : ∀ l, F.N ρ₁ ρ₁ l = F.N ρ ρ l := fun l => by
    have h := N_lmul_sq (x := ρ) ha (by rw [hr, hl2]) l
    rw [hl1] at h
    exact h
  have hr1 : F.rmul ρ₁ a = ρ :=
    ha.rmul_eq (by
      rw [← hl1, ha.N_lmul_left, hl2, H.ρ_mul_a, if_pos rfl]
      exact one_ne_zero)
  have hl3 : F.lmul (F.dual a) ρ₁ = ρ := by rw [← hl1, ha.lmul_dual_lmul]
  have hl4 : F.lmul a ρ₁ = ρ₂ := by rw [← hl1, ha.lmul_lmul ha ha.dual hlaa, hl2]
  have sq2 : ∀ l, F.N ρ₂ ρ₂ l = F.N ρ ρ l := fun l => by
    have h := N_lmul_sq (x := ρ₁) ha (by rw [hr1, hl3]) l
    rw [hl4, sq1] at h
    exact h
  have key : ∀ y, y = ρ ∨ y = ρ₁ ∨ y = ρ₂ → F.N y y y = m := by
    intro y hy
    have hsq : F.N y y y = F.N ρ ρ y := by
      rcases hy with h | h | h
      · rw [h]
      · rw [h, sq1]
      · rw [h, sq2]
    rw [hsq]
    exact hm y hy
  have hy : ρ' = ρ ∨ ρ' = ρ₁ ∨ ρ' = ρ₂ := by
    rcases H.exhaust ρ' with h | h | h | h
    · exact absurd h hu'
    · exact absurd h ha'
    · exact absurd h hb'
    · exact h
  exact (key ρ' hy).symm.trans hm'

/-! ### Analytic and arithmetic lemmas for Lemma `lem:rank6-induction` -/

theorem norm_eq_one_of_isRootOfUnity {z : ℂ} (hz : IsRootOfUnity z) : ‖z‖ = 1 := by
  obtain ⟨k, hk, hzk⟩ := hz
  have h : ‖z‖ ^ k = 1 := by rw [← norm_pow, hzk, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hk.ne').mp h

/-- The dimension `d = (3m + √(9m²+4))/2` of `ρ` is irrational (`9m² + 4` is not a square). -/
theorem irrational_of_rank6 {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hd : δ ^ 2 = 3 * m * δ + 1)
    (hpos : 0 < δ) : Irrational δ := by
  have hsq := RankSixMoments.sqrt_delta m δ hd hpos
  have hns : ¬ IsSquare (9 * m ^ 2 + 4) := by
    rintro ⟨r, hr⟩
    exact delta_not_square hm r (by rw [hr]; ring)
  have hirr : Irrational (Real.sqrt ((9 * m ^ 2 + 4 : ℕ) : ℝ)) :=
    irrational_sqrt_natCast_iff.mpr hns
  have e : ((9 * m ^ 2 + 4 : ℕ) : ℝ) = 9 * (m : ℝ) ^ 2 + 4 := by norm_num
  rw [e, hsq] at hirr
  have h2 : Irrational (((2 : ℕ) : ℝ) * δ) := by
    have e2 : ((2 : ℕ) : ℝ) * δ = ((3 * m : ℕ) : ℝ) + (2 * δ - 3 * m) := by
      push_cast
      ring
    rw [e2]
    exact hirr.natCast_add (3 * m)
  exact Irrational.of_natCast_mul 2 h2

/-- For three distinct exponents, `∑ (ζ₃^{e_j})^k = 1 + ζ₃^k + (ζ₃²)^k`. -/
theorem perm_pow_sum (e : Fin 3 → Fin 3) (h : e 0 ≠ e 1 ∧ e 0 ≠ e 2 ∧ e 1 ≠ e 2) (k : ℕ) :
    (zeta3 ^ (e 0 : ℕ)) ^ k + (zeta3 ^ (e 1 : ℕ)) ^ k + (zeta3 ^ (e 2 : ℕ)) ^ k =
      1 + zeta3 ^ k + (zeta3 ^ 2) ^ k := by
  obtain ⟨h01, h02, h12⟩ := h
  rcases perm_cases (e 0) (e 1) (e 2) h01 h02 h12 with
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;>
  · rw [h0, h1, h2]
    first
      | (simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_pow]; done)
      | (simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_pow]; ring)

/-- **The `C`-twists** (lines 3883–3897): from the Ng–Schauenburg formulas for `a`, untwistedness
`ν₃(a) = 1` and irrationality of `d`, the twists of `C₀, C₁, C₂` are `1, ζ₃, ζ₃²` once each and
`b_j = m`.  Uses `CubeRootTwists.eq_one_of_weighted_sum`, `CubeRootTwists.rank6_twists`. -/
theorem c_twists {m : ℕ} (hm : 1 ≤ m) {δ : ℝ} (hd : δ ^ 2 = 3 * m * δ + 1) (hpos : 0 < δ)
    {B : BoundaryData ι κ} (hν : B.ν₃ = 1) (I : InductionFormulas m δ B) : CTwists m B := by
  have hdC : ∀ j, 0 < 2 + 3 * (B.b j : ℝ) * δ := fun j => by
    have h0 : (0 : ℝ) ≤ 3 * (B.b j : ℝ) * δ :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hpos.le
    linarith
  have hb : (B.b 0 : ℝ) + B.b 1 + B.b 2 = 3 * m := by exact_mod_cast I.sum_b
  have hsum : ∑ j, (2 + 3 * (B.b j : ℝ) * δ) = 3 * (1 + δ ^ 2) := by
    rw [Fin.sum_univ_three]
    linear_combination 3 * δ * hb - 3 * hd
  have hw : ∑ j ∈ (Finset.univ : Finset (Fin 3)),
      ((2 + 3 * (B.b j : ℝ) * δ : ℝ) : ℂ) * B.θC j ^ 3 =
      ∑ j ∈ (Finset.univ : Finset (Fin 3)), ((2 + 3 * (B.b j : ℝ) * δ : ℝ) : ℂ) := by
    rw [I.nu3_a, hν, one_mul, ← hsum, Complex.ofReal_sum]
  have hcube := eq_one_of_weighted_sum Finset.univ (fun j => 2 + 3 * (B.b j : ℝ) * δ)
    (fun j => B.θC j ^ 3) (fun j _ => hdC j)
    (fun j _ => by
      show ‖B.θC j ^ 3‖ = 1
      rw [norm_pow, norm_eq_one_of_isRootOfUnity (I.rootC j), one_pow]) hw
  have he : ∀ j, ∃ e : Fin 3, B.θC j = zeta3 ^ (e : ℕ) := fun j =>
    eq_zeta3_pow (hcube j (Finset.mem_univ j))
  choose e he using he
  obtain ⟨hdist, hb0, hb1, hb2⟩ := rank6_twists m δ (irrational_of_rank6 hm hd hpos) (e 0) (e 1)
    (e 2) (B.b 0) (B.b 1) (B.b 2) I.sum_b (by
      have h := I.nu1_a
      rw [Fin.sum_univ_three, he 0, he 1, he 2] at h
      push_cast at h
      linear_combination h)
  refine ⟨fun j => ?_, e, hdist, he⟩
  fin_cases j <;> assumption

/-- **The residual moments** (lines 3900–3914): with the `C`-twists known, the formal codegrees
give `d_X = d²`, `d_Y = s`; the Ng–Schauenburg traces of `I(ρ)` give eq:indicator-first and
eq:indicator-second, and the center dimension identity gives `∑ n_j² = 4m² + 2`.  Uses
`FormalCodegrees.rank6_codegrees`, `RankSixMoments.indicator_moments`,
`Fusion.rank6_center_count`. -/
theorem residual_moments {m : ℕ} {δ : ℝ} (hd : δ ^ 2 = 3 * m * δ + 1) (hpos : 0 < δ)
    {B : BoundaryData ι κ} (hC : CTwists m B) (I : InductionFormulas m δ B) :
    ResidualMoments m B := by
  obtain ⟨hb, e, hdist, he⟩ := hC
  obtain ⟨-, hc2, hc3, hc4⟩ := FormalCodegrees.rank6_codegrees m δ hd hpos
  have hdX : B.dX = δ ^ 2 := by rw [I.codegree_X, hc2, hc3]
  have hdY : B.dY = 1 + δ ^ 2 := by rw [I.codegree_Y, hc4]
  have hP1 := perm_pow_sum e hdist 1
  have hP2 := perm_pow_sum e hdist 2
  simp only [pow_one] at hP1
  have hdCR : 2 + 3 * (m : ℝ) * δ = 1 + δ ^ 2 := by linarith
  have hdCC : (2 : ℂ) + 3 * (m : ℂ) * (δ : ℂ) = 1 + (δ : ℂ) ^ 2 := by exact_mod_cast hdCR
  have hZ1 : ∑ j, (B.n j : ℂ) * ((3 * (B.n j : ℝ) * δ : ℝ) : ℂ) * B.θ j =
      3 * (δ : ℂ) * ∑ j, (B.n j : ℂ) ^ 2 * B.θ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hZ2 : ∑ j, (B.n j : ℂ) * ((3 * (B.n j : ℝ) * δ : ℝ) : ℂ) * B.θ j ^ 2 =
      3 * (δ : ℂ) * ∑ j, (B.n j : ℂ) ^ 2 * B.θ j ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have t1 : (m : ℂ) * (δ : ℂ) ^ 2 + m * (1 + (δ : ℂ) ^ 2) +
      m * (1 + (δ : ℂ) ^ 2) * (1 + zeta3 + zeta3 ^ 2) +
      3 * (δ : ℂ) * ∑ j, (B.n j : ℂ) ^ 2 * B.θ j = 0 := by
    have h := I.nu1_ρ
    rw [hZ1, Fin.sum_univ_three, hb 0, hb 1, hb 2, he 0, he 1, he 2, hdX, hdY] at h
    push_cast at h
    linear_combination h - (m : ℂ) * (2 + 3 * (m : ℂ) * δ) * hP1 -
      (m : ℂ) * (1 + zeta3 + zeta3 ^ 2) * hdCC
  have t2 : (m : ℂ) * (δ : ℂ) ^ 2 + m * (1 + (δ : ℂ) ^ 2) +
      m * (1 + (δ : ℂ) ^ 2) * (1 + zeta3 ^ 2 + zeta3 ^ 4) +
      3 * (δ : ℂ) * ∑ j, (B.n j : ℂ) ^ 2 * B.θ j ^ 2 =
      3 * (1 + (δ : ℂ) ^ 2) * (((B.ε : ℝ)) : ℂ) := by
    have h := I.nu2_ρ
    rw [hZ2, Fin.sum_univ_three, hb 0, hb 1, hb 2, he 0, he 1, he 2, hdX, hdY] at h
    push_cast at h
    rw [Complex.ofReal_intCast]
    linear_combination h - (m : ℂ) * (2 + 3 * (m : ℂ) * δ) * hP2 -
      (m : ℂ) * (1 + zeta3 ^ 2 + zeta3 ^ 4) * hdCC
  obtain ⟨h1, h2⟩ := RankSixMoments.indicator_moments m δ (B.ε : ℝ) hd hpos _ _ t1 t2
  have hS : (∑ j, (B.n j : ℝ) ^ 2) = 4 * (m : ℝ) ^ 2 + 2 := by
    refine (Fusion.rank6_center_count m δ _ hd).mp ?_
    have h := I.center_dim
    rw [hdX, hdY, Fin.sum_univ_three, hb 0, hb 1, hb 2] at h
    have hZ : ∑ j, (3 * (B.n j : ℝ) * δ) ^ 2 = 9 * δ ^ 2 * ∑ j, (B.n j : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hZ] at h
    linear_combination h + 3 * ((2 + 3 * (m : ℝ) * δ) + (1 + δ ^ 2)) * hdCR
  refine ⟨I.n_pos, I.root, by exact_mod_cast hS, ?_, I.eps, ?_⟩
  · rw [h1]
    push_cast
    ring
  · rw [h2]
    push_cast
    ring

/-! ### The six arrows -/

/-- The Bischoff–Jones expansions `x` of an algebra automorphism `g` of the canonical Lagrangian
algebra `I(𝟙) = H` and `y` of `g⁻¹ = g²`, in the basis `[i]` of `End(I(𝟙)) ≅ K₀(𝓕) ⊗ ℂ`, for `g`
of order three fixing `B` (lines 3273–3296). -/
structure AutExpansion (B : BoundaryData ι κ) (x y : ι → ℝ) : Prop where
  /-- [manuscript step] `f ∗ f = f` for algebra automorphisms (lines 3283–3285), with [external]
  BJ: the primitive convolution idempotents are `d_a [a]`; so the coefficients are `0` or `d_a`. -/
  hx : ∀ i, x i = 0 ∨ x i = B.d i
  /-- The same for `g⁻¹`. -/
  hy : ∀ i, y i = 0 ∨ y i = B.d i
  /-- [external] BJ, Lemma 3.1, Cor. 3.4: composition is fusion multiplication; `g ∘ g⁻¹ = id`. -/
  hxy : ∀ l, ∑ i, ∑ j, x i * y j * (B.F.N i j l : ℝ) = if l = B.F.unit then 1 else 0
  /-- [external] The same, with `g ∘ g = g² = g⁻¹`. -/
  hxx : ∀ l, ∑ i, ∑ j, x i * x j * (B.F.N i j l : ℝ) = y l
  /-- [definitional] `g ≠ id` (the expansion of `id` is `[𝟙]`). -/
  hgid : x ≠ fun i => if i = B.F.unit then 1 else 0
  /-- [definitional] `a` is the invertible attached to `g`. -/
  hxa : x B.a ≠ 0

/-- **`L_autInvertible`** (Lemma `lem:automorphisms-invertibles`, lines 3273–3296).

* Concrete nodes: `lagrangianCenter` (positivity and duality invariance of `d` are used),
  `certDiscriminant` (opaque: it supplies the order-three automorphism `g` of
  `H = B ⊕ J ⊕ J²`, line 3231), `invertiblesContainZ3`.
* Concrete theorem: `Fusion.aut_invertible`.
* Remaining input (`hBJ`, conditional on `certDiscriminant`): the Bischoff–Jones expansions of
  `g` and `g⁻¹ = g²` (`AutExpansion`; its fields are tagged [external], [manuscript step],
  [definitional]). -/
theorem autInvertible_arrow (R : Nodes) (B : BoundaryData ι κ)
    (hBJ : (boundaryNodes R B).certDiscriminant → ∃ x y : ι → ℝ, AutExpansion B x y) :
    (boundaryNodes R B).lagrangianCenter → (boundaryNodes R B).certDiscriminant →
      (boundaryNodes R B).invertiblesContainZ3 := by
  rintro ⟨-, ⟨-, hpos, hdual⟩, -, -⟩ hdisc
  obtain ⟨x, y, ⟨hx, hy, hxy, hxx, hgid, hxa⟩⟩ := hBJ hdisc
  obtain ⟨a', ha', -, hxa', hya'⟩ := aut_invertible B.F B.d hpos hdual x y hx hy hxy
  have haa : B.a = a' := by
    by_contra hne
    exact hxa (by rw [hxa' B.a, if_neg hne])
  subst haa
  refine ⟨ha', fun h => hgid (funext fun i => by rw [hxa' i, h]), fun l => ?_⟩
  have e1 : ∑ i, ∑ j, x i * x j * (B.F.N i j l : ℝ) = (B.F.N B.a B.a l : ℝ) := by
    rw [Fintype.sum_eq_single B.a]
    · rw [Fintype.sum_eq_single B.a]
      · rw [hxa' B.a, if_pos rfl, one_mul, one_mul]
      · intro j hj
        rw [hxa' j, if_neg hj, mul_zero, zero_mul]
    · intro i hi
      rw [hxa' i, if_neg hi]
      simp
  have h := hxx l
  rw [e1, hya' l] at h
  split_ifs at h ⊢ <;> exact_mod_cast h

/-- **`L_threeInvertibles`** (lines 3309–3312: "If rank six had six invertibles, then `3s = 6` and
`d_X = s - 1 = 1`").

* Concrete nodes: `invertiblesContainZ3`, `noSignExtension` (`d_X ≠ 1`), `rankFork`
  (`rank ≤ 6`), `lagrangianCenter` (positive dimensions, `Dim 𝓕 = 3s`, `d_X = s - 1`),
  `threeInvertibles`.
* Concrete theorem: `Branching.six_invertibles_impossible`, after
  `dims_eq_one_of_extra_invertible` (an extra invertible gives six distinct invertible simples
  `𝟙, a, a*, x, ax, a*x`, which exhaust a ring of rank `≤ 6`, so `Dim 𝓕 = 6`).
* Remaining inputs: none beyond the nodes.  (The concrete `noSignExtension` records `d_X ≠ 1`;
  that "`X` not invertible" gives `d_X ≠ 1` uses that an object of Frobenius–Perron dimension one
  is invertible, which belongs to the external `L_noSign` side of the node.) -/
theorem threeInvertibles_arrow (R : Nodes) (B : BoundaryData ι κ) :
    (boundaryNodes R B).invertiblesContainZ3 → (boundaryNodes R B).noSignExtension →
      (boundaryNodes R B).rankFork → (boundaryNodes R B).lagrangianCenter →
      (boundaryNodes R B).threeInvertibles := by
  rintro hZ ⟨-, hnoSign⟩ ⟨-, hfork⟩ ⟨-, hP, hDim, hX⟩
  refine ⟨hZ, fun x hx => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hxu, hxa, hxb⟩ := hne
  have hcard : Fintype.card ι ≤ 6 := by omega
  obtain ⟨h6, hall⟩ := dims_eq_one_of_extra_invertible hZ hP hcard hx hxu hxa hxb
  have hsum : ∑ i, B.d i ^ 2 = 6 := by simp [hall, h6]
  exact Branching.six_invertibles_impossible B.s B.dX (by linarith) hX hnoSign

/-- **`L_rankSixRing`** (eq:rank6-ring, lines 3792–3826).

* Concrete nodes: `rankFork`, `notRankFour` (together: rank six), `threeInvertibles`,
  `lagrangianCenter` (the positive dimension character), `rankSixRing`.
* Concrete theorem: `Fusion.rank6_ring_of_fusionAlgebraIso` (i.e. `Fusion.rank6_ring`).
* Remaining input `hΨ`: *at rank six*, `K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` ([external] BJ, Cor. 3.4:
  the composition algebra of `End_𝒞(H)` is the complex fusion algebra; [manuscript step] with
  `H = 1 ⊕ X ⊕ 2Y`, i.e. `branchH` with `Y ≅ Y*` at rank six, `End_𝒞(H) ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)`,
  lines 3794–3800).  The isomorphism forces `card ι = 6`, so it is only assumed under that
  hypothesis; the rank six is obtained from the nodes `rankFork` and `notRankFour`. -/
theorem rankSixRing_arrow (R : Nodes) (B : BoundaryData ι κ)
    (hΨ : Fintype.card ι = 6 → FusionAlgebraIso B.F) :
    (boundaryNodes R B).rankFork → (boundaryNodes R B).notRankFour →
      (boundaryNodes R B).threeInvertibles → (boundaryNodes R B).lagrangianCenter →
      (boundaryNodes R B).branchH → (boundaryNodes R B).rankSixRing := by
  rintro ⟨-, hfork⟩ ⟨-, h4⟩ ⟨⟨ha, ha1, haa⟩, hinv⟩ ⟨-, ⟨hFP, hpos, -⟩, -, -⟩ -
  have hcard : Fintype.card ι = 6 := hfork.resolve_left h4
  exact rank6_ring_of_fusionAlgebraIso B.F hcard ha ha1 haa hinv B.d hFP hpos (hΨ hcard)

/-- **`L_rankSixMoments`** (Lemma `lem:rank6-induction`, lines 3842–3914).

* Concrete nodes: `rankSixRing` (the ring, hence `d_ρ² = 3m d_ρ + 1` by `IsHIRing.char_rho_sq`
  and `d_ρ` irrational), `untwistedPointed` (`ν₃(a) = 1`), `lagrangianCenter` (positive
  dimensions), `rankSixMoments`.
* Concrete theorems: `CubeRootTwists.eq_one_of_weighted_sum`, `CubeRootTwists.rank6_twists`,
  `FormalCodegrees.rank6_codegrees`, `RankSixMoments.indicator_moments`,
  `Fusion.rank6_center_count` (via `c_twists`, `residual_moments`).
* Remaining inputs: `hInd`, the [external] formulas (Ostrik, Ng–Schauenburg, Vafa,
  Frobenius–Schur, `Dim Z(𝓕) = (Dim 𝓕)²`) evaluated on the [manuscript step] induction
  decomposition, for the ring's `m` and `d_ρ` (`InductionFormulas`, fields tagged). -/
theorem rankSixMoments_arrow (R : Nodes) (B : BoundaryData ι κ)
    (hInd : ∀ ρ ρ₁ ρ₂ m, IsHIRing B.F B.a ρ ρ₁ ρ₂ m → InductionFormulas m (B.d ρ) B) :
    (boundaryNodes R B).rankSixRing → (boundaryNodes R B).untwistedPointed →
      (boundaryNodes R B).lagrangianCenter → (boundaryNodes R B).rankSixMoments := by
  rintro ⟨ρ, ρ₁, ρ₂, m, H⟩ ⟨-, hν⟩ ⟨-, hP, -, -⟩
  have hda : B.d B.a = 1 := hP.eq_one_of_isInvertible H.a_inv
  have hd := H.char_rho_sq hP.1 hda
  have hpos := hP.2.1 ρ
  have I := hInd ρ ρ₁ ρ₂ m H
  have hC := c_twists H.one_le hd hpos hν I
  refine ⟨ρ, ρ₁, ρ₂, m, H, ?_, hC, residual_moments hd hpos hC I⟩
  rw [RankSixMoments.sqrt_delta m _ hd hpos]
  ring

/-- **`L_multiplicityOne`** (`m = 1`, lines 3926–4004).

* Concrete nodes: `rankSixMoments`, `multiplicityOne`.
* Concrete theorem: `NumberTheory.multiplicity_eq_one_of_family_of_larson`, i.e.
  `NumberTheory.multiplicity_eq_one_of_family` (squareclass bound, the `D ≠ 10` and `D = 10`
  cases) with Lemma `lem:conductor40` supplied by `NumberTheory.conductor40Bound` and Larson's
  Theorem 1.3 by `NumberTheory.larsonRootCount`.
* Remaining inputs: none. -/
theorem multiplicityOne_arrow (R : Nodes) (B : BoundaryData ι κ) :
    (boundaryNodes R B).rankSixMoments → (boundaryNodes R B).multiplicityOne := by
  rintro ⟨ρ, ρ₁, ρ₂, m, H, -, -, M⟩
  have hm1 : m = 1 := multiplicity_eq_one_of_family_of_larson larsonRootCount H.one_le B.n B.θ
    M.root
    M.sum_sq M.first M.eps M.second
  subst hm1
  exact ⟨ρ, ρ₁, ρ₂, H⟩

/-- **`L_twelveTwists`** (Lemma `lem:six-residual-twists`, lines 4011–4060).

* Concrete nodes: `multiplicityOne` (gives `m = 1` for the ring of `rankSixMoments`, by
  `mult_eq_of_isHIRing`), `rankSixMoments`, `twelveTwists`.
* Concrete theorems: `NumberTheory.six_residual_twists_proved` (Gauss periods, linear
  independence of the nonresidue roots, doubling sends nonresidues to residues) and its
  Galois-averaging step `NumberTheory.nonresidueOrbitStep`.
* Remaining inputs: none. -/
theorem twelveTwists_arrow (R : Nodes) (B : BoundaryData ι κ) :
    (boundaryNodes R B).multiplicityOne → (boundaryNodes R B).rankSixMoments →
      (boundaryNodes R B).twelveTwists := by
  rintro ⟨ρ', ρ₁', ρ₂', H'⟩ ⟨ρ, ρ₁, ρ₂, m, H, hdρ, hC, M⟩
  obtain rfl : m = 1 := mult_eq_of_isHIRing H H'
  have hdim' : ∑ j, B.n j ^ 2 = 6 := by
    have h := M.sum_sq
    omega
  have hfirst' : ∑ j, (B.n j : ℂ) ^ 2 * B.θ j = -((1 : ℂ) + (Real.sqrt 13 : ℂ)) / 2 := by
    rw [M.first]
    norm_num
  have hsecond' : ∑ j, (B.n j : ℂ) ^ 2 * B.θ j ^ 2 =
      (-1 + (2 * (B.ε : ℂ) - 1) * (Real.sqrt 13 : ℂ)) / 2 := by
    rw [M.second]
    norm_num
  obtain ⟨hn1, hinj, hsurj, hε⟩ :=
    six_residual_twists_proved B.n M.n_pos B.θ M.root hdim' hfirst' hsecond'
  have hmem : ∀ j, ∃ e ∈ nonresidues13, B.θ j = zeta13 ^ e := by
    intro j
    have hm : B.θ j ∈ rootMultiset B.n B.θ :=
      Multiset.mem_bind.mpr ⟨j, Finset.mem_univ _,
        Multiset.mem_replicate.mpr ⟨(pow_pos (M.n_pos j) 2).ne', rfl⟩⟩
    have hsum6 : (rootMultiset B.n B.θ).sum = (-1 - (Real.sqrt 13 : ℂ)) / 2 := by
      rw [rootMultiset_sum, hfirst']
      ring
    have hcard6 : Multiset.card (rootMultiset B.n B.θ) = 6 := by
      rw [rootMultiset_card, hdim']
    exact nonresidueOrbitStep _ (rootMultiset_roots M.root) hcard6 hsum6 _ hm
  have hcardκ : Fintype.card κ = 6 := by simpa [hn1] using hdim'
  refine ⟨ρ, ρ₁, ρ₂, H, ?_, hC, ⟨hcardκ, hn1, hinj, hmem, hsurj, hε⟩⟩
  rw [hdρ]
  norm_num

/-- **The six boundary-ring arrows of the proof map are theorems** for `boundaryNodes R B`, given
the remaining inputs (Bischoff–Jones expansions and algebra identification, the evaluated
Ostrik/Ng–Schauenburg/Vafa/Frobenius–Schur formulas and the center dimension identity on the
manuscript's induction decomposition); Larson's Theorem 1.3, Lemma `lem:conductor40` and the
Galois-orbit step of Lemma `lem:six-residual-twists` are proved.  Hence, under these hypotheses, the
fields `L_autInvertible`, `L_threeInvertibles`, `L_rankSixRing`, `L_rankSixMoments`,
`L_multiplicityOne`, `L_twelveTwists` of `Inputs (boundaryNodes R B)` need not be assumed.  The
overridden nodes are disjoint from those of `ProofMapProperness.concreteNodes`, so both can be
applied together (`boundaryNodes (concreteNodes R D u) B`). -/
theorem boundary_arrows (R : Nodes) (B : BoundaryData ι κ)
    (hBJ : (boundaryNodes R B).certDiscriminant → ∃ x y : ι → ℝ, AutExpansion B x y)
    (hΨ : Fintype.card ι = 6 → FusionAlgebraIso B.F)
    (hInd : ∀ ρ ρ₁ ρ₂ m, IsHIRing B.F B.a ρ ρ₁ ρ₂ m → InductionFormulas m (B.d ρ) B) :
    let N := boundaryNodes R B
    (N.lagrangianCenter → N.certDiscriminant → N.invertiblesContainZ3) ∧
    (N.invertiblesContainZ3 → N.noSignExtension → N.rankFork → N.lagrangianCenter →
      N.threeInvertibles) ∧
    (N.rankFork → N.notRankFour → N.threeInvertibles → N.lagrangianCenter → N.branchH →
      N.rankSixRing) ∧
    (N.rankSixRing → N.untwistedPointed → N.lagrangianCenter → N.rankSixMoments) ∧
    (N.rankSixMoments → N.multiplicityOne) ∧
    (N.multiplicityOne → N.rankSixMoments → N.twelveTwists) :=
  ⟨autInvertible_arrow R B hBJ, threeInvertibles_arrow R B,
    rankSixRing_arrow R B hΨ, rankSixMoments_arrow R B hInd,
    multiplicityOne_arrow R B, twelveTwists_arrow R B⟩

#print axioms autInvertible_arrow
#print axioms threeInvertibles_arrow
#print axioms rankSixRing_arrow
#print axioms rankSixMoments_arrow
#print axioms multiplicityOne_arrow
#print axioms twelveTwists_arrow
#print axioms boundary_arrows

end HaagerupIzumi.C8.ProofMap
