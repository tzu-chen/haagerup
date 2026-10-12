module

public import HaagerupIzumi.C8.ProofMapConcreteBoundary
public import HaagerupIzumi.C8.ProofMapProperness
public import HaagerupIzumi.C8.RankFour
public import HaagerupIzumi.C8.Fusion.NearGroupRing
public import HaagerupIzumi.C8.ProofMapConcreteRankFourVoa

@[expose] public section

/-!
# The rank-four exclusion arrow of the proof map, made concrete

Section "Excluding rank four" (lines 3356–3790 of
`c8_expanded_20260929/haagerup_c8_expanded.tex`) is the arrow

* `L_notRankFour : rankFork → threeInvertibles → untwistedPointed → weightOne →
  projectiveVacuum → noSignExtension → lagrangianCenter → branchB → stronglyRational →
  initialGrades → notRankFour`.

At rank four the boundary fusion ring `K₀(𝓕)` (the `BasedRing` `B.F` of `BoundaryData`) has the
simples `𝟙, a, a*, ρ` and the near-group rule `ρ ⊗ ρ = 𝟙 + a + a* + m ρ` (`NearGroupRule`).
`rankFourNodes R B` overrides `notRankFour` of `R : Nodes` by

* `NoRankFourNearGroup B`: `K₀(𝓕)` is not a rank-four near-group ring, i.e. no simple `ρ` satisfies
  the near-group rule `ρ ⊗ ρ = 𝟙 + a + a* + m ρ` when `rank 𝓕 = 4`;

`ProofMapConcreteBoundary.boundaryNodes`, applied on top, adds `rank 𝓕 ≠ 4` as a conjunct, and
`notRankFour_arrow` proves both.

Concrete argument (`notRankFour_arrow`): at rank four the four simples are `𝟙, a, a*, ρ`
(`threeInvertibles`), the invertibles have dimension one (`PositiveDims.eq_one_of_isInvertible`), so
`Dim 𝓕 = 3 + d_ρ² = 3s` (`lagrangianCenter`); the near-group rule gives `d_ρ² = 3 + m d_ρ`
(`Fusion.nearGroup_char_sq`, applied to the positive dimension character); an invertible `ρ` cannot
satisfy the rule (`ρ ⊗ ρ` would be simple); `RankFour.rank_four_excluded` (with the case `m = 0`
proved in `RankFour.nearGroup_m0_impossible` from `d_X ≠ 1`, node `noSignExtension`) and
`dim U₁ = 6` (node `weightOne`) exclude every `m`.

Remaining inputs (`RankFourInputs`, tagged in the field docstrings): the near-group form of the
rank-four ring ([manuscript step]), Larson's theorem ([external]), and the conclusions of the case
analyses `m = 2` ([external], with `Fusion.e8_A4_invariants_ge`); for `m = 3, 6`, Proposition
`prop:near-group-current-obstructions` is proved from the VOA-side data of the even blocks
(`ProofMapConcreteRankFourVoa`: `Theta.m{3,6}_{first,reverse}_obstruction_of_voa`, with the
pole-cancellation identity proved), and those data are the inputs (tagged in
`RankFourInputs.case3`, `case6`).
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Fusion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
variable {A : VertexOperatorAlgebra k V}

/-- The near-group fusion rule `ρ ⊗ ρ = 𝟙 + a + a* + m ρ` (line 3358). -/
def NearGroupRule (F : BasedRing ι) (a ρ : ι) (m : ℕ) : Prop :=
  ∀ l, F.N ρ ρ l = (if l = F.unit then 1 else 0) + (if l = a then 1 else 0) +
    (if l = F.dual a then 1 else 0) + (if l = ρ then m else 0)

/-- `K₀(𝓕)` is not a rank-four near-group ring. -/
def NoRankFourNearGroup (B : BoundaryData ι κ) : Prop :=
  ∀ ρ m, Fintype.card ι = 4 → NearGroupRule B.F B.a ρ m → False

/-- The proof map with `notRankFour` made concrete. -/
def rankFourNodes (R : Nodes) (B : BoundaryData ι κ) : Nodes :=
  { R with notRankFour := NoRankFourNearGroup B }

/-- The remaining inputs of `L_notRankFour`, tagged; `lag`, `rat`, `init` are the opaque parts of
the nodes `lagrangianCenter`, `stronglyRational`, `initialGrades`, and `vac`, `brB` are the
concrete nodes `projectiveVacuum` (`VacuumNode`) and `branchB` (`BranchB`), on which they are
conditional, together with the concrete `ν₃(a) = 1` of `untwistedPointed`. -/
structure RankFourInputs (B : BoundaryData ι κ) (D : ClosureData A) (u : V)
    (lag rat init vac brB : Prop) : Prop where
  /-- [manuscript step] lines 3356–3358: at rank four with exactly the three invertibles
  `𝟙, a, a*` (node `threeInvertibles`), the remaining simple `ρ` is fixed by `a` and self-dual, and
  `ρ ⊗ ρ = 𝟙 + a + a* + m ρ` for some `m` (Frobenius reciprocity). -/
  rule : Fintype.card ι = 4 →
    (Z3Generator B.F B.a ∧ ∀ x, B.F.IsInvertible x → x = B.F.unit ∨ x = B.a ∨ x = B.F.dual B.a) →
    ∀ ρ, ¬ B.F.IsInvertible ρ → ∃ m, NearGroupRule B.F B.a ρ m
  /-- [external] Larson, Theorem 1.1 (pseudo-unitary near-group categories for `ℤ/3` with two
  self-dual simples; pseudo-unitarity from the Lagrangian center, node `lagrangianCenter`):
  `m ∈ {0, 2, 3, 6}`. -/
  larson : lag → Fintype.card ι = 4 → ∀ ρ m, NearGroupRule B.F B.a ρ m →
    m = 0 ∨ m = 2 ∨ m = 3 ∨ m = 6
  /-- [external] case `m = 2` (lines 3364–3480): the twisted `A₄` double, Etingof–Gelaki–Ostrik
  Theorem 7.1 / Corollary 7.4, Huang–Kirillov–Lepowsky, Dong–Mason Theorem 1 (with `c = 8`, node
  `initialGrades`, strong rationality, and the strict positivity of nonvacuum lowest weights,
  node `projectiveVacuum`, lines 3370–3372) give a holomorphic `H' ≅ V_{E₈}` with
  `U = H'^{A₄}`; the twisted double is identified with `Rep(U)` through the Lagrangian center
  `Z(𝓕) ≃ Rep(U)` (node `lagrangianCenter`, `lag`); formalized: `Fusion.e8_A4_invariants_ge`
  (`dim 𝔢₈^{A₄} ≥ 16`). -/
  case2 : lag → rat → init → vac → Fintype.card ι = 4 → ∀ ρ, NearGroupRule B.F B.a ρ 2 →
    16 ≤ Module.finrank k ↥(D.U u ⊓ A.grade 1)
  /-- Case `m = 3`, Proposition `prop:near-group-current-obstructions` (lines 3482–3770): the
  VOA-side data of one of the two orientations (`M3FirstVoa`, Table 1, or `M3ReverseVoa`,
  Table 2), for `d = dim U₁` — [external] Zhu modularity, Huang's `S` and the comparison with the
  categorical modular data (`σ` with the explicit Weil-type `S`, `T` of the table), and
  [manuscript step] the even-block reading of the characters (the weight-zero vector, its
  `η⁸`-multiplied `q`-expansion, its polar and vacuum coefficients, lines 3700–3770) and the
  choice of orientation.  The pole-cancellation identity is **proved**
  (`Theta.m3_first_obstruction_of_voa`, `Theta.m3_reverse_obstruction_of_voa`).  Uses the
  Lagrangian center `Z(𝓕) ≃ Rep(U)` (`lag`: the center carries the modular data of the near-group
  double, prop:m3-modular, around line 3451), strict positivity of nonvacuum weights (`vac`), the
  extension algebra `1 + X` and `χ₁ + χ₆₄ = χ_B` (`brB`, lines 3482, 3647) and the untwisted
  pointed part (`ν₃(a) = 1`). -/
  case3 : lag → rat → init → vac → brB → B.ν₃ = 1 → Fintype.card ι = 4 →
    ∀ ρ, NearGroupRule B.F B.a ρ 3 →
    Nonempty (M3FirstVoa (Module.finrank k ↥(D.U u ⊓ A.grade 1))) ∨
      Nonempty (M3ReverseVoa (Module.finrank k ↥(D.U u ⊓ A.grade 1)))
  /-- Case `m = 6`, Proposition `prop:near-group-current-obstructions`: the VOA-side data of one
  of the two orientations (`M6FirstVoa`, Table 3, or `M6ReverseVoa`, Table 4); tags and premises
  as for `case3`; pole cancellation proved (`Theta.m6_*_obstruction_of_voa`). -/
  case6 : lag → rat → init → vac → brB → B.ν₃ = 1 → Fintype.card ι = 4 →
    ∀ ρ, NearGroupRule B.F B.a ρ 6 →
    Nonempty (M6FirstVoa (Module.finrank k ↥(D.U u ⊓ A.grade 1))) ∨
      Nonempty (M6ReverseVoa (Module.finrank k ↥(D.U u ⊓ A.grade 1)))

/-- An invertible simple does not satisfy the near-group rule (`ρ ⊗ ρ` would be simple, but it
contains `𝟙` and `a ≠ 𝟙`). -/
theorem not_isInvertible_of_nearGroupRule {F : BasedRing ι} {a ρ : ι} {m : ℕ} (ha1 : a ≠ F.unit)
    (h : NearGroupRule F a ρ m) : ¬ F.IsInvertible ρ := by
  intro hρ
  have e1 : F.N ρ ρ F.unit ≠ 0 := by rw [h]; simp
  have e2 : F.N ρ ρ a ≠ 0 := by rw [h]; simp
  exact ha1 ((hρ.lmul_eq e2).symm.trans (hρ.lmul_eq e1))

/-- **`L_notRankFour`** (Section "Excluding rank four", lines 3356–3790).

* Concrete nodes: `threeInvertibles` (the invertibles are `𝟙, a, a*`), `weightOne`
  (`dim U₁ = 6`), `noSignExtension` (`d_X ≠ 1`), `lagrangianCenter` (positive dimensions,
  `∑ d² = 3s`, `d_X = s - 1`), `notRankFour` (`NoRankFourNearGroup`, and `rank 𝓕 ≠ 4`).
  `projectiveVacuum` (`VacuumNode`), `branchB` (`BranchB`) and `untwistedPointed` (`ν₃(a) = 1`)
  enter only through the case inputs, as do the opaque `stronglyRational`, `initialGrades`.
  The node `rankFork` is not used (the case `rank 𝓕 = 4` is the hypothesis of
  `NoRankFourNearGroup`).
* Concrete theorems: `Fusion.nearGroup_char_sq`, `PositiveDims.eq_one_of_isInvertible`,
  `RankFour.rank_four_excluded` (with `RankFour.nearGroup_m0_impossible`).
* Remaining inputs: the fields of `RankFourInputs` (tagged there). -/
theorem notRankFour_arrow (B : BoundaryData ι κ) (D : ClosureData A) (u : V)
    (lag rat init vac brB : Prop) (I : RankFourInputs B D u lag rat init vac brB) :
    (Z3Generator B.F B.a ∧ ∀ x, B.F.IsInvertible x → x = B.F.unit ∨ x = B.a ∨ x = B.F.dual B.a) →
    (D.U u ⊓ A.grade 1 = D.K ∧ Module.finrank k D.K = 6 ∧ IsSl2SumSpan A D.K) →
    B.dX ≠ 1 →
    (lag ∧ PositiveDims B.F B.d ∧ ∑ i, B.d i ^ 2 = 3 * B.s ∧ B.dX = B.s - 1) → rat → init →
    vac → brB → B.ν₃ = 1 → NoRankFourNearGroup B ∧ Fintype.card ι ≠ 4 := by
  intro h3 hw1 hX ⟨hlag, hP, hDim, hdX⟩ hrat hinit hvac hbrB hν
  obtain ⟨ha, ha1, haa⟩ := h3.1
  have Z := Z3.of B.F ha ha1 haa
  have hU1 : Module.finrank k ↥(D.U u ⊓ A.grade 1) = 6 := by rw [hw1.1]; exact hw1.2.1
  have hd1 : B.d B.F.unit = 1 := hP.1.map_unit
  have hda : B.d B.a = 1 := hP.eq_one_of_isInvertible ha
  have hdb : B.d (B.F.dual B.a) = 1 := hP.eq_one_of_isInvertible ha.dual
  have key : ∀ ρ m, Fintype.card ι = 4 → NearGroupRule B.F B.a ρ m → False := by
    intro ρ m h4 hρ
    have hninv := not_isInvertible_of_nearGroupRule ha1 hρ
    have hρu : B.F.unit ≠ ρ := fun h => hninv (h ▸ B.F.isInvertible_unit)
    have hρa : B.a ≠ ρ := fun h => hninv (h ▸ ha)
    have hρb : B.F.dual B.a ≠ ρ := fun h => hninv (h ▸ ha.dual)
    have hnd : [B.F.unit, B.a, B.F.dual B.a, ρ].Nodup := by
      simp [Z.ua, Z.ub, Z.ab, hρu, hρa, hρb]
    have huniv : [B.F.unit, B.a, B.F.dual B.a, ρ].toFinset = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hnd, h4]; simp)
    have hsum : ∑ i, B.d i ^ 2 = 3 + B.d ρ ^ 2 := by
      rw [← huniv, List.sum_toFinset _ hnd]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hd1, hda, hdb]
      ring
    have hd : B.d ρ ^ 2 = 3 + (m : ℝ) * B.d ρ := nearGroup_char_sq B.F m hρ hP.1 hda hdb
    exact RankFour.rank_four_excluded m (I.larson hlag h4 ρ m hρ) (B.d ρ) B.s B.dX hd
      (by rw [← hsum]; exact hDim) hdX hX _ hU1
      (fun h => I.case2 hlag hrat hinit hvac h4 ρ (h ▸ hρ))
      (fun h => case3_of_voa (I.case3 hlag hrat hinit hvac hbrB hν h4 ρ (h ▸ hρ)))
      (fun h => case6_of_voa (I.case6 hlag hrat hinit hvac hbrB hν h4 ρ (h ▸ hρ)))
  refine ⟨key, fun h4 => ?_⟩
  obtain ⟨ρ, hρu, hρa, hρb⟩ : ∃ ρ, ρ ≠ B.F.unit ∧ ρ ≠ B.a ∧ ρ ≠ B.F.dual B.a := by
    by_contra hcon
    push Not at hcon
    have hle : (Finset.univ : Finset ι) ⊆ {B.F.unit, B.a, B.F.dual B.a} := by
      intro x _
      by_cases hxu : x = B.F.unit
      · simp [hxu]
      · by_cases hxa : x = B.a
        · simp [hxa]
        · simp [hcon x hxu hxa]
    have h1 := Finset.card_le_card hle
    have h2 : ({B.F.unit, B.a, B.F.dual B.a} : Finset ι).card ≤ 3 := Finset.card_le_three
    rw [Finset.card_univ, h4] at h1
    omega
  have hninv : ¬ B.F.IsInvertible ρ := fun h => by
    rcases h3.2 ρ h with h | h | h
    · exact hρu h
    · exact hρa h
    · exact hρb h
  obtain ⟨m, hm⟩ := I.rule h4 h3 ρ hninv
  exact key ρ m h4 hm

#print axioms not_isInvertible_of_nearGroupRule
#print axioms notRankFour_arrow

end HaagerupIzumi.C8.ProofMap
