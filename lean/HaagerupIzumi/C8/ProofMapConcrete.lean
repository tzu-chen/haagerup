module

public import HaagerupIzumi.C8.ProofMapConcreteBoundary
public import HaagerupIzumi.C8.ProofMapConcreteCharacters
public import HaagerupIzumi.C8.ProofMapConcretePF13
public import HaagerupIzumi.C8.ProofMapConcreteRegularity
public import HaagerupIzumi.C8.ProofMapConcreteTopBound
public import HaagerupIzumi.C8.ProofMapConcreteUnitarity

@[expose] public section

/-!
# The proof map with all concrete nodes

`allConcreteNodes` composes the concrete node functions of `ProofMapProperness` (inside
`characterNodes`), `ProofMapConcreteCharacters`, `ProofMapConcreteBoundary`,
`ProofMapConcretePF13`, `ProofMapConcreteRegularity`, `ProofMapConcreteTopBound` and
`ProofMapConcreteUnitarity`.  Their overridden nodes are disjoint except `certStructural`, to which
the PF13 records and the positive stress identity are both added as conjuncts.  The twelve simple
`U`-modules are indexed by the same type `Characters.Label` in the character, top-bound and
strong-unitarity branches, and the top bound is stated for their actual lowest weights
`CharacterData.hw` (`topDataOf`).  The boundary-ring indices `ι` (simples of `𝓕`) and `κ`
(residual central simples) are not linked to `Label`.

`inputs_of_concrete` builds `Inputs (allConcreteNodes …)` from

* the 29 fields of `RemainingInputs` (the five certificate inputs, the eleven external `E_`
  arrows, and the thirteen manuscript-lemma arrows that are not made concrete), and
* the remaining inputs of the concrete arrows, bundled by branch (`BoundaryInputs`,
  `CharacterInputs`, `PF13Inputs`, the regularity inputs, `TopBoundInputs`).  Each input is tagged
  in its docstring as **[external]** (a cited theorem), **[certificate]** (lattice data),
  **[definitional]** (the meaning of a concrete parameter), **[standard]** (standard mathematics)
  or **[manuscript step]** (an argument of the manuscript that is not formalized); inputs drawn
  from a premise node of the arrow are stated conditionally on that node.

So the seventeen manuscript-lemma fields `L_gates`, `L_recursive`, `L_weightOne`, `L_proper`,
`L_pf13`, `L_positiveStress`, `L_c2`, `L_topBound`, `L_autInvertible`, `L_threeInvertibles`,
`L_rankSixRing`, `L_rankSixMoments`, `L_multiplicityOne`, `L_twelveTwists`, `L_characters`,
`L_unmixed`, `L_stronglyUnitary` are theorems.  `concrete_conclusions` reads off the concrete
meaning of the chain theorems of `ProofMap` for these nodes, and `concrete_proof_map` goes
directly from the remaining inputs to these conclusions.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Fusion HaagerupIzumi.C8.Characters MeasureTheory

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {A : VertexOperatorAlgebra k V}
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable {kp : Type*} [Field kp] {W W' : Type*} [AddCommGroup W] [Module kp W] [AddCommGroup W']
  [Module kp W']
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Sec : Type*} [Fintype Sec]

/-- The top-bound data on the twelve simple `U`-modules: their actual lowest weights `C.hw` and the
multiplicities `xT l a`, `yT l a` of the fourteen core tops in their lowest spaces. -/
def topDataOf (C : CharacterData) (xT yT : Label → ℕ → ℕ) : TopData Label := ⟨C.hw, xT, yT⟩

/-- The proof map with every concrete node of the `ProofMapProperness` and `ProofMapConcrete*`
files. -/
def allConcreteNodes (R : Nodes) (D : ClosureData A) (u : V) (C : CharacterData)
    (B : BoundaryData ι κ) (P : PF13Data kp W W') (St : StressData E H) (xT yT : Label → ℕ → ℕ)
    (recon : Sec → Label) (Unitarizable : Label → Prop) : Nodes :=
  unitarityNodes (topBoundNodes (regularityNodes (pf13Nodes (boundaryNodes
    (characterNodes R D u C) B) P) St) (topDataOf C xT yT)) recon Unitarizable

/-- The remaining inputs of the boundary-ring arrows (see `ProofMapConcreteBoundary`). -/
structure BoundaryInputs (R : Nodes) (B : BoundaryData ι κ) where
  /-- Conditional on `certDiscriminant` (the automorphism of `H/B`): the Bischoff–Jones
  expansions (`AutExpansion`, fields tagged there). -/
  hBJ : (boundaryNodes R B).certDiscriminant → ∃ x y : ι → ℝ, AutExpansion B x y
  /-- At rank six: [external] BJ Cor. 3.4 and [manuscript step] `End(1 ⊕ X ⊕ 2Y)`,
  lines 3794–3800. -/
  hΨ : Fintype.card ι = 6 → FusionAlgebraIso B.F
  /-- The evaluated formulas of Lemma `lem:rank6-induction` (`InductionFormulas`, fields tagged
  there). -/
  hInd : ∀ ρ ρ₁ ρ₂ m, IsHIRing B.F B.a ρ ρ₁ ρ₂ m → InductionFormulas m (B.d ρ) B

/-- The fields of `ProofMap.Inputs` that are **not** proved for the concrete nodes: the five
certificate inputs, the eleven external theorems, and the thirteen manuscript lemmas
`L_projectiveVacuum`, `L_rigid`, `L_rational`, `L_branchB`, `L_branchH`, `L_rankFork`,
`L_noSign`, `L_untwisted`, `L_notRankFour`, `L_netCount`, `L_reconstruction`, `L_annulus`,
`L_boundaryUnitary`. -/
structure RemainingInputs (N : Nodes) : Prop where
  C_finiteClosure : N.certFiniteClosure
  C_dimensions : N.certDimensions
  C_pct : N.certPCT
  C_structural : N.certStructural
  C_discriminant : N.certDiscriminant
  E_cklw529 : N.strongGen → N.certPCT → N.initialGrades
  L_projectiveVacuum : N.positiveStress → N.c2Cofinite → N.initialGrades → N.projectiveVacuum
  L_rigid : N.projectiveVacuum → N.c2Cofinite → N.initialGrades → N.rigidSemisimple
  L_rational : N.rigidSemisimple → N.c2Cofinite → N.initialGrades → N.stronglyRational
  L_branchB : N.stronglyRational → N.weightOne → N.certStructural → N.topBound →
    N.certDimensions → N.branchB
  L_branchH : N.branchB → N.topBound → N.certStructural → N.stronglyRational → N.branchH
  E_dmno : N.branchH → N.stronglyRational → N.projectiveVacuum → N.branchB →
    N.certDiscriminant → N.lagrangianCenter
  L_rankFork : N.lagrangianCenter → N.branchH → N.rankFork
  L_noSign : N.weightOne → N.branchB → N.stronglyRational → N.noSignExtension
  L_untwisted : N.threeInvertibles → N.certDiscriminant → N.lagrangianCenter →
    N.stronglyRational → N.untwistedPointed
  L_notRankFour : N.rankFork → N.threeInvertibles → N.untwistedPointed →
    N.weightOne → N.projectiveVacuum → N.noSignExtension → N.lagrangianCenter → N.branchB →
    N.stronglyRational → N.initialGrades → N.notRankFour
  E_gsy : N.twelveTwists → N.untwistedPointed → N.multiplicityOne → N.lagrangianCenter →
    N.modularData
  E_netCR : N.stronglyRational → N.initialGrades → N.netCompletelyRational
  L_netCount : N.netCompletelyRational → N.branchH → N.noSignExtension →
    N.rankSixRing → N.certDiscriminant → N.netCount
  L_reconstruction : N.netCompletelyRational → N.stronglyRational → N.initialGrades →
    N.reconstruction
  L_annulus : N.reconstruction → N.netCompletelyRational → N.initialGrades → N.annulus
  E_tener : N.stronglyUnitary → N.annulus → N.completelyUnitary
  L_boundaryUnitary : N.completelyUnitary → N.lagrangianCenter → N.boundaryUnitary
  E_izumi : N.boundaryUnitary → N.multiplicityOne → N.untwistedPointed → N.boundaryIsHaagerup
  E_moritaCenter : N.boundaryIsHaagerup → N.lagrangianCenter → N.completelyUnitary →
    N.repIsCenter
  E_netCenter : N.netCount → N.netRepIsCenter
  E_netExtension : N.netRepIsCenter → N.netCompletelyRational → N.netExtension
  E_diagonal : N.netCompletelyRational → N.netCount → N.reconstruction →
    N.characterVector → N.stronglyUnitary → N.diagonalTheory
  E_e8Extension : N.repIsCenter → N.projectiveVacuum → N.stronglyRational →
    N.completelyUnitary → N.e8Extension

/-- **The seventeen concrete manuscript-lemma arrows discharge their fields of `Inputs`.**  From
the 29 remaining fields and the remaining inputs of the concrete arrows (bundled by branch; the
regularity inputs are listed individually: the Haar-average data `μ, f, hf, hK, hfK, havg`
([definitional]/[standard]), the factor energy bounds `hfac` and nonnegativity `hnonneg`
([external], conditional on the concrete `pf13Factor`), and finite-dimensional grades of `U`
([definitional])), `Inputs` holds for the concrete nodes. -/
theorem inputs_of_concrete [CharZero k] [CharZero kp] (R : Nodes) (D : ClosureData A) (u : V)
    (C : CharacterData) (B : BoundaryData ι κ) (P : PF13Data kp W W') (St : StressData E H)
    (xT yT : Label → ℕ → ℕ) (recon : Sec → Label) (Unitarizable : Label → Prop)
    (RI : RemainingInputs (allConcreteNodes R D u C B P St xT yT recon Unitarizable))
    (HB : BoundaryInputs (characterNodes R D u C) B) (HC : CharacterInputs R D u C)
    (HP : PF13Inputs P)
    {G : Fin 4 → Type*} [∀ i, MeasurableSpace (G i)] (μ : ∀ i, Measure (G i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, G i → E) (hf : ∀ i, Integrable (f i) (μ i))
    (hK : ∀ i, IsCompact (St.K i)) (hfK : ∀ i g, f i g ∈ St.K i)
    (havg : ∀ i, St.avg i = ∫ g, f i g ∂(μ i))
    (hfac : (pf13Nodes (boundaryNodes (characterNodes R D u C) B) P).pf13Factor →
      ∀ i, ∃ Dc : ℝ, ∀ z ∈ St.K i, FactorEnergy St Dc z)
    (hnonneg : (pf13Nodes (boundaryNodes (characterNodes R D u C) B) P).pf13Factor →
      ∀ i, St.factorNonneg i)
    [∀ n, FiniteDimensional ℂ (St.U.grade n)]
    (HT : TopBoundInputs (regularityNodes (pf13Nodes (boundaryNodes (characterNodes R D u C) B) P)
      St) (topDataOf C xT yT)) :
    Inputs (allConcreteNodes R D u C B P St xT yT recon Unitarizable) := by
  obtain ⟨hgates, hrec, hw1, hprop⟩ := properness_arrows R D u
  obtain ⟨hchar, hunm⟩ := character_arrows R D u C HC
  obtain ⟨haut, hthree, hring, hmom, hm1, htw⟩ :=
    boundary_arrows (characterNodes R D u C) B HB.hBJ HB.hΨ HB.hInd
  have hpf := pf13_arrow (boundaryNodes (characterNodes R D u C) B) P HP
  obtain ⟨hpos, hc2⟩ := regularity_arrows (pf13Nodes (boundaryNodes (characterNodes R D u C) B) P)
    St μ f hf hK hfK havg hfac hnonneg
  have htop := topBound_arrow (regularityNodes (pf13Nodes (boundaryNodes
    (characterNodes R D u C) B) P) St) (topDataOf C xT yT) HT
  have hsu := stronglyUnitary_arrow (topBoundNodes (regularityNodes (pf13Nodes (boundaryNodes
    (characterNodes R D u C) B) P) St) (topDataOf C xT yT)) recon Unitarizable
  exact
    { C_finiteClosure := RI.C_finiteClosure
      C_dimensions := RI.C_dimensions
      C_pct := RI.C_pct
      C_structural := RI.C_structural
      C_discriminant := RI.C_discriminant
      L_gates := hgates
      L_recursive := hrec
      L_weightOne := hw1
      L_proper := hprop
      E_cklw529 := RI.E_cklw529
      L_pf13 := fun h => hpf h.1
      L_positiveStress := hpos
      L_c2 := hc2
      L_projectiveVacuum := RI.L_projectiveVacuum
      L_rigid := RI.L_rigid
      L_rational := RI.L_rational
      L_topBound := htop
      L_branchB := RI.L_branchB
      L_branchH := RI.L_branchH
      E_dmno := RI.E_dmno
      L_rankFork := RI.L_rankFork
      L_autInvertible := haut
      L_noSign := RI.L_noSign
      L_threeInvertibles := hthree
      L_untwisted := RI.L_untwisted
      L_notRankFour := RI.L_notRankFour
      L_rankSixRing := hring
      L_rankSixMoments := hmom
      L_multiplicityOne := hm1
      L_twelveTwists := htw
      E_gsy := RI.E_gsy
      L_characters := fun hm => hchar hm.1
      L_unmixed := hunm
      E_netCR := RI.E_netCR
      L_netCount := RI.L_netCount
      L_reconstruction := RI.L_reconstruction
      L_stronglyUnitary := hsu
      L_annulus := RI.L_annulus
      E_tener := RI.E_tener
      L_boundaryUnitary := RI.L_boundaryUnitary
      E_izumi := RI.E_izumi
      E_moritaCenter := RI.E_moritaCenter
      E_netCenter := RI.E_netCenter
      E_netExtension := RI.E_netExtension
      E_diagonal := RI.E_diagonal
      E_e8Extension := RI.E_e8Extension }

omit [FiniteDimensional ℝ E] in
/-- **The concrete meaning of the main results.**  For the concrete nodes, the chain theorems of
`ProofMap` give: the boundary fusion ring `K₀(𝓕)` is `HI(ℤ/3)` (eq:rank6-ring with `m = 1`); the
twelve-simple twist list of line 4053; the character vector is the `γ = 0` Evans–Gannon vector,
coefficient by coefficient; the lowest weights and top dimensions of the table at line 4178; the
universal top bound `0 ≤ h ≤ 17/10` for the actual lowest weights; every simple `U`-module is
unitarizable; `U₁ = K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂`, `dim K = 6`, `U ⊊ B`; `U` is `C₂`-cofinite; and the embedded
parafermion factor is `K(𝔰𝔩₂, 13)`. -/
theorem concrete_conclusions (R : Nodes) (D : ClosureData A) (u : V)
    (C : CharacterData) (B : BoundaryData ι κ) (P : PF13Data kp W W') (St : StressData E H)
    (xT yT : Label → ℕ → ℕ) (recon : Sec → Label) (Unitarizable : Label → Prop)
    (hI : Inputs (allConcreteNodes R D u C B P St xT yT recon Unitarizable)) :
    (∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1) ∧
    (∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1 ∧ B.d ρ = (3 + Real.sqrt 13) / 2 ∧ CTwists 1 B ∧
      SixResidualTwists B) ∧
    (C.F = C.Ξ₀ ∧ ∀ l n, (C.a l n : ℂ) = C.e₀ l n) ∧
    (∀ l, C.hw l = lowestWeight l ∧ C.td l = topDim l) ∧
    (∀ l, 0 ≤ C.hw l ∧ C.hw l ≤ 17 / 10) ∧
    (∀ l, Unitarizable l) ∧
    (D.U u ⊓ A.grade 1 = D.K ∧ Module.finrank k D.K = 6 ∧ IsSl2SumSpan A D.K) ∧ D.U u ≠ ⊤ ∧
    FiniteDimensional ℂ (H ⧸ C2 St.U) ∧
    (∃ φ : W ≃ₗ[kp] W', φ P.L = P.L' ∧ φ P.a = P.a' ∧ φ P.b = P.b' ∧ φ P.d = P.d' ∧
      φ P.A.vac = P.A'.vac ∧ ∀ (n : ℤ) (x y : W), φ (P.A.mode n x y) = P.A'.mode n (φ x) (φ y)) := by
  obtain ⟨hm1, htw, hmd, -, -, -, htop, -, -, -⟩ := boundary_chain hI
  obtain ⟨-, -, hsu, -, -, -, -⟩ := thm_main_net hI
  obtain ⟨-, hw1, hprop⟩ := prop_mainproper hI
  have hinit := initialGrades_of hI
  have hchar := hI.L_characters hmd hw1 (projectiveVacuum_of hI) hinit (stronglyRational_of hI)
  have hpf := hI.L_pf13 hI.C_structural
  have hc2 := hI.L_c2 (hI.L_positiveStress hI.C_structural hpf) hinit
  exact ⟨hm1, htw, hchar.1, hchar.2, htop, hsu, hw1, hprop, hc2, hpf⟩

/-- **From the remaining inputs to the concrete conclusions** (`inputs_of_concrete` followed by
`concrete_conclusions`): the seventeen proved arrows are used in this derivation. -/
theorem concrete_proof_map [CharZero k] [CharZero kp] (R : Nodes) (D : ClosureData A) (u : V)
    (C : CharacterData) (B : BoundaryData ι κ) (P : PF13Data kp W W') (St : StressData E H)
    (xT yT : Label → ℕ → ℕ) (recon : Sec → Label) (Unitarizable : Label → Prop)
    (RI : RemainingInputs (allConcreteNodes R D u C B P St xT yT recon Unitarizable))
    (HB : BoundaryInputs (characterNodes R D u C) B) (HC : CharacterInputs R D u C)
    (HP : PF13Inputs P)
    {G : Fin 4 → Type*} [∀ i, MeasurableSpace (G i)] (μ : ∀ i, Measure (G i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, G i → E) (hf : ∀ i, Integrable (f i) (μ i))
    (hK : ∀ i, IsCompact (St.K i)) (hfK : ∀ i g, f i g ∈ St.K i)
    (havg : ∀ i, St.avg i = ∫ g, f i g ∂(μ i))
    (hfac : (pf13Nodes (boundaryNodes (characterNodes R D u C) B) P).pf13Factor →
      ∀ i, ∃ Dc : ℝ, ∀ z ∈ St.K i, FactorEnergy St Dc z)
    (hnonneg : (pf13Nodes (boundaryNodes (characterNodes R D u C) B) P).pf13Factor →
      ∀ i, St.factorNonneg i)
    [∀ n, FiniteDimensional ℂ (St.U.grade n)]
    (HT : TopBoundInputs (regularityNodes (pf13Nodes (boundaryNodes (characterNodes R D u C) B) P)
      St) (topDataOf C xT yT)) :
    (∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1) ∧
    (∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1 ∧ B.d ρ = (3 + Real.sqrt 13) / 2 ∧ CTwists 1 B ∧
      SixResidualTwists B) ∧
    (C.F = C.Ξ₀ ∧ ∀ l n, (C.a l n : ℂ) = C.e₀ l n) ∧
    (∀ l, C.hw l = lowestWeight l ∧ C.td l = topDim l) ∧
    (∀ l, 0 ≤ C.hw l ∧ C.hw l ≤ 17 / 10) ∧
    (∀ l, Unitarizable l) ∧
    (D.U u ⊓ A.grade 1 = D.K ∧ Module.finrank k D.K = 6 ∧ IsSl2SumSpan A D.K) ∧ D.U u ≠ ⊤ ∧
    FiniteDimensional ℂ (H ⧸ C2 St.U) ∧
    (∃ φ : W ≃ₗ[kp] W', φ P.L = P.L' ∧ φ P.a = P.a' ∧ φ P.b = P.b' ∧ φ P.d = P.d' ∧
      φ P.A.vac = P.A'.vac ∧ ∀ (n : ℤ) (x y : W), φ (P.A.mode n x y) = P.A'.mode n (φ x) (φ y)) :=
  concrete_conclusions R D u C B P St xT yT recon Unitarizable
    (inputs_of_concrete R D u C B P St xT yT recon Unitarizable RI HB HC HP μ f hf hK hfK havg hfac
      hnonneg HT)

#print axioms inputs_of_concrete
#print axioms concrete_conclusions
#print axioms concrete_proof_map

end HaagerupIzumi.C8.ProofMap
