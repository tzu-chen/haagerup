module

public import HaagerupIzumi.C8.ProofMapConcreteBoundary
public import HaagerupIzumi.C8.ProofMapConcreteBranching
public import HaagerupIzumi.C8.ProofMapConcreteBranchH
public import HaagerupIzumi.C8.ProofMapConcreteCharacters
public import HaagerupIzumi.C8.ProofMapConcreteNetCount
public import HaagerupIzumi.C8.ProofMapConcretePF13
public import HaagerupIzumi.C8.ProofMapConcreteRankFour
public import HaagerupIzumi.C8.ProofMapConcreteRigid
public import HaagerupIzumi.C8.ProofMapConcreteRegularity
public import HaagerupIzumi.C8.ProofMapConcreteTopBound
public import HaagerupIzumi.C8.ProofMapConcreteUnitarity
public import HaagerupIzumi.C8.ProofMapConcreteUntwisted
public import HaagerupIzumi.C8.ProofMapConcreteVacuum
public import HaagerupIzumi.C8.ProofMapSimples
public import HaagerupIzumi.C8.Fusion.EndHSchur

@[expose] public section

/-!
# The proof map with all concrete nodes

`allConcreteNodes` composes the concrete node functions of `ProofMapConcreteVacuum`,
`ProofMapProperness` (inside `characterNodes`), `ProofMapConcreteCharacters`,
`ProofMapConcreteRigid` (together with the vacuum layer: `regNodes`), `ProofMapConcreteBranching`
(which also sets the node `branchH`; `ProofMapConcreteBranchH` has no node function of its own and
proves the arrow `L_branchH` into it), `ProofMapConcreteRankFour`, `ProofMapConcreteNetCount`,
`ProofMapConcreteUntwisted` (together: `coreNodes`),
`ProofMapConcreteBoundary`,
`ProofMapConcretePF13`, `ProofMapConcreteRegularity`, `ProofMapConcreteTopBound` and
`ProofMapConcreteUnitarity`.  Their overridden nodes are disjoint except `certStructural`, to which
the irreducibility of the eighty currents, the PF13 records and the positive stress identity are
added as conjuncts; `notRankFour`, to which `boundaryNodes` adds `rank 𝓕 ≠ 4` on top of
`NoRankFourNearGroup`; `rankFork`, `noSignExtension`, to which `boundaryNodes`
adds `rank 𝓕 ∈ {4, 6}` and `d_X ≠ 1` as conjuncts on top of the branching statements;
`netCount`, to which `unitarityNodes` adds `#Sec = 12` on top of `NetHI`; and `untwistedPointed`,
to which `boundaryNodes` adds `ν₃(a) = 1` on top of `UntwistedNode`.  The
projective-vacuum node is stated for the vertex operator algebra `St.U` of the regularity branch
(the same object as in `positiveStress`, `c2Cofinite`); the rigidity node for a monoidal category
`𝒞` standing for `Rep(U)` (linked to `St.U` only through the definitional input `hunit`); the same
`ℂ`-linear category `𝒞` carries the objects `H, X, Y` of the rank-six algebra identification
(`BoundaryInputs`).

**The simple `U`-modules.**  The top-bound, branching, projective-vacuum and strong-unitarity
branches are stated for an arbitrary finite type `Simp` of isomorphism classes of simple
`U`-modules (`SD : SimpleData Simp`: lowest weights `SD.hw`, top dimensions `SD.td`, the class
`SD.vac` of `U`), as in the manuscript, which learns how many simples there are only from the
modular data (GSY Theorem A(2), node `modularData`, line 4053).  The identification with the
twelve labels `Characters.Label` of the character table is one input, `LI : SimpleLabels
R.modularData SD C` ([manuscript step], conditional on `modularData`), used only where
label-specific facts are needed: the character arrow (no weight-zero vectors in `b, a, c₀`,
`noWeightZero_of_vacuum`) and the strong-unitarity count (`card Simp = 12`, `SimpleLabels.card`,
a consequence of the identification rather than true by construction).  The character branch
itself (`CharacterData`, characters and lowest weights `C.hw` of the labelled modules) is indexed
by `Label`.  The boundary-ring indices `ι` (simples of `𝓕`) and `κ` (residual central simples)
are not linked to
`Label`; `ι` is the index type whose cardinality is `rank 𝓕` in the rank fork.  The net boundary
data `Bn` (for `𝓕_net`) is a second `BoundaryData`, not linked to `B`; the net sectors `Sec` are
those of the strong-unitarity branch.  The untwisted node is stated for a linear monoidal category
`Cr` standing for `Rep(B)`, its nine invertibles `Sv` and the algebra `Ah = H/B`.

`inputs_of_concrete` builds `Inputs (allConcreteNodes …)` from

* the 20 fields of `RemainingInputs` (the five certificate inputs, the eleven external `E_`
  arrows, and the four manuscript-lemma arrows that are not made concrete), and
* the remaining inputs of the concrete arrows, bundled by branch (`BoundaryInputs`, with the
  Bischoff–Jones identification `bj`, the decomposition `dec` and the Schur data of `𝟙, X, Y`
  from which `hΨ` is built; `CharacterInputs`, `PF13Inputs`, `BranchBInputs`, `SignInputs` with
  `hadj`, `hfp`, `VacuumInputs` (one regularity input `reg` for the component algebras, finite
  length `noNeg`, `labels`), the identification `LI` of the simples with the twelve labels,
  `RankFourInputs`, the sector data `S₁, S₂` of `J, J²` with `SectorInputs` and `BranchHInputs`,
  the rigidity inputs `hunit`, `hEP`, `NetInputs`,
  `UntwistedInputs` with `hν`, the regularity inputs, `TopBoundInputs`).
  Each input is tagged
  in its docstring as **[external]** (a cited theorem), **[certificate]** (lattice data),
  **[definitional]** (the meaning of a concrete parameter), **[standard]** (standard mathematics)
  or **[manuscript step]** (an argument of the manuscript that is not formalized); inputs drawn
  from a premise node of the arrow are stated conditionally on that node.

So the twenty-six manuscript-lemma fields `L_gates`, `L_recursive`, `L_weightOne`, `L_proper`,
`L_pf13`, `L_positiveStress`, `L_c2`, `L_projectiveVacuum`, `L_rigid`, `L_topBound`, `L_branchB`,
`L_branchH`, `L_rankFork`, `L_noSign`, `L_untwisted`, `L_notRankFour`, `L_netCount`,
`L_autInvertible`, `L_threeInvertibles`, `L_rankSixRing`, `L_rankSixMoments`,
`L_multiplicityOne`, `L_twelveTwists`, `L_characters`, `L_unmixed`, `L_stronglyUnitary` are
theorems.  `concrete_conclusions` reads off the concrete
meaning of the chain theorems of `ProofMap` for these nodes, and `concrete_proof_map` goes
directly from the remaining inputs to these conclusions.
-/

namespace HaagerupIzumi.C8.ProofMap

open HaagerupIzumi.C8 HaagerupIzumi.C8.Fusion HaagerupIzumi.C8.Characters MeasureTheory
open CategoryTheory MonoidalCategory Limits

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
  {A : VertexOperatorAlgebra k V}
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable {kp : Type*} [Field kp] {W W' : Type*} [AddCommGroup W] [Module kp W] [AddCommGroup W']
  [Module kp W']
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Sec : Type*} [Fintype Sec]
variable {σ : Type*}
variable {Simp : Type*} [Fintype Simp] [DecidableEq Simp]
variable {ιn κn : Type*} [Fintype ιn] [DecidableEq ιn] [Fintype κn]
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
  {τ₁ τ₂ : Type*} [Fintype τ₁] [Fintype τ₂]

/-- The top-bound data on the simple `U`-modules: their lowest weights `SD.hw` and the
multiplicities `xT s a`, `yT s a` of the fourteen core tops in their lowest spaces. -/
def topDataOf (SD : SimpleData Simp) (xT yT : Simp → ℕ → ℕ) : TopData Simp := ⟨SD.hw, xT, yT⟩

/-- The innermost layers: the projective vacuum (`vacuumNodes`) and rigidity (`rigidNodes`). -/
def regNodes (R : Nodes) (SD : SimpleData Simp) (St : StressData E H) (𝒞 : Type*) [Category 𝒞]
    [MonoidalCategory 𝒞] : Nodes :=
  rigidNodes (vacuumNodes R St SD) 𝒞

/-- The inner layers: `regNodes`, the properness and character nodes (`characterNodes`), the
branching nodes (`branchingNodes`), the rank-four exclusion (`rankFourNodes`), the net sector
count (`netNodes`), then the untwisted pointed part (`untwistedNodes`). -/
def coreNodes (R : Nodes) (D : ClosureData A) (u : V) (C : CharacterData) (SD : SimpleData Simp)
    (St : StressData E H) (𝒞 : Type*) [Category 𝒞] [MonoidalCategory 𝒞]
    (Bb : BranchBData A σ Simp) (Hd : BranchHData Simp)
    (Sg : SignData A) (B : BoundaryData ι κ) (Bn : BoundaryData ιn κn) (Cr : Type*) [Category Cr] [MonoidalCategory Cr] [BraidedCategory Cr] [Preadditive Cr]
    [HasFiniteBiproducts Cr] [HasCoequalizers Cr]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive Cr]
    (𝕜 : Type) [Field 𝕜] [Linear 𝕜 Cr] [MonoidalLinear 𝕜 Cr] (Ah : Mon Cr) [IsCommMonObj Ah.X]
    (Sv : ZMod 3 × ZMod 3 → Cr) : Nodes :=
  untwistedNodes (netNodes (rankFourNodes (branchingNodes
    (characterNodes (regNodes R SD St 𝒞) D u C) D u SD Bb Hd Sg ι) B) Bn) 𝕜 Cr Ah Sv

/-- The proof map with every concrete node of the `ProofMapProperness` and `ProofMapConcrete*`
files. -/
def allConcreteNodes (R : Nodes) (D : ClosureData A) (u : V) (C : CharacterData)
    (SD : SimpleData Simp) (𝒞 : Type*) [Category 𝒞] [MonoidalCategory 𝒞]
    (Bb : BranchBData A σ Simp) (Hd : BranchHData Simp)
    (Sg : SignData A) (B : BoundaryData ι κ) (Bn : BoundaryData ιn κn) (Cr : Type*) [Category Cr] [MonoidalCategory Cr] [BraidedCategory Cr] [Preadditive Cr]
    [HasFiniteBiproducts Cr] [HasCoequalizers Cr]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive Cr]
    (𝕜 : Type) [Field 𝕜] [Linear 𝕜 Cr] [MonoidalLinear 𝕜 Cr] (Ah : Mon Cr) [IsCommMonObj Ah.X]
    (Sv : ZMod 3 × ZMod 3 → Cr) (P : PF13Data kp W W') (St : StressData E H)
    (xT yT : Simp → ℕ → ℕ) (recon : Sec → Simp) (Unitarizable : Simp → Prop) : Nodes :=
  unitarityNodes (topBoundNodes (regularityNodes (pf13Nodes (boundaryNodes
    (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B) P) St) (topDataOf SD xT yT)) recon
    Unitarizable

/-- The remaining inputs of the boundary-ring arrows (see `ProofMapConcreteBoundary`), with the
objects `H`, `X`, `Y` of the `ℂ`-linear category `𝒞 = Rep(U)` (the category of the rigidity
branch) used for the rank-six algebra identification. -/
structure BoundaryInputs (R : Nodes) (B : BoundaryData ι κ) (𝒞 : Type*) [Category 𝒞]
    [MonoidalCategory 𝒞] [Preadditive 𝒞] [Linear ℂ 𝒞] [HasBinaryBiproducts 𝒞] where
  /-- Conditional on `certDiscriminant` (the automorphism of `H/B`): the Bischoff–Jones
  expansions (`AutExpansion`, fields tagged there). -/
  hBJ : (boundaryNodes R B).certDiscriminant → ∃ x y : ι → ℝ, AutExpansion B x y
  /-- The extension algebra `H` of `U`, as an object of `𝒞`. -/
  H : 𝒞
  /-- The summand `X` of `B↓U = U ⊕ X`. -/
  X : 𝒞
  /-- The summand `Y` of `H↓U` (the restriction of `J`). -/
  Y : 𝒞
  /-- [manuscript step] `𝟙 = U`, `X`, `Y` are simple `U`-modules (eq:B-branching,
  eq:H-branching-fork, lines 3219, 3233). -/
  simple1 : Simple (𝟙_ 𝒞)
  simpleX : Simple X
  simpleY : Simple Y
  /-- [manuscript step] `𝟙, X, Y` are pairwise non-isomorphic: they are distinguished by their
  lowest spaces (line 3237; lowest weights `0, 1, 1`, top dimensions `1, 80, 81`). -/
  ne1X : (𝟙_ 𝒞 ≅ X) → False
  ne1Y : (𝟙_ 𝒞 ≅ Y) → False
  neXY : (X ≅ Y) → False
  /-- [external] Bischoff–Jones Corollary 3.4 (with Lemma 3.1), at rank six: the composition
  algebra `End_𝒞(H)` of the canonical Lagrangian algebra `H = I(𝟙)` is the complexified fusion
  algebra `K₀(𝓕) ⊗ ℂ` (`Fusion.BJIso`). -/
  bj : Fintype.card ι = 6 → Fusion.BJIso B.F H
  /-- [manuscript step] at rank six (`Y ≅ Y*`), `H↓U = 𝟙 ⊕ X ⊕ 2Y` (eq:rank-fork and
  lines 3795–3800). -/
  dec : Fintype.card ι = 6 → (H ≅ 𝟙_ 𝒞 ⊞ (X ⊞ (Y ⊞ Y)))
  /-- The evaluated formulas of Lemma `lem:rank6-induction` (`InductionFormulas`, fields tagged
  there). -/
  hInd : ∀ ρ ρ₁ ρ₂ m, IsHIRing B.F B.a ρ ρ₁ ρ₂ m → InductionFormulas m (B.d ρ) B

/-- **`hΨ` of `rankSixRing_arrow` from the boundary inputs**: `K₀(𝓕) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` at rank
six, from the Bischoff–Jones identification, the decomposition `H ≅ 𝟙 ⊞ (X ⊞ (Y ⊞ Y))` and
Schur's lemma (`Fusion.fusionAlgebraIsoOfSimple`; the manuscript step
`End(1 ⊕ X ⊕ 2Y) ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` is `Fusion.endHIsoOfSimple`). -/
noncomputable def BoundaryInputs.hΨ {R : Nodes} {B : BoundaryData ι κ} {𝒞 : Type*} [Category 𝒞]
    [MonoidalCategory 𝒞] [Preadditive 𝒞] [Linear ℂ 𝒞] [HasBinaryBiproducts 𝒞] [HasKernels 𝒞]
    [∀ X Y : 𝒞, FiniteDimensional ℂ (X ⟶ Y)] (HB : BoundaryInputs R B 𝒞) :
    Fintype.card ι = 6 → FusionAlgebraIso B.F := fun h6 =>
  haveI := HB.simple1
  haveI := HB.simpleX
  haveI := HB.simpleY
  fusionAlgebraIsoOfSimple B.F (𝟙_ 𝒞) HB.X HB.Y (HB.bj h6) (HB.dec h6) HB.ne1X HB.ne1Y HB.neXY

/-- The fields of `ProofMap.Inputs` that are **not** proved for the concrete nodes: the five
certificate inputs, the eleven external theorems, and the four manuscript lemmas
`L_rational`, `L_reconstruction`, `L_annulus`, `L_boundaryUnitary`. -/
structure RemainingInputs (N : Nodes) : Prop where
  C_finiteClosure : N.certFiniteClosure
  C_dimensions : N.certDimensions
  C_pct : N.certPCT
  C_structural : N.certStructural
  C_discriminant : N.certDiscriminant
  E_cklw529 : N.strongGen → N.certPCT → N.initialGrades
  L_rational : N.rigidSemisimple → N.c2Cofinite → N.initialGrades → N.stronglyRational
  E_dmno : N.branchH → N.stronglyRational → N.projectiveVacuum → N.branchB →
    N.certDiscriminant → N.lagrangianCenter
  E_gsy : N.twelveTwists → N.untwistedPointed → N.multiplicityOne → N.lagrangianCenter →
    N.modularData
  E_netCR : N.stronglyRational → N.initialGrades → N.netCompletelyRational
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

/-- **The twenty-six concrete manuscript-lemma arrows discharge their fields of `Inputs`.**  From
the 20 remaining fields and the remaining inputs of the concrete arrows (bundled by branch; the
branching inputs are `BranchBInputs`, `SignInputs`, the adjunction `hadj` ([external], conditional
on `lagrangianCenter`) and `hfp` ([standard], conditional on `stronglyRational`); the
projective-vacuum inputs are `VacuumInputs` (`reg` conditional on `factorNonneg`, `noNeg` on
`c2Cofinite`, `labels` on `initialGrades`); the character inputs `CharacterInputs` include the
definitional `below`, whose consequence `a l 0 = 0` for `b, a, c₀` is the premise `hpos` of the
character arrow (`noWeightZero_of_vacuum`, from the concrete `VacuumNode` and `LI`); the
rank-four inputs are `RankFourInputs`, conditional on the opaque `lagrangianCenter`,
`stronglyRational`, `initialGrades` and on the concrete `VacuumNode`, `BranchB`, `ν₃(a) = 1`;
the `H`-branching inputs are the sector data `S₁, S₂` with `SectorInputs` (certificates
conditional on the opaque `certStructural`, complete reducibility on `stronglyRational`) and
`BranchHInputs`; `BranchBInputs` has its complete-reducibility fields conditional on
`stronglyRational`; the
rigidity inputs are `hunit` ([definitional]) and `hEP` ([external] McRae, Etingof–Penneys,
conditional on `c2Cofinite` and the opaque `initialGrades`); the net-count inputs are `NetInputs`
for the net boundary data `Bn`, conditional on the opaque `netCompletelyRational`,
`certDiscriminant`, the concrete algebraic `rankSixRing` and the proved free-induction
equivalence (`untwistedNode_of_inputs`); the untwisted-pointed inputs are `UntwistedInputs` (on
`Rep(B)` and `H/B`, conditional on the opaque `certDiscriminant`, with the instance hypotheses
`Rep(B)` braided, coequalizers preserved, `H/B` commutative) and `hν` ([manuscript
step]/[standard] tensor embedding into `𝓕` and Frobenius–Schur indicator, conditional on
`lagrangianCenter`, `stronglyRational`; it supplies `ν₃(a) = 1`, the `𝓕`-side content); the
boundary inputs `BoundaryInputs` include the [external] Bischoff–Jones identification and the
[manuscript step] decomposition `H ≅ 𝟙 ⊞ (X ⊞ (Y ⊞ Y))` at rank six, from which `hΨ` is built
by `Fusion.fusionAlgebraIsoOfSimple`; the identification `LI` of the simples with the twelve
labels ([manuscript step], conditional on `modularData`) gives the label-specific input of the
character arrow (`noWeightZero_of_vacuum`) and the count of twelve simples for strong unitarity;
the regularity inputs are listed individually: the Haar-average data `μ, f, hf, hK, hfK, havg`
([definitional]/[standard]), the factor energy bounds `hfac` and nonnegativity `hnonneg`
([external], conditional on the concrete `pf13Factor`), and finite-dimensional grades of `U`
([definitional])), `Inputs` holds for the concrete nodes. -/
theorem inputs_of_concrete [CharZero k] [CharZero kp] [Fintype σ] [DecidableEq σ]
    (R : Nodes) (D : ClosureData A) (u : V)
    (C : CharacterData) (SD : SimpleData Simp) (𝒞 : Type*) [Category 𝒞] [MonoidalCategory 𝒞]
    [Preadditive 𝒞] [Linear ℂ 𝒞] [HasBinaryBiproducts 𝒞] [HasKernels 𝒞]
    [∀ X Y : 𝒞, FiniteDimensional ℂ (X ⟶ Y)] (Bb : BranchBData A σ Simp)
    (Hd : BranchHData Simp) (Sg : SignData A) (B : BoundaryData ι κ) (Bn : BoundaryData ιn κn)
    (Cr : Type*) [Category Cr] [MonoidalCategory Cr] [BraidedCategory Cr] [Preadditive Cr]
    [HasFiniteBiproducts Cr] [HasCoequalizers Cr]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive Cr]
    (𝕜 : Type) [Field 𝕜] [Linear 𝕜 Cr] [MonoidalLinear 𝕜 Cr] (Ah : Mon Cr) [IsCommMonObj Ah.X] (Sv : ZMod 3 × ZMod 3 → Cr) (P : PF13Data kp W W')
    (St : StressData E H)
    (xT yT : Simp → ℕ → ℕ) (recon : Sec → Simp) (Unitarizable : Simp → Prop)
    (RI : RemainingInputs
      (allConcreteNodes R D u C SD 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv P St xT yT recon Unitarizable))
    (HB : BoundaryInputs (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B 𝒞)
    (HC : CharacterInputs (regNodes R SD St 𝒞) D u C) (LI : SimpleLabels R.modularData SD C)
    (HP : PF13Inputs P) (HBr : BranchBInputs SD D u Bb R.stronglyRational)
    (HS : SignInputs SD D u Bb Sg)
    (hadj : R.lagrangianCenter → Fintype.card ι = ∑ l, Hd.mult l ^ 2)
    (hfp : R.stronglyRational → B.dX = 1 → Sg.XInvertible) (HV : VacuumInputs St SD R.initialGrades)
    (HR : RankFourInputs B D u R.lagrangianCenter R.stronglyRational R.initialGrades
      (VacuumNode St SD) (BranchB SD D u Bb))
    (S₁ : SectorData A M₁ τ₁ Simp) (S₂ : SectorData A M₂ τ₂ Simp)
    (I₁ : SectorInputs SD D u S₁ R.certStructural R.stronglyRational)
    (I₂ : SectorInputs SD D u S₂ R.certStructural R.stronglyRational)
    (IH : BranchHInputs SD Bb Hd S₁ S₂)
    (hunit : VacuumNode St SD → Projective (𝟙_ 𝒞))
    (hEP : FiniteDimensional ℂ (H ⧸ C2 St.U) → R.initialGrades → Projective (𝟙_ 𝒞) →
      ∀ X : 𝒞, Nonempty (HasRightDual X))
    (HN : NetInputs D u Sg Bn Sec R.netCompletelyRational R.certDiscriminant
      (∃ ρ ρ₁ ρ₂ m, IsHIRing B.F B.a ρ ρ₁ ρ₂ m) (UntwistedNode 𝕜 Cr Ah Sv))
    [∀ X Y : Cr, FiniteDimensional 𝕜 (X ⟶ Y)] (HU : UntwistedInputs 𝕜 Cr Ah Sv R.certDiscriminant)
    (hν : UntwistedNode 𝕜 Cr Ah Sv → R.certDiscriminant → R.lagrangianCenter → R.stronglyRational →
      (Z3Generator B.F B.a ∧ ∀ x, B.F.IsInvertible x → x = B.F.unit ∨ x = B.a ∨ x = B.F.dual B.a) →
      B.ν₃ = 1)
    {G : Fin 4 → Type*} [∀ i, MeasurableSpace (G i)] (μ : ∀ i, Measure (G i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, G i → E) (hf : ∀ i, Integrable (f i) (μ i))
    (hK : ∀ i, IsCompact (St.K i)) (hfK : ∀ i g, f i g ∈ St.K i)
    (havg : ∀ i, St.avg i = ∫ g, f i g ∂(μ i))
    (hfac : (pf13Nodes (boundaryNodes (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B)
      P).pf13Factor →
      ∀ i, ∃ Dc : ℝ, ∀ z ∈ St.K i, FactorEnergy St Dc z)
    (hnonneg : (pf13Nodes (boundaryNodes (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B)
      P).pf13Factor →
      ∀ i, St.factorNonneg i)
    [∀ n, FiniteDimensional ℂ (St.U.grade n)]
    (HT : TopBoundInputs (regularityNodes (pf13Nodes (boundaryNodes
      (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B) P)
      St) (topDataOf SD xT yT)) :
    Inputs
      (allConcreteNodes R D u C SD 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv P St xT yT recon Unitarizable) := by
  obtain ⟨hgates, hrec, hw1, hprop⟩ := properness_arrows R D u
  obtain ⟨hchar, hunm⟩ := character_arrows (regNodes R SD St 𝒞) D u C HC fun hm hpv =>
    noWeightZero_of_vacuum SD C (LI.ident hm) (LI.hw hm) (LI.vac hm) HC.below
      hpv.2.2
  obtain ⟨haut, hthree, hring, hmom, hm1, htw⟩ :=
    boundary_arrows (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B HB.hBJ HB.hΨ HB.hInd
  have hpf := pf13_arrow (boundaryNodes (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B) P HP
  obtain ⟨hpos, hc2⟩ := regularity_arrows
    (pf13Nodes (boundaryNodes (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B) P)
    St μ f hf hK hfK havg hfac hnonneg
  have htop := topBound_arrow (regularityNodes (pf13Nodes (boundaryNodes
    (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B) P) St) (topDataOf SD xT yT) HT
  have hsu := stronglyUnitary_arrow (topBoundNodes (regularityNodes (pf13Nodes (boundaryNodes
    (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B) P) St) (topDataOf SD xT yT)) recon
    Unitarizable LI.card
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
      L_projectiveVacuum := fun hps hc2 hinit => projectiveVacuum_arrow R St SD _ HV hps hc2 hinit.1
      L_rigid := fun hpv hc2 hinit => rigid_arrow St SD 𝒞 _ hunit hEP hpv hc2 hinit.1
      L_rational := RI.L_rational
      L_topBound := htop
      L_branchB := fun hrat hw1 hcs htop hdim =>
        branchB_arrow SD D u Bb _ HBr hrat hw1 hcs.1.1.2 htop hdim
      L_branchH := fun hB htop hcs hrat =>
        branchH_arrow SD D u Bb Hd S₁ S₂ R.certStructural _ I₁ I₂ IH hB htop hcs.1.1.1 hrat
      E_dmno := RI.E_dmno
      L_rankFork := fun hlag hH => branchRankFork_arrow SD Hd ι R.lagrangianCenter hadj hlag.1 hH
      L_autInvertible := haut
      L_noSign := fun hw1 hB hrat =>
        noSign_arrow SD D u Bb Sg HS R.stronglyRational B.dX hfp hw1 hB hrat
      L_threeInvertibles := hthree
      L_untwisted := fun h3 hdisc hlag hrat =>
        untwisted_arrow 𝕜 Cr Ah Sv B _ _ _ HU hν h3 hdisc hlag.1 hrat
      L_notRankFour := fun _ h3 hunt hw1 hpv hsign hlag hB hrat hinit =>
        notRankFour_arrow B D u _ _ _ _ _ HR h3 hw1 hsign.2 hlag hrat hinit.1 hpv hB hunt.2
      L_rankSixRing := hring
      L_rankSixMoments := hmom
      L_multiplicityOne := hm1
      L_twelveTwists := htw
      E_gsy := RI.E_gsy
      L_characters := hchar
      L_unmixed := hunm
      E_netCR := RI.E_netCR
      L_netCount := fun hcr _ hsign hring hdisc =>
        netCount_arrow R D u Sg Bn Sec _ _ _ _ HN (untwistedNode_of_inputs 𝕜 Cr Ah Sv _ HU hdisc)
          hcr hsign.1.2 hring hdisc
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
universal top bound `0 ≤ h ≤ 17/10` for the lowest weights of all simple `U`-modules; Lemma
`lem:vacuum-projective` (nonnegative lowest weights of all modules, weight zero only through `U`,
`U` projective among grading-restricted generalized modules, and `0 ≤ hw s` with `hw s = 0` only
for the class of `U`); `Rep(U)` is
rigid with every object projective; `B↓U = U ⊕ X` with `h_X = 1`,
`dim X_top = 80` (eq:B-branching); `H↓U = 𝟏 + X + Y + Y*` (eq:H-branching-fork); the net
boundary category has the `HI(ℤ/3)` ring with untwisted pointed part and `12` sectors (A2); free
`H/B`-induction from the additive closure of `L₋` is an equivalence onto all `H/B`-modules and
`ν₃(a) = 1`; `X` is not invertible, no finite-order automorphism `g` of `B`
has `B^g = U`, and `d_X ≠ 1` (Lemma `lem:no-sign-extension`); every simple `U`-module is
unitarizable; `U₁ = K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂`, `dim K = 6`, `U ⊊ B`; `U` is `C₂`-cofinite; and the embedded
parafermion factor is `K(𝔰𝔩₂, 13)`. -/
theorem concrete_conclusions (R : Nodes) (D : ClosureData A) (u : V)
    (C : CharacterData) (SD : SimpleData Simp) (𝒞 : Type*) [Category 𝒞] [MonoidalCategory 𝒞]
    (Bb : BranchBData A σ Simp)
    (Hd : BranchHData Simp) (Sg : SignData A) (B : BoundaryData ι κ) (Bn : BoundaryData ιn κn)
    (Cr : Type*) [Category Cr] [MonoidalCategory Cr] [BraidedCategory Cr] [Preadditive Cr]
    [HasFiniteBiproducts Cr] [HasCoequalizers Cr]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive Cr]
    (𝕜 : Type) [Field 𝕜] [Linear 𝕜 Cr] [MonoidalLinear 𝕜 Cr] (Ah : Mon Cr) [IsCommMonObj Ah.X] (Sv : ZMod 3 × ZMod 3 → Cr) (P : PF13Data kp W W')
    (St : StressData E H)
    (xT yT : Simp → ℕ → ℕ) (recon : Sec → Simp) (Unitarizable : Simp → Prop)
    (hI : Inputs
      (allConcreteNodes R D u C SD 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv P St xT yT recon Unitarizable)) :
    (∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1) ∧
    (∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1 ∧ B.d ρ = (3 + Real.sqrt 13) / 2 ∧ CTwists 1 B ∧
      SixResidualTwists B) ∧
    (C.F = C.Ξ₀ ∧ ∀ l n, (C.a l n : ℂ) = C.e₀ l n) ∧
    (∀ l, C.hw l = lowestWeight l ∧ C.td l = topDim l) ∧
    (∀ s, 0 ≤ SD.hw s ∧ SD.hw s ≤ 17 / 10) ∧
    VacuumNode St SD ∧ RigidSemisimple 𝒞 ∧
    BranchB SD D u Bb ∧ HBranching SD Hd ∧ (NetHI Bn ∧ Fintype.card Sec = 12) ∧
    (UntwistedNode 𝕜 Cr Ah Sv ∧ B.ν₃ = 1) ∧
    ((¬ Sg.XInvertible ∧ ∀ g, ¬ FixesExactlyU D u Sg g) ∧ B.dX ≠ 1) ∧
    (∀ l, Unitarizable l) ∧
    (D.U u ⊓ A.grade 1 = D.K ∧ Module.finrank k D.K = 6 ∧ IsSl2SumSpan A D.K) ∧ D.U u ≠ ⊤ ∧
    FiniteDimensional ℂ (H ⧸ C2 St.U) ∧
    (∃ φ : W ≃ₗ[kp] W', φ P.L = P.L' ∧ φ P.a = P.a' ∧ φ P.b = P.b' ∧ φ P.d = P.d' ∧
      φ P.A.vac = P.A'.vac ∧ ∀ (n : ℤ) (x y : W), φ (P.A.mode n x y) = P.A'.mode n (φ x) (φ y)) := by
  obtain ⟨hm1, htw, hmd, hunt, -, -, htop, hH, hsign, hring⟩ := boundary_chain hI
  obtain ⟨-, -, hsu, -, -, -, -⟩ := thm_main_net hI
  obtain ⟨-, hw1, hprop⟩ := prop_mainproper hI
  have hinit := initialGrades_of hI
  have hchar := hI.L_characters hmd hw1 (projectiveVacuum_of hI) hinit (stronglyRational_of hI)
  have hpf := hI.L_pf13 hI.C_structural
  have hc2 := hI.L_c2 (hI.L_positiveStress hI.C_structural hpf) hinit
  have hB := hI.L_branchB (stronglyRational_of hI) hw1 hI.C_structural htop hI.C_dimensions
  have hrig := hI.L_rigid (projectiveVacuum_of hI) hc2 hinit
  have hnet := hI.L_netCount (hI.E_netCR (stronglyRational_of hI) hinit) hH hsign hring
    hI.C_discriminant
  exact ⟨hm1, htw, hchar.1, hchar.2, htop, projectiveVacuum_of hI, hrig, hB, hH, hnet, hunt,
    hsign, hsu, hw1, hprop, hc2, hpf⟩

/-- **From the remaining inputs to the concrete conclusions** (`inputs_of_concrete` followed by
`concrete_conclusions`): the proved arrows are used in this derivation (all except `L_unmixed`,
whose node no later arrow uses). -/
theorem concrete_proof_map [CharZero k] [CharZero kp] [Fintype σ] [DecidableEq σ]
    (R : Nodes) (D : ClosureData A) (u : V)
    (C : CharacterData) (SD : SimpleData Simp) (𝒞 : Type*) [Category 𝒞] [MonoidalCategory 𝒞]
    [Preadditive 𝒞] [Linear ℂ 𝒞] [HasBinaryBiproducts 𝒞] [HasKernels 𝒞]
    [∀ X Y : 𝒞, FiniteDimensional ℂ (X ⟶ Y)] (Bb : BranchBData A σ Simp)
    (Hd : BranchHData Simp) (Sg : SignData A) (B : BoundaryData ι κ) (Bn : BoundaryData ιn κn)
    (Cr : Type*) [Category Cr] [MonoidalCategory Cr] [BraidedCategory Cr] [Preadditive Cr]
    [HasFiniteBiproducts Cr] [HasCoequalizers Cr]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : Cr, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [MonoidalPreadditive Cr]
    (𝕜 : Type) [Field 𝕜] [Linear 𝕜 Cr] [MonoidalLinear 𝕜 Cr] (Ah : Mon Cr) [IsCommMonObj Ah.X] (Sv : ZMod 3 × ZMod 3 → Cr) (P : PF13Data kp W W')
    (St : StressData E H)
    (xT yT : Simp → ℕ → ℕ) (recon : Sec → Simp) (Unitarizable : Simp → Prop)
    (RI : RemainingInputs
      (allConcreteNodes R D u C SD 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv P St xT yT recon Unitarizable))
    (HB : BoundaryInputs (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B 𝒞)
    (HC : CharacterInputs (regNodes R SD St 𝒞) D u C) (LI : SimpleLabels R.modularData SD C)
    (HP : PF13Inputs P) (HBr : BranchBInputs SD D u Bb R.stronglyRational)
    (HS : SignInputs SD D u Bb Sg)
    (hadj : R.lagrangianCenter → Fintype.card ι = ∑ l, Hd.mult l ^ 2)
    (hfp : R.stronglyRational → B.dX = 1 → Sg.XInvertible) (HV : VacuumInputs St SD R.initialGrades)
    (HR : RankFourInputs B D u R.lagrangianCenter R.stronglyRational R.initialGrades
      (VacuumNode St SD) (BranchB SD D u Bb))
    (S₁ : SectorData A M₁ τ₁ Simp) (S₂ : SectorData A M₂ τ₂ Simp)
    (I₁ : SectorInputs SD D u S₁ R.certStructural R.stronglyRational)
    (I₂ : SectorInputs SD D u S₂ R.certStructural R.stronglyRational)
    (IH : BranchHInputs SD Bb Hd S₁ S₂)
    (hunit : VacuumNode St SD → Projective (𝟙_ 𝒞))
    (hEP : FiniteDimensional ℂ (H ⧸ C2 St.U) → R.initialGrades → Projective (𝟙_ 𝒞) →
      ∀ X : 𝒞, Nonempty (HasRightDual X))
    (HN : NetInputs D u Sg Bn Sec R.netCompletelyRational R.certDiscriminant
      (∃ ρ ρ₁ ρ₂ m, IsHIRing B.F B.a ρ ρ₁ ρ₂ m) (UntwistedNode 𝕜 Cr Ah Sv))
    [∀ X Y : Cr, FiniteDimensional 𝕜 (X ⟶ Y)] (HU : UntwistedInputs 𝕜 Cr Ah Sv R.certDiscriminant)
    (hν : UntwistedNode 𝕜 Cr Ah Sv → R.certDiscriminant → R.lagrangianCenter → R.stronglyRational →
      (Z3Generator B.F B.a ∧ ∀ x, B.F.IsInvertible x → x = B.F.unit ∨ x = B.a ∨ x = B.F.dual B.a) →
      B.ν₃ = 1)
    {G : Fin 4 → Type*} [∀ i, MeasurableSpace (G i)] (μ : ∀ i, Measure (G i))
    [∀ i, IsProbabilityMeasure (μ i)] (f : ∀ i, G i → E) (hf : ∀ i, Integrable (f i) (μ i))
    (hK : ∀ i, IsCompact (St.K i)) (hfK : ∀ i g, f i g ∈ St.K i)
    (havg : ∀ i, St.avg i = ∫ g, f i g ∂(μ i))
    (hfac : (pf13Nodes (boundaryNodes (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B)
      P).pf13Factor →
      ∀ i, ∃ Dc : ℝ, ∀ z ∈ St.K i, FactorEnergy St Dc z)
    (hnonneg : (pf13Nodes (boundaryNodes (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B)
      P).pf13Factor →
      ∀ i, St.factorNonneg i)
    [∀ n, FiniteDimensional ℂ (St.U.grade n)]
    (HT : TopBoundInputs (regularityNodes (pf13Nodes (boundaryNodes
      (coreNodes R D u C SD St 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv) B) P)
      St) (topDataOf SD xT yT)) :
    (∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1) ∧
    (∃ ρ ρ₁ ρ₂, IsHIRing B.F B.a ρ ρ₁ ρ₂ 1 ∧ B.d ρ = (3 + Real.sqrt 13) / 2 ∧ CTwists 1 B ∧
      SixResidualTwists B) ∧
    (C.F = C.Ξ₀ ∧ ∀ l n, (C.a l n : ℂ) = C.e₀ l n) ∧
    (∀ l, C.hw l = lowestWeight l ∧ C.td l = topDim l) ∧
    (∀ s, 0 ≤ SD.hw s ∧ SD.hw s ≤ 17 / 10) ∧
    VacuumNode St SD ∧ RigidSemisimple 𝒞 ∧
    BranchB SD D u Bb ∧ HBranching SD Hd ∧ (NetHI Bn ∧ Fintype.card Sec = 12) ∧
    (UntwistedNode 𝕜 Cr Ah Sv ∧ B.ν₃ = 1) ∧
    ((¬ Sg.XInvertible ∧ ∀ g, ¬ FixesExactlyU D u Sg g) ∧ B.dX ≠ 1) ∧
    (∀ l, Unitarizable l) ∧
    (D.U u ⊓ A.grade 1 = D.K ∧ Module.finrank k D.K = 6 ∧ IsSl2SumSpan A D.K) ∧ D.U u ≠ ⊤ ∧
    FiniteDimensional ℂ (H ⧸ C2 St.U) ∧
    (∃ φ : W ≃ₗ[kp] W', φ P.L = P.L' ∧ φ P.a = P.a' ∧ φ P.b = P.b' ∧ φ P.d = P.d' ∧
      φ P.A.vac = P.A'.vac ∧ ∀ (n : ℤ) (x y : W), φ (P.A.mode n x y) = P.A'.mode n (φ x) (φ y)) :=
  concrete_conclusions R D u C SD 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv P St xT yT recon Unitarizable
    (inputs_of_concrete R D u C SD 𝒞 Bb Hd Sg B Bn Cr 𝕜 Ah Sv P St xT yT recon Unitarizable RI HB HC
      LI HP HBr HS hadj hfp HV HR S₁ S₂ I₁ I₂ IH hunit hEP HN HU hν μ f hf hK hfK havg hfac hnonneg
      HT)

#print axioms inputs_of_concrete
#print axioms concrete_conclusions
#print axioms concrete_proof_map

end HaagerupIzumi.C8.ProofMap
