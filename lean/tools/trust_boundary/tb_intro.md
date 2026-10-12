# Trust boundary of the c = 8 formalization (`concrete_proof_map`)

*Status: working tree of 4 October 2026, 17:10 CDT (branch `c8-checkpoint-20260927`, uncommitted).
Lean v4.33.1, Mathlib `0df444a3`.  Paths are relative to `lean/HaagerupIzumi/C8/`; manuscript line
numbers refer to `c8_expanded_20260929/haagerup_c8_expanded.tex`.*

*This file is generated: edit `lean/tools/trust_boundary/tb_gen.py` (entries), `tb_intro.md`
(Sections 1–3) or `tb_outro.md` (Section 8), then run
`python3 lean/tools/trust_boundary/tb_gen.py` and `python3 lean/tools/trust_boundary/tb_check.py`
(checks every file:line reference of Section 5 against the sources).  Line numbers written in
`tb_gen.py` refer to the sources of 4 October, 14:15 CDT and are translated by `tb_linemap.json`;
references to `Lattice/` and `ProofMapLattice.lean` are looked up when the file is generated.*

This document lists **every hypothesis** on which the theorem `concrete_proof_map`
(ProofMapConcrete.lean:430) still depends, and therefore every hypothesis behind the three main
results of the manuscript as they appear in the Lean proof map.  It is written for review: each
hypothesis has its Lean name and location, a tag, a one-line mathematical statement, the
citation or manuscript lines, and whether the lattice model now proves it.

## 1. What is proved

* `concrete_proof_map` is kernel-checked; `#print axioms` gives only `propext`, `Classical.choice`,
  `Quot.sound` (no `sorry`, no `axiom`, no `native_decide`).  It is `concrete_conclusions`
  (ProofMapConcrete.lean:388) applied to `inputs_of_concrete` (ProofMapConcrete.lean:251).
* `inputs_of_concrete` proves the instance `Inputs (allConcreteNodes …)` of the proof-map
  structure `ProofMap.Inputs` (ProofMap.lean:157).  Of its 46 fields (5 certificates `C_…`,
  11 external theorems `E_…`, 30 manuscript lemmas `L_…`), **26 `L_` arrows are theorems** about
  concrete objects; the other 20 (5 `C_`, 11 `E_`, 4 open `L_`) are the fields of the hypothesis
  `RemainingInputs`.  The proved arrows are `L_gates`, `L_recursive`, `L_weightOne`, `L_proper`, `L_pf13`,
  `L_positiveStress`, `L_c2`, `L_projectiveVacuum`, `L_rigid`, `L_topBound`, `L_branchB`,
  `L_branchH`, `L_rankFork`, `L_noSign`, `L_untwisted`, `L_notRankFour`, `L_netCount`,
  `L_autInvertible`, `L_threeInvertibles`, `L_rankSixRing`, `L_rankSixMoments`,
  `L_multiplicityOne`, `L_twelveTwists`, `L_characters`, `L_unmixed`, `L_stronglyUnitary`; each
  proof uses the input bundles listed in Section 5.
* The conclusions of `concrete_proof_map` are concrete statements (ProofMapConcrete.lean:478–491):
  the boundary fusion ring `K₀(𝓕)` is `HI(ℤ/3)` with `d_ρ = (3 + √13)/2`, the `C`-twists `1, ζ₃,
  ζ₃²` and the six residual twists (the nonresidue thirteenth roots); the character vector is the
  `γ = 0` Evans–Gannon vector, coefficient by coefficient; the lowest weights and top dimensions of
  the table at line 4178; `0 ≤ h ≤ 17/10` for every simple `U`-module; Lemma
  `lem:vacuum-projective` (nonnegative lowest weights, `U` the only weight-zero simple, `U`
  projective); `Rep(U)` rigid with every object projective; `B↓U = U ⊕ X` with `h_X = 1`,
  `dim X_top = 80`; `H↓U = 𝟏 + X + Y + Y*`; the net boundary category has the `HI(ℤ/3)` ring and
  twelve sectors; free `H/B`-induction from `L₋` is an equivalence onto all `H/B`-modules and
  `ν₃(a) = 1`; `X` is not invertible, `B^g ≠ U` for every finite-order automorphism, `d_X ≠ 1`;
  every simple `U`-module is unitarizable; `U₁ = K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂`, `dim K = 6`, `U ⊊ B`; `U` is
  `C₂`-cofinite; the parafermion factor is `K(𝔰𝔩₂, 13)`.
* **The lattice instance.**  `lattice_proof_map` (ProofMapLattice.lean) is `concrete_proof_map`
  for the actual lattice VOA `V_{E₆⊕A₂}` of `Lattice/` (`A = latA hB`, closure data
  `D = latticeDP` with the actual currents, `S₂`, `u`, `P₄`; only `S₃` is a parameter), from
  `hB : FLMBorcherds`.  There `C_dimensions`, `C_pct` (with the node `certPCT` given its meaning:
  `θ_g` mode-compatible, `θ_g S₂ = S₂`, `θ_g U = U`) and the minimal-generation conjuncts of
  `C_finiteClosure` with nineteen `LowerCertificate` fields are theorems; Section 7 gives the
  hypothesis count of both theorems.
* The three main results `prop_mainproper`, `thm_main_net`, `thm_claim_main`
  (ProofMap.lean:426, 478, 494) hold for `allConcreteNodes` under the same hypotheses.  Several of their conclusions
  are **opaque nodes** (Section 2): strong rationality, complete rationality of the net,
  `Rep(𝒩_U) ≃ Z(𝓗₃)`, the diagonal full net, complete unitarity, `Rep(U) ≃ Z(𝓗₃)`, the `E₈`
  extension.  For these, the Lean theorem certifies that the external theorems and open lemmas
  compose correctly; their content is exactly the content of the `E_…` and open `L_…` fields that
  conclude them.

## 2. How to read the entries

**Tags.**  **[external]**: a theorem from the literature, specialized to the objects at hand.
**[certificate]**: an exact finite identity of the lattice construction (Appendix `sec:ledger`),
computed by the lattice engine.  **[manuscript step]**: an argument of the manuscript that is not
formalized.  **[definitional]**: the meaning of a concrete parameter (it says what a Lean object
*is*).  **[standard]**: standard mathematics not formalized here.  An entry may carry several
tags; it is listed under its primary tag, the others are in the last column.

**Conditional hypotheses.**  Most inputs are stated as implications from a node of the proof map
(e.g. `stronglyRational → …`), mirroring where the manuscript uses that node.  A node is either
*concrete* (a Lean proposition about the concrete objects) or *opaque* (a `Prop` parameter of
`R : Nodes`).  In `allConcreteNodes` the opaque nodes, or opaque parts of nodes, are:

* opaque: `certPCT`, `certDiscriminant`, `stronglyRational`, `modularData`,
  `netCompletelyRational`, `annulus`, `completelyUnitary`, `boundaryUnitary`,
  `boundaryIsHaagerup`, `repIsCenter`, `netRepIsCenter`, `netExtension`, `diagonalTheory`,
  `e8Extension`;
* opaque part ∧ concrete part: `certStructural` (opaque ∧ `CurrentsIrreducible` ∧ `PF13SelfRow` ∧
  the positive-stress identity), `initialGrades` (opaque ∧ `dim U₀ = 1`), `lagrangianCenter`
  (opaque ∧ positive dimension character with `∑ d² = 3s`, `d_X = s - 1`), `reconstruction`
  (opaque ∧ `recon` injective with unitarizable values);
* all other nodes are concrete.

**Lattice model.**  `Lattice/` builds the lattice VOA `V_{E₆⊕A₂}` concretely (Fock model) as
`latticeVOA hF`, whose only hypothesis is `hF : FLMInput`; `FLMInput` follows from
`FLMBorcherds` alone (`flmInput_of_borcherds`, Lattice/FLMReduce.lean:237;
`flmInput_iff_borcherds`, 241): the Borcherds identity for the concrete modes, FLM Theorem
8.10.2 — an **[external]** input of the lattice model itself.  `latticeD`
(Lattice/S2Link.lean:115) is the closure data with the currents of `Lattice/Data.lean` and
`S₂ = S2span` (the 120 echelon vectors of the minimal-generation record); `latticeDP`
(Lattice/P4Link.lean:93) is `latticeD` with the actual triplet `P₄`, so that only `S₃` (dimension
956, not yet exported) remains a parameter.  The column "Lattice model" says whether the
statement is a theorem for `latticeD`/`latticeDP` (modulo `FLMBorcherds`) and whether it is
discharged in `lattice_proof_map`.

**The lattice instance `lattice_proof_map`** (ProofMapLattice.lean).  `concrete_proof_map` is
stated for arbitrary closure data; `lattice_proof_map` instantiates it at `A = latA hB =
latticeVOA (flmInput_of_borcherds hB)`, `D = latD hB S₃ hS₃ = latticeDP …`, `u = uV`.  Each
lattice theorem was checked against the node it replaces:

* `certDimensions` (concrete node of `ProofMapProperness.concreteNodes`: `dim K = 6`,
  `dim B₁ = 86`, `IsSl2SumSpan A K`): `certDimensions_latticeD` is a theorem about that very node.
* `certFiniteClosure` (concrete node `certFiniteClosureProp D u`): its conjuncts `ω ∈ S₂`,
  `u ∈ S₂`, `S₂ ≤ U` are `minimalGeneration_latticeD`; of the 26 fields of `LowerCertificate`,
  nineteen are theorems for `latticeDP`: `KK0` (`KK0_latD`, proved in ProofMapLattice.lean from the
  kernel-checked current brackets of `Lattice/Relations.lean` and skew symmetry); `ω_mem`;
  `KS₂0`, `TK`, `KmK` (the closure conditions
  `S2Closed_S2span` of the record, which with `S₂ ≤ closureSpace` make up
  `S2span_eq_closureSpace`, all 524 closure relations; `T x = x_(-2) 𝟏` is the axiom `T_eq`);
  `hL_q`, `hR_qp`, `hR_q0`, `hR_qm` (P4Link, stated with the same `A.mode 0 D.hL q`,
  `(2 : ℂ) • D.qp`, … as the fields); `eL_q`, `fL_q` (`eL_q_latticeDP`, `fL_q_latticeDP`,
  Lattice/P4Left.lean); `fR_qp`, `fR_q0`, `fR_qm` (`fR_*_latticeDP`, Lattice/P4RFRP.lean,
  P4RFRZ.lean, P4RFRM.lean); `eR_qp`, `eR_q0`, `eR_qm` (`eR_*_latticeDP`, Lattice/P4RERP.lean,
  P4RDerived.lean, the last two by the commutator formula); `L2_P₄` (`L2_P4_latticeDP`,
  Lattice/P4RL2.lean); `KS₂1` (`KS21_latticeDP`, Lattice/KS21.lean: 720 kernel checks with
  `modeQRF`, about 320 s of kernel time).  The other 7 fields
  (`LowerRest`), the Gate 4/5 certificates and the two
  nilpotence statements remain inputs, now about the concrete algebra (`LatticeClosureInputs`).
  `finrank_S2span` (`dim S₂ = 120`) is proved but no node needs it.
* `certPCT` is an **opaque** node of `ProofMap`, so no lattice theorem can discharge it in
  `concrete_proof_map`.  `lattice_proof_map` uses `pctNodes R D u`, which sets
  `certPCT := PCTCert D u` (ProofMapLattice.lean), the reading of line 2604: `θ_g = pctV` (the
  map `eq:pct`, lines 1975–1989) is compatible with all modes (`PCTModeCompatible`; with the
  proved antilinearity `pctV_smul` and `θ_g² = 1`, an antilinear automorphism of the lattice
  VOA), `θ_g S₂ = S₂` (`certPCT_latticeD`), and `θ_g U = U` (`pctV_mem_U_latD`, proved in
  ProofMapLattice.lean from the first two conjuncts, `θ_g 𝟏 = 𝟏`, `θ_g ω = ω` and `S₂ ≤ U`: each
  current `k` equals `½ L(1) T k` with `T k ∈ S₂`, so `θ_g k ∈ ω_(2) S₂ ⊆ U`).  The first conjunct
  is the theorem `pctModeCompatible` (Lattice/PCTModes.lean, no hypotheses: reduction to basis
  states and the cocycle identity `ε(-α, -β) = ε(α, β)`), so the PCT node is discharged
  outright (`certPCT_latD`).  The node is used
  only as a premise of `E_cklw529`, whose remaining content is then: the transported form
  `⟨v, w⟩_g` is positive definite with PCT operator `θ_g` (Dong–Lin unitarity of the lattice VOA,
  transported by `g`, lines 1985–1987), so the `θ_g`-stable `U` is a unitary subalgebra, hence
  simple (CKLW Proposition 5.29), with `c = 8` and the initial grades.
* All other hypotheses of `concrete_proof_map` are hypotheses of `lattice_proof_map`, specialized
  to the lattice algebra (`LatticeRemainingInputs` holds the 17 other fields of
  `RemainingInputs`).  New hypothesis: `hB : FLMBorcherds`; the instance argument
  `[CharZero k]` disappears (`k = ℂ`).
* `KS₂1` (`K_(1) S₂ ⊆ K`, grade two): a first probe with the kernel decomposition `kOK` of
  `Lattice/LatticeLowerCore.lean` (`lean/tools/lattice_export/gen_lower_ks21.py`: `H_R(1) r₆₁`
  alone 8.3 s, probe peak 3.1 GiB) was stopped; it is now proved by the lattice agent with the
  faster `modeQRF` (`KS21_latticeDP`, Lattice/KS21.lean: 720 checks, about 320 s of kernel time
  in total).  Of the 7 remaining `LowerCertificate` fields, `S₂S₂1`, `S₂S₂2` are `120 × 120`
  products of the basis vectors of `S₂`; `S₂S₂0`, `N₃_le_S₃`, `S₃_prov`, `P₄_prov`, `L1_P₄` need
  `S₃`.

## 3. The concrete parameters

`concrete_proof_map` is universally quantified over the following objects.  Their *meaning* is
definitional (fixed by the docstrings and by the inputs that mention them); nothing forces an
arbitrary instance to be the intended object except those inputs.

| Parameter | Lean type (file:line) | Intended object | Notes |
|---|---|---|---|
| `R` | `Nodes` (ProofMap.lean:36) | the claims of the manuscript | supplies the opaque nodes of Section 2 |
| `k`, `V`, `A` | field, space, `VertexOperatorAlgebra k V` (VertexAlgebra/Basic.lean:149) | the lattice VOA `B = V_{E₆⊕A₂}` | `[CharZero k]`; for the lattice model `A = latticeVOA hF` over `ℂ` (needs `FLMBorcherds`) |
| `D` | `ClosureData A` (Properness/Setup.lean:107) | currents `h,e,f` (left/right), `S₂` (dim 120), `S₃` (dim 956), triplet `q₊, q₀, q₋` | Prop fields `currents_grade`, `S₂_grade`, `S₃_grade`, `triplet_grade` (124–127) [definitional]; `latticeDP` proves them except `S₃_grade` (`triplet_grade_P4`, Lattice/P4Link.lean:85; `hS₃` is a parameter of `lattice_proof_map`) |
| `u` | `V` | the field `u ∈ S₂` | `U = D.U u = ⟨K, ω, u⟩` (MainProperness.lean:48) |
| `C` | `CharacterData` (ProofMapConcreteCharacters.lean:226) | Zhu's representation `σ`, the character vector `F` of the twelve labelled simples, graded dimensions `a`, `hw`, `td`, the Evans–Gannon columns `Ξ₀, Ξ₃` and their coefficients, multiplicities `n₁, n₂` | indexed by `Characters.Label` |
| `Simp`, `SD` | type, `SimpleData Simp` (ProofMapSimples.lean:27) | isomorphism classes of simple `U`-modules, lowest weights `hw`, top dimensions `td`, class `vac` of `U` | finite with rational `hw`: [external] from `C₂`-cofiniteness (Zhu; Dong–Li–Mason; Miyamoto), known before `modularData` (ProofMapSimples.lean⁠:20–24); linked to `Label` only by `LI` (after `modularData`), compatibly with `hw`, `td`, `vac` and hence the twists |
| `𝒞` | category with `MonoidalCategory`, `Preadditive`, `Linear ℂ`, binary biproducts, kernels, finite-dimensional Homs (ProofMapConcrete.lean:432–434) | `Rep(U)` | carries `RigidSemisimple 𝒞` and the objects `H, X, Y` of `BoundaryInputs`; linked to `St.U` only by `hunit` |
| `HB.H`, `HB.X`, `HB.Y` | objects of `𝒞` (fields of `BoundaryInputs`, ProofMapConcrete.lean:152–156) | the extension algebra `H`, the summands `X` of `B↓U` and `Y` of `H↓U` | constrained by `simple1`, …, `dec` |
| `Bb` | `BranchBData A σ Simp` (ProofMapConcreteBranching.lean:79) | a decomposition `B↓U = ⊕_{j:σ} M_j`: classes `lab`, weight-one spaces `T j`, vacuum summand `vac` | |
| `Hd` | `BranchHData Simp` (ProofMapConcreteBranching.lean:97) | multiplicities `[H↓U : M_l]` | |
| `Sg` | `SignData A` (ProofMapConcreteBranching.lean:115) | finite-order automorphisms `g` of `B` with linear action `act`, toral rank `toral g` of `(B₁)^g`, the proposition `XInvertible` | `toral`, `XInvertible` are unmodelled (meaning definitional) |
| `B` | `BoundaryData ι κ` (ProofMapConcreteBoundary.lean:93) | `K₀(𝓕)`, the invertible `a`, dimensions `d`, `s`, `d_X`, `d_Y`, center data `θC, b, n, θ, ε, ν₃` | `ι` = simples of `𝓕` (`card ι = rank 𝓕`), `κ` = residual central simples |
| `Bn` | `BoundaryData ιn κn` | the same for `𝓕_net` | not linked to `B` |
| `Cr`, `𝕜`, `Ah`, `Sv` | monoidal 𝕜-linear category with finite biproducts and finite-dimensional Homs, `Mon Cr`, `ZMod 3 × ZMod 3 → Cr` (ProofMapConcrete.lean:436–437, 459–460) | `Rep(B)`, the algebra `H/B`, the nine invertibles `S v` | not linked to `A` |
| `P` | `PF13Data kp W W'` (ProofMapConcretePF13.lean:70) | the algebra generated by `L, a` inside `U`, the parafermion algebra `K(𝔰𝔩₂,13)`, generators `L, a, b, d` and `L′, a′, b′, d′`, `c = 8/5` | `[CharZero kp]` |
| `St` | `StressData E H` (ProofMapConcreteRegularity.lean:69) | `U` over `ℂ` on its pre-Hilbert space `H`, the real space `E` of PCT-fixed weight-two vectors, `ω`, Haar averages `avg`, orbits `K`, the predicate `factorNonneg` | Prop fields `ιE_add`, `ιE_smul`, `ιE_grade`, `ιE_ω` (75–80) [definitional]; `factorNonneg` unmodelled; `St.U` is **not linked** to `D.U u` |
| `xT`, `yT` | `Simp → ℕ → ℕ` | multiplicities of the fourteen core tops in each lowest space | via `topDataOf` (ProofMapConcrete.lean:111) |
| `Sec`, `recon` | finite type, `Sec → Simp` | net sectors, reconstruction on isomorphism classes | |
| `Unitarizable` | `Simp → Prop` | "admits a positive-definite invariant Hermitian form" | unmodelled: the meaning of strong unitarity rests on it |
| `S₁`, `S₂` | `SectorData A M τ Simp` (ProofMapConcreteBranchH.lean:41) | the sectors `J`, `J²` of `H = B ⊕ J ⊕ J²` as weak `B`-modules, `J₁`, and their decompositions over `U` | |
| `G`, `μ`, `f` | measure spaces, `Measure`, `G i → E` (ProofMapConcrete.lean:464–465) | the compact current group with Haar measure, orbit maps of the four factor conformal vectors | |

The vertex-algebra axioms of `A`, `St.U`, `P.A`, `P.A'` are fields of the structures
`VertexAlgebra` / `VertexOperatorAlgebra` (VertexAlgebra/Basic.lean:45, 149); for the lattice
algebra they are theorems modulo `FLMBorcherds` (`latticeVOA`, Lattice/VOA.lean:133).
