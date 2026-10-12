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
(ProofMapConcrete.lean:445) still depends, and therefore every hypothesis behind the three main
results of the manuscript as they appear in the Lean proof map.  It is written for review: each
hypothesis has its Lean name and location, a tag, a one-line mathematical statement, the
citation or manuscript lines, and whether the lattice model now proves it.

## 1. What is proved

* `concrete_proof_map` is kernel-checked; `#print axioms` gives only `propext`, `Classical.choice`,
  `Quot.sound` (no `sorry`, no `axiom`, no `native_decide`).  It is `concrete_conclusions`
  (ProofMapConcrete.lean:400) applied to `inputs_of_concrete` (ProofMapConcrete.lean:261).
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
* The conclusions of `concrete_proof_map` are concrete statements (ProofMapConcrete.lean:495–508):
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
  (ProofMap.lean:428, 480, 496) hold for `allConcreteNodes` under the same hypotheses.  Several of their conclusions
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
| `C` | `CharacterData` (ProofMapConcreteCharacters.lean:228) | Zhu's representation `σ`, the character vector `F` of the twelve labelled simples, graded dimensions `a`, `hw`, `td`, the Evans–Gannon columns `Ξ₀, Ξ₃` and their coefficients, multiplicities `n₁, n₂` | indexed by `Characters.Label` |
| `Simp`, `SD` | type, `SimpleData Simp` (ProofMapSimples.lean:33) | isomorphism classes of simple `U`-modules, lowest weights `hw`, top dimensions `td`, class `vac` of `U` | finite with rational `hw`: [external] from `C₂`-cofiniteness (Zhu; Dong–Li–Mason; Miyamoto), known before `modularData` (ProofMapSimples.lean:20–24); linked to `Label` only by `LI` (after `modularData`), compatibly with `hw`, `td`, `vac` and hence the twists |
| `𝒞` | category with `MonoidalCategory`, `Preadditive`, `Linear ℂ`, binary biproducts, kernels, finite-dimensional Homs (ProofMapConcrete.lean:447–449) | `Rep(U)` | carries `RigidSemisimple 𝒞` and the objects `H, X, Y` of `BoundaryInputs`; linked to `St.U` only by `hunit` |
| `HB.H`, `HB.X`, `HB.Y` | objects of `𝒞` (fields of `BoundaryInputs`, ProofMapConcrete.lean:159–163) | the extension algebra `H`, the summands `X` of `B↓U` and `Y` of `H↓U` | constrained by `simple1`, …, `dec` |
| `Bb` | `BranchBData A σ Simp` (ProofMapConcreteBranching.lean:79) | a decomposition `B↓U = ⊕_{j:σ} M_j`: classes `lab`, weight-one spaces `T j`, vacuum summand `vac` | |
| `Hd` | `BranchHData Simp` (ProofMapConcreteBranching.lean:97) | multiplicities `[H↓U : M_l]` | |
| `Sg` | `SignData A` (ProofMapConcreteBranching.lean:115) | finite-order automorphisms `g` of `B` with linear action `act`, toral rank `toral g` of `(B₁)^g`, the proposition `XInvertible` | `toral`, `XInvertible` are unmodelled (meaning definitional) |
| `B` | `BoundaryData ι κ` (ProofMapConcreteBoundary.lean:93) | `K₀(𝓕)`, the invertible `a`, dimensions `d`, `s`, `d_X`, `d_Y`, center data `θC, b, n, θ, ε, ν₃` | `ι` = simples of `𝓕` (`card ι = rank 𝓕`), `κ` = residual central simples |
| `Bn` | `BoundaryData ιn κn` | the same for `𝓕_net` | not linked to `B` |
| `Cr`, `𝕜`, `Ah`, `Sv` | monoidal 𝕜-linear category with finite biproducts and finite-dimensional Homs, `Mon Cr`, `ZMod 3 × ZMod 3 → Cr` (ProofMapConcrete.lean:451–452, 476–477) | `Rep(B)`, the algebra `H/B`, the nine invertibles `S v` | not linked to `A` |
| `P` | `PF13Data kp W W'` (ProofMapConcretePF13.lean:70) | the algebra generated by `L, a` inside `U`, the parafermion algebra `K(𝔰𝔩₂,13)`, generators `L, a, b, d` and `L′, a′, b′, d′`, `c = 8/5` | `[CharZero kp]` |
| `St` | `StressData E H` (ProofMapConcreteRegularity.lean:69) | `U` over `ℂ` on its pre-Hilbert space `H`, the real space `E` of PCT-fixed weight-two vectors, `ω`, Haar averages `avg`, orbits `K`, the predicate `factorNonneg` | Prop fields `ιE_add`, `ιE_smul`, `ιE_grade`, `ιE_ω` (75–80) [definitional]; `factorNonneg` unmodelled; `St.U` is **not linked** to `D.U u` |
| `xT`, `yT` | `Simp → ℕ → ℕ` | multiplicities of the fourteen core tops in each lowest space | via `topDataOf` (ProofMapConcrete.lean:112) |
| `Sec`, `recon` | finite type, `Sec → Simp` | net sectors, reconstruction on isomorphism classes | |
| `Unitarizable` | `Simp → Prop` | "admits a positive-definite invariant Hermitian form" | unmodelled: the meaning of strong unitarity rests on it |
| `S₁`, `S₂` | `SectorData A M τ Simp` (ProofMapConcreteBranchH.lean:41) | the sectors `J`, `J²` of `H = B ⊕ J ⊕ J²` as weak `B`-modules, `J₁`, and their decompositions over `U` | |
| `G`, `μ`, `f` | measure spaces, `Measure`, `G i → E` (ProofMapConcrete.lean:481–482) | the compact current group with Haar measure, orbit maps of the four factor conformal vectors | |

The vertex-algebra axioms of `A`, `St.U`, `P.A`, `P.A'` are fields of the structures
`VertexAlgebra` / `VertexOperatorAlgebra` (VertexAlgebra/Basic.lean:45, 149); for the lattice
algebra they are theorems modulo `FLMBorcherds` (`latticeVOA`, Lattice/VOA.lean:133).


## 4. The 20 fields of `RemainingInputs` (overview)

`RemainingInputs` (ProofMapConcrete.lean:201) holds the arrows of `ProofMap.Inputs` that are not proved for the concrete nodes.  Each is listed again, with full detail, under its tag in Section 5.

| Field | File:line | Tag | One line |
|---|---|---|---|
| `C_finiteClosure` | ProofMapConcrete.lean:202 (node ProofMapProperness.lean:69, def ProofMapProperness.lean:39) | [certificate] | The finite closure certificates: `LowerCertificate D`, a Gate 4 certificate with a Gate 5 certificate, nilpotence of raising/lowering words of length 25 on `S₃`, and `ω ∈ S₂`, `u ∈ S₂`, `S₂ ≤ U` (sub-entries below) |
| `C_dimensions` | ProofMapConcrete.lean:203 (node ProofMapProperness.lean:70–71) | [certificate] | `dim K = 6`, `dim B₁ = 86`, and `K` is spanned by two commuting standard 𝔰𝔩₂-triples (`IsSl2SumSpan`) |
| `C_pct` | ProofMapConcrete.lean:204 (node ProofMap.lean:44–45, opaque) | [certificate] | The exact PCT certificate: the transported PCT involution `θ_g` preserves `S₂` |
| `C_structural` | ProofMapConcrete.lean:205 (nodes ProofMapConcreteBranching.lean:139, ProofMapConcretePF13.lean:90, ProofMapConcreteRegularity.lean:104) | [certificate] | Conjunction of: the opaque part `R.certStructural` (Potts/PF13 fields, the core `T` and its spectral witnesses, cert:structural-inputs); `CurrentsIrreducible D u` (ProofMapConcreteBranching.lean:74: `B₁/K` has no proper nonzero subspace stable under the zero modes of `U`); `PF13SelfRow P.A P.L P.a P.b P.d P.c` (`c = 8/5`) (ProofMapConcretePF13.lean:51–67: the 16 one-sided OPE identities of the generated pair `L, a`); and the positive-stress identity `ω = ω_{A₁,₁} + (3403/4563) ω̄_{A₁,₃₉} + (25/6) p̄ + (25/26) z̄` (ProofMapConcreteRegularity.lean:52, 129) |
| `C_discriminant` | ProofMapConcrete.lean:206 (node ProofMap.lean:50, opaque) | [certificate] | The discriminant form of the lattice VOA `B` is `(ℤ/3)²` with `q(a,b) = (2a²+b²)/3`, and `H/B` lies on the isotropic line `L₊` |
| `E_cklw529` | ProofMapConcrete.lean:207 (doc ProofMap.lean:178–184) | [external] | A PCT-stable strongly generated subalgebra of the unitary lattice VOA is a simple unitary VOA of CFT type with `c = 8`, `U₂ = S₂`, `U₃ = S₃`; concrete conjunct `dim U₀ = 1` |
| `L_rational` | ProofMapConcrete.lean:208 (doc ProofMap.lean:232–235) | [manuscript step] | `Rep(U)` rigid and semisimple + `C₂`-cofinite + CFT type ⇒ `U` strongly rational |
| `E_dmno` | ProofMapConcrete.lean:209 (doc ProofMap.lean:251–256) | [external] | `H` holomorphic ⇒ Lagrangian ⇒ `Rep(U) ≃ Z(𝓕)`, `𝓕 = Rep(U)_H`; concrete conjuncts: the dimensions of `𝓕` form a positive duality-invariant character, `∑ d_i² = 3s`, `d_X = s - 1` |
| `E_gsy` | ProofMapConcrete.lean:211 (doc ProofMap.lean:334–338) | [external] | An untwisted `HI(ℤ/3)` category with the twelve twists of line 4053 has the standard Haagerup modular data (opaque node `modularData`) |
| `E_netCR` | ProofMapConcrete.lean:213 (doc ProofMap.lean:359–362) | [external] | `U` strongly rational, unitary, CFT type ⇒ the net `𝒩_U` is completely rational |
| `L_reconstruction` | ProofMapConcrete.lean:214 (doc ProofMap.lean:374–379) | [manuscript step] | A3: reconstruction sends the irreducible `𝒩_U` sectors injectively to unitarizable simple `U`-modules (concrete: `recon` injective, values unitarizable) |
| `L_annulus` | ProofMapConcrete.lean:216 (doc ProofMap.lean:384–393) | [manuscript step] | A1: pairwise annulus compatibility of the bounded-insertion and smeared-field nets |
| `E_tener` | ProofMapConcrete.lean:217 (doc ProofMap.lean:394–395) | [external] | Strong unitarity + annulus compatibility ⇒ `U` completely unitary (positivity of fusion forms) |
| `L_boundaryUnitary` | ProofMapConcrete.lean:218 (doc ProofMap.lean:397–400) | [manuscript step] | `U` completely unitary ⇒ `𝓕 = Rep(U)_H` (all modules) is a unitary fusion category |
| `E_izumi` | ProofMapConcrete.lean:219 (doc ProofMap.lean:401–403) | [external] | A unitary fusion category with ring `HI(ℤ/3)` and untwisted pointed part is `𝓗₂` or `𝓗₃` |
| `E_moritaCenter` | ProofMapConcrete.lean:220 (doc ProofMap.lean:404–407) | [external] | `𝓕 ≃ 𝓗₂` or `𝓗₃` + Lagrangian center + complete unitarity ⇒ `Rep(U) ≃ Z(𝓗₃)` as unitary ribbon categories |
| `E_netCenter` | ProofMapConcrete.lean:222 (doc ProofMap.lean:408–409) | [external] | The same identification for the net: `Rep(𝒩_U) ≃ Z(𝓗₃)` |
| `E_netExtension` | ProofMapConcrete.lean:223 (doc ProofMap.lean:410–412) | [external] | The holomorphic net extension `𝒩_U ⊂ 𝓔₃` |
| `E_diagonal` | ProofMapConcrete.lean:224 (doc ProofMap.lean:413–416) | [external] | The diagonal full net with `Z = ∑ \|χ_i\|²` |
| `E_e8Extension` | ProofMapConcrete.lean:226 (doc ProofMap.lean:417–423) | [external] | The chosen `𝓗₃` extension `H′ ≅ V_{E₈}` and its defects |

## 5. Every hypothesis, grouped by tag

Each hypothesis is listed once, under its primary tag; secondary tags are in the last column.  Bundles (an input whose content is a structure) are marked and their fields follow as separate entries.  `AutExpansion` and `InductionFormulas` occur twice (for the boundary category `𝓕`, data `B`, and for the net category `𝓕_net`, data `Bn`); their fields are listed for each use, as they are separate hypotheses.


### 5.1 [external] (98 entries covering 113 Lean hypotheses; 8 bundles)


#### Carpi–Kawahigashi–Longo–Weiner (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.E_cklw529` | ProofMapConcrete.lean:207 (doc ProofMap.lean:178–184) | A PCT-stable strongly generated subalgebra of the unitary lattice VOA is a simple unitary VOA of CFT type with `c = 8`, `U₂ = S₂`, `U₃ = S₃`; concrete conjunct `dim U₀ = 1` | CKLW Prop. 5.29; cor:initial-grades (228); `U₂ = S₂, U₃ = S₃` formalized in `InitialGrades.cor_initial_grades_of_certificates` | — | [manuscript step] cor:initial-grades content |

#### Davydov–Müger–Nikshych–Ostrik (2 hypotheses)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.E_dmno` | ProofMapConcrete.lean:209 (doc ProofMap.lean:251–256) | `H` holomorphic ⇒ Lagrangian ⇒ `Rep(U) ≃ Z(𝓕)`, `𝓕 = Rep(U)_H`; concrete conjuncts: the dimensions of `𝓕` form a positive duality-invariant character, `∑ d_i² = 3s`, `d_X = s - 1` | DMNO §4; positive spherical structure from character asymptotics; extension dimension identities (3243–3260) | — | [manuscript step] positivity and dimension identities |
| 2 | `hadj` | ProofMapConcrete.lean:464 | conditional on `lagrangianCenter`: `rank 𝓕 = dim End_𝒞(H) = ∑_l mult(l)²` | DMNO adjunction `FI(𝟙) = ⊕ a ⊗ a*` with Schur (3263–3268) | — | [standard] Schur |

#### Gannon–Schopieray–Yadav (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.E_gsy` | ProofMapConcrete.lean:211 (doc ProofMap.lean:334–338) | An untwisted `HI(ℤ/3)` category with the twelve twists of line 4053 has the standard Haagerup modular data (opaque node `modularData`) | GSY Theorem A(2)/5.1 (lines 4065–4066) | — |  |

#### Tener / Longo (nets) (2 hypotheses)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.E_netCR` | ProofMapConcrete.lean:213 (doc ProofMap.lean:359–362) | `U` strongly rational, unitary, CFT type ⇒ the net `𝒩_U` is completely rational | Tener [TenFusion] Cor. 4.24; [TenFields] Prop. 7.5, Lemma 7.6; Longo Thm 24 (4271–4279) | — |  |
| 2 | `RI.E_tener` | ProofMapConcrete.lean:217 (doc ProofMap.lean:394–395) | Strong unitarity + annulus compatibility ⇒ `U` completely unitary (positivity of fusion forms) | Tener, Def. 2.18, Cor. 4.6 | — |  |

#### Izumi (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.E_izumi` | ProofMapConcrete.lean:219 (doc ProofMap.lean:401–403) | A unitary fusion category with ring `HI(ℤ/3)` and untwisted pointed part is `𝓗₂` or `𝓗₃` | Izumi Def. 2.7, Thms 5.9, 9.1; `H²(ℤ/3, ℂˣ) = 0` proved (`Fusion.units_cube_surjective`) | — |  |

#### Grossman–Snyder / DMNO / Reutter (2 hypotheses)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.E_moritaCenter` | ProofMapConcrete.lean:220 (doc ProofMap.lean:404–407) | `𝓕 ≃ 𝓗₂` or `𝓗₃` + Lagrangian center + complete unitarity ⇒ `Rep(U) ≃ Z(𝓗₃)` as unitary ribbon categories | Grossman–Snyder Thm 1.4; DMNO; Reutter Thm 5 | — |  |
| 2 | `RI.E_netCenter` | ProofMapConcrete.lean:222 (doc ProofMap.lean:408–409) | The same identification for the net: `Rep(𝒩_U) ≃ Z(𝓗₃)` | Cor. cor:analytic-net-haagerup | — |  |

#### Longo–Rehren / Müger / DMNO (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.E_netExtension` | ProofMapConcrete.lean:223 (doc ProofMap.lean:410–412) | The holomorphic net extension `𝒩_U ⊂ 𝓔₃` | Longo–Rehren Thm 4.9; Longo Thm 24; DMNO Cor. 4.1, Prop. 4.4; Müger §§4, 8 | — |  |

#### Rehren (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.E_diagonal` | ProofMapConcrete.lean:224 (doc ProofMap.lean:413–416) | The diagonal full net with `Z = ∑ \|χ_i\|²` | Rehren Thm 1.4, Prop. 1.5, Cor. 1.6 (lines 5089–5091) | — |  |

#### HKL / Gui / ABD / Dong–Mason (E₈) (2 hypotheses)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.E_e8Extension` | ProofMapConcrete.lean:226 (doc ProofMap.lean:417–423) | The chosen `𝓗₃` extension `H′ ≅ V_{E₈}` and its defects | DMNO; Huang–Kirillov–Lepowsky Thms 3.2–3.6; Gui Q-systems; Abe–Buhl–Dong Prop. 5.2; Dong–Mason Thm 1; Müger | — |  |
| 2 | `[IsCommMonObj Ah.X]` | ProofMapConcrete.lean:455 | `H/B` is a commutative algebra in `Rep(B)` (the extension `B ⊂ H` of VOAs gives a commutative algebra) | Huang–Kirillov–Lepowsky; line 3331 | — |  |

#### Bischoff–Jones (6 hypotheses; 2 bundles)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `BoundaryInputs.hBJ` *(bundle; content listed separately)* | ProofMapConcrete.lean:157 | Conditional on `certDiscriminant`: the order-3 automorphism `g` of `H/B` and `g⁻¹` have Bischoff–Jones expansions `x, y` (`AutExpansion`, sub-entries) | Lemma lem:automorphisms-invertibles (3273–3296); BJ Lemma 3.1, Cor. 3.4 | — |  |
| 2 | `AutExpansion[B].hxy` | ProofMapConcreteBoundary.lean:538 | composition is fusion multiplication: `x · y = [𝟙]` (`g ∘ g⁻¹ = id`) | BJ Lemma 3.1, Cor. 3.4 | — |  |
| 3 | `AutExpansion[B].hxx` | ProofMapConcreteBoundary.lean:540 | `x · x = y` (`g ∘ g = g⁻¹`) | BJ Lemma 3.1, Cor. 3.4 | — |  |
| 4 | `AutExpansion[Bn].hxy` | ProofMapConcreteBoundary.lean:538 | composition is fusion multiplication: `x · y = [𝟙]` (`g ∘ g⁻¹ = id`) | BJ Lemma 3.1, Cor. 3.4 | — |  |
| 5 | `AutExpansion[Bn].hxx` | ProofMapConcreteBoundary.lean:540 | `x · x = y` (`g ∘ g = g⁻¹`) | BJ Lemma 3.1, Cor. 3.4 | — |  |
| 6 | `BoundaryInputs.bj` | ProofMapConcrete.lean:177 | At rank six: `End_𝒞(H) ≅ K₀(𝓕) ⊗ ℂ` as unital ℂ-algebras (`BJIso`, Fusion/EndHSchur.lean:209) | BJ Cor. 3.4 with Lemma 3.1 (line 3799) | — |  |
| 7 | `NetInputs.iso` | ProofMapConcreteNetCount.lean:82 | same conditions: `K₀(𝓕_net) ⊗ ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` (`FusionAlgebraIso`) | BJ Cor. 3.4; eq:analytic-end-algebra (the `End(1⊕X⊕2Y)` step is `Fusion.endHIsoOfSimple`) | — | [manuscript step] |
| 8 | `NetInputs.bj` *(bundle; content listed separately)* | ProofMapConcreteNetCount.lean:86 | conditional on `certDiscriminant`: BJ expansions of the lattice automorphism on the net inclusion (`AutExpansion[Bn]`, sub-entries above) | lines 4355–4358 | — |  |

#### Ostrik / Ng–Schauenburg / Vafa (20 hypotheses; 2 bundles)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `BoundaryInputs.hInd` *(bundle; content listed separately)* | ProofMapConcrete.lean:183 | For the rank-six ring with multiplicity `m`: the evaluated center-induction formulas (`InductionFormulas`, sub-entries) | Lemma lem:rank6-induction (3842–3914) | — |  |
| 2 | `InductionFormulas[B].codegree_X` | ProofMapConcreteBoundary.lean:168 | `d_X = Dim 𝓕 / f` for the formal codegree `f = 3 + 3δ⁻²` | Ostrik Thms 2.5, 2.13 | — |  |
| 3 | `InductionFormulas[B].codegree_Y` | ProofMapConcreteBoundary.lean:171 | `d_Y = Dim 𝓕 / 3` | Ostrik; line 3864 | — | [manuscript step] `3` is the codegree of the 2-dim representation |
| 4 | `InductionFormulas[B].rootC` | ProofMapConcreteBoundary.lean:173 | the twists of `C₀, C₁, C₂` are roots of unity | Vafa | — |  |
| 5 | `InductionFormulas[B].root` | ProofMapConcreteBoundary.lean:175 | the residual twists are roots of unity | Vafa | — |  |
| 6 | `InductionFormulas[B].nu1_a` | ProofMapConcreteBoundary.lean:182 | `∑ d_{C_j} θ_{C_j} = Dim 𝓕 · ν₁(a) = 0` | Ng–Schauenburg Thm 4.1 | — | [manuscript step] `I(a) = ∑ C_j` |
| 7 | `InductionFormulas[B].nu3_a` | ProofMapConcreteBoundary.lean:185 | `∑ d_{C_j} θ_{C_j}³ = Dim 𝓕 · ν₃(a)` | Ng–Schauenburg Thm 4.1 | — | [manuscript step] |
| 8 | `InductionFormulas[B].nu1_ρ` | ProofMapConcreteBoundary.lean:189 | `∑ [I(ρ):Z] d_Z θ_Z = 0` (with `θ_X = θ_Y = 1`) | Ng–Schauenburg Thm 4.1 | — | [manuscript step] decomposition of `I(ρ)` |
| 9 | `InductionFormulas[B].nu2_ρ` | ProofMapConcreteBoundary.lean:194 | `∑ [I(ρ):Z] d_Z θ_Z² = Dim 𝓕 · ν₂(ρ)` | Ng–Schauenburg Thm 4.1 | — | [manuscript step] |
| 10 | `InductionFormulas[B].eps` | ProofMapConcreteBoundary.lean:199 | the second Frobenius–Schur indicator `ν₂(ρ) = ±1` | standard FS-indicator theory | — |  |
| 11 | `InductionFormulas[B].center_dim` | ProofMapConcreteBoundary.lean:202 | `Dim Z(𝓕) = (Dim 𝓕)²`, summed over the center simples `𝟙, X, Y, C_j, Z_j` | lines 3897–3904 | — | [manuscript step] completeness of the list |
| 12 | `InductionFormulas[Bn].codegree_X` | ProofMapConcreteBoundary.lean:168 | `d_X = Dim 𝓕 / f` for the formal codegree `f = 3 + 3δ⁻²` | Ostrik Thms 2.5, 2.13 | — |  |
| 13 | `InductionFormulas[Bn].codegree_Y` | ProofMapConcreteBoundary.lean:171 | `d_Y = Dim 𝓕 / 3` | Ostrik; line 3864 | — | [manuscript step] `3` is the codegree of the 2-dim representation |
| 14 | `InductionFormulas[Bn].rootC` | ProofMapConcreteBoundary.lean:173 | the twists of `C₀, C₁, C₂` are roots of unity | Vafa | — |  |
| 15 | `InductionFormulas[Bn].root` | ProofMapConcreteBoundary.lean:175 | the residual twists are roots of unity | Vafa | — |  |
| 16 | `InductionFormulas[Bn].nu1_a` | ProofMapConcreteBoundary.lean:182 | `∑ d_{C_j} θ_{C_j} = Dim 𝓕 · ν₁(a) = 0` | Ng–Schauenburg Thm 4.1 | — | [manuscript step] `I(a) = ∑ C_j` |
| 17 | `InductionFormulas[Bn].nu3_a` | ProofMapConcreteBoundary.lean:185 | `∑ d_{C_j} θ_{C_j}³ = Dim 𝓕 · ν₃(a)` | Ng–Schauenburg Thm 4.1 | — | [manuscript step] |
| 18 | `InductionFormulas[Bn].nu1_ρ` | ProofMapConcreteBoundary.lean:189 | `∑ [I(ρ):Z] d_Z θ_Z = 0` (with `θ_X = θ_Y = 1`) | Ng–Schauenburg Thm 4.1 | — | [manuscript step] decomposition of `I(ρ)` |
| 19 | `InductionFormulas[Bn].nu2_ρ` | ProofMapConcreteBoundary.lean:194 | `∑ [I(ρ):Z] d_Z θ_Z² = Dim 𝓕 · ν₂(ρ)` | Ng–Schauenburg Thm 4.1 | — | [manuscript step] |
| 20 | `InductionFormulas[Bn].eps` | ProofMapConcreteBoundary.lean:199 | the second Frobenius–Schur indicator `ν₂(ρ) = ±1` | standard FS-indicator theory | — |  |
| 21 | `InductionFormulas[Bn].center_dim` | ProofMapConcreteBoundary.lean:202 | `Dim Z(𝓕) = (Dim 𝓕)²`, summed over the center simples `𝟙, X, Y, C_j, Z_j` | lines 3897–3904 | — | [manuscript step] completeness of the list |
| 22 | `NetInputs.ind` *(bundle; content listed separately)* | ProofMapConcreteNetCount.lean:103 | the evaluated center-induction formulas for `𝓕_net` (`InductionFormulas[Bn]`, sub-entries above) | lines 4410–4424 | — |  |

#### Dong–Lin–Ng (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `CharacterInputs.fin` | ProofMapConcreteCharacters.lean:304 | conditional on `stronglyRational`: the modular representation of `Rep(U)` has finite image | DLN Theorem I | — |  |

#### Zhu / Huang (modularity) (5 hypotheses)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `CharacterInputs.T_diag` | ProofMapConcreteCharacters.lean:307 | `σ(T)` is diagonal with entries `e^{2πi(h - c/24)}` (`c = 8`) | Huang | — |  |
| 2 | `CharacterInputs.S_ne` | ProofMapConcreteCharacters.lean:311 | Zhu’s `S` is the categorical `S`, so `S_{0,c₁} = d_{c₁}/D ≠ 0` | Huang | — |  |
| 3 | `CharacterInputs.hol` | ProofMapConcreteCharacters.lean:313 | the twelve characters are holomorphic on `ℍ` | Zhu | — |  |
| 4 | `CharacterInputs.cov` | ProofMapConcreteCharacters.lean:315 | the character vector is `σ`-covariant | Zhu, Huang | — |  |
| 5 | `CharacterInputs.summ` | ProofMapConcreteCharacters.lean:323 | absolute convergence of the characters on `ℍ` | Zhu | — |  |

#### Evans–Gannon (14 hypotheses; 1 bundle)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `CharacterInputs.EG` *(bundle; content listed separately)* | ProofMapConcreteCharacters.lean:337 | conditional on `modularData`: the Evans–Gannon fundamental matrix columns `Ξ₀`, `Ξ₃` (`EvansGannon`, sub-entries) | EG §§1.4, 2.4, eq. (2.7) (lines 4161–4170) | — |  |
| 2 | `EvansGannon.hol₀, hol₃` | ProofMapConcreteCharacters.lean:260–261 | `Ξ₀`, `Ξ₃` are holomorphic | Evans–Gannon §§1.4, 2.4 | — |  |
| 3 | `EvansGannon.cov₀, cov₃` | ProofMapConcreteCharacters.lean:262–265 | `Ξ₀`, `Ξ₃` are `σ`-covariant | Evans–Gannon §§1.4, 2.4 | — |  |
| 4 | `EvansGannon.q₀, q₃` | ProofMapConcreteCharacters.lean:266–269 | `q`-expansions in the exponents `n + t_l - 1/3` | Evans–Gannon §§1.4, 2.4 | — |  |
| 5 | `EvansGannon.sum₀, sum₃` | ProofMapConcreteCharacters.lean:270–273 | absolute convergence at every height | Evans–Gannon §§1.4, 2.4 | — |  |
| 6 | `EvansGannon.pp₃_o, pp₃, pp₃_d3` | ProofMapConcreteCharacters.lean:274–276 | principal part of `Ξ₃`: `q^{-7/39}` in the `d₃` coordinate only | Evans–Gannon §§1.4, 2.4 | — |  |
| 7 | `EvansGannon.vac₀, vac₃` | ProofMapConcreteCharacters.lean:277–278 | the `q^{2/3}` coefficients of the vacuum coordinates are `6` and `13` | Evans–Gannon §§1.4, 2.4 | — |  |
| 8 | `EvansGannon.table` | ProofMapConcreteCharacters.lean:279 | `Ξ₀` has the lowest weights and top dimensions of the table at line 4178 | Evans–Gannon §§1.4, 2.4 | — |  |

#### Dong–Lam–Yamada / Linshaw (3 hypotheses)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `PF13Inputs.row'` | ProofMapConcretePF13.lean:99 | `K(𝔰𝔩₂,13)` satisfies the same 16 one-sided OPE identities at `c = 8/5` | DLY decoupling; Linshaw recursive first rows | — |  |
| 2 | `PF13Inputs.simple'` | ProofMapConcretePF13.lean:111 | `K(𝔰𝔩₂,13)` is simple | standard (parafermion literature) | — |  |
| 3 | `PF13Inputs.gen'` | ProofMapConcretePF13.lean:115 | `K(𝔰𝔩₂,13)` is generated by `L′, a′` | DLY; Linshaw | — |  |

#### Abe–Buhl–Dong / regularity of the factors (5 hypotheses; 1 bundle)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `hfac` | ProofMapConcrete.lean:485–487 | conditional on `pf13Factor`: every orbit point has symmetric zero mode whose eigenvectors of energy `> D` lie in `C₂(U)` (`FactorEnergy`) | Abe–Buhl–Dong Prop. 5.2; lemma lem:positive-c2 (2846–2888) | — | [manuscript step] complete reducibility of `U`, `C_{2,A}(U) ⊆ C₂(U)` |
| 2 | `hnonneg` | ProofMapConcrete.lean:488–490 | conditional on `pf13Factor`: the four factors have nonnegative lowest weights, zero only for the vacuum (`factorNonneg`, an unmodelled predicate) | lines 2719–2721 (no citation in the manuscript) | — |  |
| 3 | `VacuumInputs.reg` *(bundle; content listed separately)* | ProofMapConcreteVacuum.lean:156 | conditional on `factorNonneg`: for every orbit point `z` and weak `U`-module `M`, `Ω_{A_z}(M) ≅ ⊕` tops on which `z_(1)` acts by lowest weights `≥ 0` and `z_(0)` kills the weight-zero tops (`ComponentTops`, sub-entries) | proof of lem:compatible-top (2903–2907), vacuum-top step (2951–2954); regularity of the factors (Zhu algebra; uncited in the manuscript) | — |  |
| 4 | `ComponentTops.eqv` | Regularity/VacuumTopZero.lean:292 | `Ω_{A′}(M) ≅ ⨁ₖ T k`, the tops of the simple ordinary summands of `M↓A′` | regularity of `A′` | — |  |
| 5 | `ComponentTops.wt_nonneg` | Regularity/VacuumTopZero.lean:290 | the lowest weights of the factor are `≥ 0` | line 2719 | — |  |
| 6 | `ComponentTops.Lm1_vac` | Regularity/VacuumTopZero.lean:295 | `L^{A′}(-1) = e_(0)` kills the weight-zero tops (vacuum unique of weight 0, `L(-1)𝟏 = 0`) | lines 2951–2954 | — |  |

#### Dong–Li–Mason (complete reducibility) (12 hypotheses)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `BranchBInputs.stable` | ProofMapConcreteBranching.lean:164 | conditional on `stronglyRational`: the summands `M_j` are `U`-submodules (zero modes preserve their weight spaces) | complete reducibility over a regular VOA (line 3213) | — |  |
| 2 | `BranchBInputs.disj` | ProofMapConcreteBranching.lean:166 | conditional on `stronglyRational`: the sum `⊕ M_j` is direct | complete reducibility over a regular VOA (line 3213) | — |  |
| 3 | `BranchBInputs.top` | ProofMapConcreteBranching.lean:169 | conditional on `stronglyRational`: a summand of lowest weight one has nonzero top | complete reducibility over a regular VOA (line 3213) | — |  |
| 4 | `BranchBInputs.sum` | ProofMapConcreteBranching.lean:171 | conditional on `stronglyRational`: `B₁ = ⊕_j (M_j)₁` | complete reducibility over a regular VOA (line 3213) | — |  |
| 5 | `SectorInputs[I₁ (J)].stable` | ProofMapConcreteBranchH.lean:83 | conditional on `stronglyRational`: the summands are `U`-submodules | complete reducibility; line 3236 | — |  |
| 6 | `SectorInputs[I₁ (J)].disj` | ProofMapConcreteBranchH.lean:85 | conditional on `stronglyRational`: the sum is direct | complete reducibility; line 3236 | — |  |
| 7 | `SectorInputs[I₁ (J)].top` | ProofMapConcreteBranchH.lean:88 | conditional on `stronglyRational`: lowest weight one ⇒ nonzero top | complete reducibility; line 3236 | — |  |
| 8 | `SectorInputs[I₁ (J)].sum` | ProofMapConcreteBranchH.lean:90 | conditional on `stronglyRational`: `J₁ = ⊕ (M_j)₁` | complete reducibility; line 3236 | — |  |
| 9 | `SectorInputs[I₂ (J²)].stable` | ProofMapConcreteBranchH.lean:83 | conditional on `stronglyRational`: the summands are `U`-submodules | complete reducibility; line 3236 | — |  |
| 10 | `SectorInputs[I₂ (J²)].disj` | ProofMapConcreteBranchH.lean:85 | conditional on `stronglyRational`: the sum is direct | complete reducibility; line 3236 | — |  |
| 11 | `SectorInputs[I₂ (J²)].top` | ProofMapConcreteBranchH.lean:88 | conditional on `stronglyRational`: lowest weight one ⇒ nonzero top | complete reducibility; line 3236 | — |  |
| 12 | `SectorInputs[I₂ (J²)].sum` | ProofMapConcreteBranchH.lean:90 | conditional on `stronglyRational`: `J₁ = ⊕ (M_j)₁` | complete reducibility; line 3236 | — |  |

#### RLYG (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `SignInputs.rlyg` | ProofMapConcreteBranching.lean:359 | a finite-order automorphism of `𝔢₆ ⊕ 𝔞₂` fixes a toral subalgebra of dimension `≥ orbits(σ) + orbits(τ)` for diagram automorphisms `σ` of `E₆`, `τ` of `A₂` | RLYG §5.2 (line 3309) | — |  |

#### Huang / Miyamoto (finite length) (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `VacuumInputs.noNeg` | ProofMapConcreteVacuum.lean:163 | conditional on `c2Cofinite` and the (proved) nonnegativity of lowest weights: a grading-restricted generalized module has no generalized `L(0)`-weight `-m`, `m ≥ 1` | Huang; Miyamoto (2959–2961) | — | [standard] composition factors are ordinary |

#### McRae / Etingof–Penneys (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `hEP` | ProofMapConcrete.lean:473–474 | conditional on `c2Cofinite`, `initialGrades`: if `𝟙` is projective, every object of `Rep(U)` has a dual | McRae §§2.3, 3; Etingof–Penneys Thm 1.1; growth/non-negligibility 2992–3006 | — | [manuscript step] lines 2992–3006 |

#### Larson (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RankFourInputs.larson` | ProofMapConcreteRankFour.lean:84 | conditional on `lagrangianCenter`: `m ∈ {0, 2, 3, 6}` | Larson Thm 1.1 | — |  |

#### EGO / HKL / Dong–Mason (m = 2) (1 hypothesis)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RankFourInputs.case2` | ProofMapConcreteRankFour.lean:93 | conditional on `lagrangianCenter`, `stronglyRational`, `initialGrades`, `VacuumNode`: for `m = 2`, `dim U₁ ≥ 16` | EGO Thm 7.1/Cor. 7.4; HKL; Dong–Mason Thm 1 (3364–3480); `dim 𝔢₈^{A₄} ≥ 16` proved | — | [manuscript step] twisted double identified with `Rep(U)` via `Z(𝓕) ≃ Rep(U)` (`lagrangianCenter`) |

#### Zhu / Huang (even-block modularity) (20 hypotheses; 2 bundles)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RankFourInputs.case3` *(bundle; content listed separately)* | ProofMapConcreteRankFour.lean:107 | conditional on `lagrangianCenter`, `stronglyRational`, `initialGrades`, `VacuumNode`, `BranchB`, `ν₃ = 1`: VOA-side data of one orientation for `m = 3` (`M3FirstVoa ∨ M3ReverseVoa`, sub-entries) | prop:near-group-current-obstructions (3482–3770); the center has the modular data of the near-group double (prop:m3-modular, ≈3451) | — | [manuscript step] choice of orientation; `Z(𝓕) ≃ Rep(U)` (`lagrangianCenter`) |
| 2 | `RankFourInputs.case6` *(bundle; content listed separately)* | ProofMapConcreteRankFour.lean:114 | same premises (including `lagrangianCenter`) for `m = 6`: `M6FirstVoa ∨ M6ReverseVoa` (Table 4 with the 6-dimensional swap-symmetric block `SθE6G6m`) | same | — | [manuscript step] choice of orientation; `Z(𝓕) ≃ Rep(U)` |
| 3 | `M3FirstVoa.hσS, hσT` | ProofMapConcreteRankFourVoa.lean:48–49 | Table 1, `d = 15 + A + 10B`: `σ(S)`, `σ(T)` are the explicit even-block matrices (Zhu modularity, Huang’s `S`, comparison with the categorical modular data) | Zhu; Huang | — |  |
| 4 | `M3FirstVoa.hVhol, hVcov` | ProofMapConcreteRankFourVoa.lean:51–52 | Table 1, `d = 15 + A + 10B`: the weight-zero even-block vector `V` is holomorphic and `σ`-covariant | Zhu; Huang | — |  |
| 5 | `M3FirstVoa.hsum` | ProofMapConcreteRankFourVoa.lean:57 | Table 1, `d = 15 + A + 10B`: absolute convergence of the expansion | Zhu | — |  |
| 6 | `M3ReverseVoa.hσS, hσT` | ProofMapConcreteRankFourVoa.lean:76–77 | Table 2, `d = 14 + 42A`: `σ(S)`, `σ(T)` are the explicit even-block matrices (Zhu modularity, Huang’s `S`, comparison with the categorical modular data) | Zhu; Huang | — |  |
| 7 | `M3ReverseVoa.hVhol, hVcov` | ProofMapConcreteRankFourVoa.lean:79–80 | Table 2, `d = 14 + 42A`: the weight-zero even-block vector `V` is holomorphic and `σ`-covariant | Zhu; Huang | — |  |
| 8 | `M3ReverseVoa.hsum` | ProofMapConcreteRankFourVoa.lean:86 | Table 2, `d = 14 + 42A`: absolute convergence of the expansion | Zhu | — |  |
| 9 | `M6FirstVoa.hσS, hσT` | ProofMapConcreteRankFourVoa.lean:103–104 | Table 3, `d = 8 + A`: `σ(S)`, `σ(T)` are the explicit even-block matrices (Zhu modularity, Huang’s `S`, comparison with the categorical modular data) | Zhu; Huang | — |  |
| 10 | `M6FirstVoa.hVhol, hVcov` | ProofMapConcreteRankFourVoa.lean:106–107 | Table 3, `d = 8 + A`: the weight-zero even-block vector `V` is holomorphic and `σ`-covariant | Zhu; Huang | — |  |
| 11 | `M6FirstVoa.hsum` | ProofMapConcreteRankFourVoa.lean:112 | Table 3, `d = 8 + A`: absolute convergence of the expansion | Zhu | — |  |
| 12 | `M6ReverseVoa.hσS, hσT` | ProofMapConcreteRankFourVoa.lean:128–129 | Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`: `σ(S)`, `σ(T)` are the explicit even-block matrices (Zhu modularity, Huang’s `S`, comparison with the categorical modular data) | Zhu; Huang | — |  |
| 13 | `M6ReverseVoa.hVhol, hVcov` | ProofMapConcreteRankFourVoa.lean:131–132 | Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`: the weight-zero even-block vector `V` is holomorphic and `σ`-covariant | Zhu; Huang | — |  |
| 14 | `M6ReverseVoa.hsum` | ProofMapConcreteRankFourVoa.lean:137 | Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`: absolute convergence of the expansion | Zhu | — |  |

#### Kawahigashi–Longo / CKLW (nets) (3 hypotheses)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `NetInputs.dims` | ProofMapConcreteNetCount.lean:74 | conditional on `netCompletelyRational`: `𝓕_net` is `C*` (positive dual-invariant dimensions), finite index, `Dim 𝓕_net = 3s`, `d_X = s - 1` | Kawahigashi–Longo Prop. 2.3 (4334); lines 4334–4345 | — |  |
| 2 | `NetInputs.pointed` | ProofMapConcreteNetCount.lean:91 | conditional on `netCompletelyRational` and rank six: a pointed `𝓕_net` would give a finite-order automorphism `g` of `B` with `B^g = U` | CKLW Thm 6.9, Prop. 7.6, Thm 7.5; index multiplicativity (4362–4373) | — | [manuscript step] index-two extensions 4366–4370 |
| 3 | `NetInputs.count` | ProofMapConcreteNetCount.lean:107 | conditional on `netCompletelyRational`: `#Sec = 6 + #κ` (Lagrangian-algebra theorem and exhaustion of the center simples) | line 4426; eq:analytic-center-dimensions | — | [manuscript step] exhaustion |

#### Dong / Dong–Lepowsky (lattice modules) (6 hypotheses)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `UntwistedInputs.hSchur` | ProofMapConcreteUntwisted.lean:112 | conditional on `certDiscriminant`: the nine lattice modules `S v` are simple, pairwise non-isomorphic, `End = ℂ` | Dong (lattice VOA modules) | — |  |
| 2 | `UntwistedInputs.hfusion` | ProofMapConcreteUntwisted.lean:115 | `S v ⊗ S w ≅ S (v + w)` | Dong–Lepowsky fusion rules | — |  |
| 3 | `UntwistedInputs.hunitS` | ProofMapConcreteUntwisted.lean:120 | `S (0, 0) ≅ 𝟙` (the vacuum module `B`) | Dong | — |  |
| 4 | `UntwistedInputs.hss` | ProofMapConcreteUntwisted.lean:131 | `Rep(B)` is semisimple and pointed: every object is a finite sum of the nine `S v` | Dong | — |  |
| 5 | `UntwistedInputs.hθ` | ProofMapConcreteUntwisted.lean:140 | conditional on `certDiscriminant`: the self-braidings of the three invertibles `S (a, -a)` on `L₋` are trivial (`q = 0` on the isotropic line: trivial twists) | lines 3335–3340; braiding of lattice VOA modules | — |  |
| 6 | `[BraidedCategory Cr]` | ProofMapConcrete.lean:451 | `Rep(B)` is braided (the braiding of lattice VOA modules; Huang for the module category of a rational VOA) | lines 3335–3340 | — |  |

### 5.2 [certificate] (58 entries covering 73 Lean hypotheses; 1 bundles)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.C_finiteClosure` *(bundle; content listed separately)* | ProofMapConcrete.lean:202 (node ProofMapProperness.lean:69, def ProofMapProperness.lean:39) | The finite closure certificates: `LowerCertificate D`, a Gate 4 certificate with a Gate 5 certificate, nilpotence of raising/lowering words of length 25 on `S₃`, and `ω ∈ S₂`, `u ∈ S₂`, `S₂ ≤ U` (sub-entries below) | cert:initial (2023), cert:lower (2253), Gates 4/5 (2264–2265, sec:gate4 2268, sec:gate5 2430), ledger sec:ledger (5236) | partly, modulo `FLMBorcherds`: the last three conjuncts (`minimalGeneration_latticeD`, Lattice/S2Link.lean:132) and the nineteen `LowerCertificate` fields `KK0`, `ω_mem`, `KS₂0`, `KS₂1`, `TK`, `KmK`, `hL_q`, `eL_q`, `fL_q`, `hR_qp`, `hR_q0`, `hR_qm`, `eR_qp`, `eR_q0`, `eR_qm`, `fR_qp`, `fR_q0`, `fR_qm`, `L2_P₄` for `latticeDP` (Lattice/P4Link.lean:93) are theorems, discharged in `lattice_proof_map` (`certFiniteClosure_latD`, ProofMapLattice.lean:360); the other 7 `LowerCertificate` fields (`LowerRest`, ProofMapLattice.lean:137), Gates 4/5 and nilpotence are not proved (`LatticeClosureInputs`, ProofMapLattice.lean:152).  `S₂` is exactly the closure, all 524 closure relations (`S2span_eq_closureSpace`, Lattice/S2Closure.lean:179); `dim S₂ = 120` (`finrank_S2span`, Lattice/S2Link.lean:102) is proved but not needed by the node |  |
| 2 | `RI.C_dimensions` | ProofMapConcrete.lean:203 (node ProofMapProperness.lean:70–71) | `dim K = 6`, `dim B₁ = 86`, and `K` is spanned by two commuting standard 𝔰𝔩₂-triples (`IsSl2SumSpan`) | cert:initial (2023–2030); `E₆ ⊕ A₂` lattice: 8 + 72 + 6 = 86 | **proved for `latticeD` modulo `FLMBorcherds`** (`certDimensions_latticeD`, Lattice/S2Link.lean:140; `certDimensions_lattice`, Lattice/VOA.lean:320); discharged in `lattice_proof_map` (`certDimensions_latD`, ProofMapLattice.lean:369) |  |
| 3 | `RI.C_pct` | ProofMapConcrete.lean:204 (node ProofMap.lean:44–45, opaque) | The exact PCT certificate: the transported PCT involution `θ_g` preserves `S₂` | cert:initial (2024), line 2604; transport `θ_g = gθg⁻¹` (1979–1992) | `θ_g S₂ = S₂` **proved for `latticeD`** (`certPCT_latticeD`, Lattice/PCTLink.lean:479) modulo `FLMBorcherds`; in `concrete_proof_map` the node `certPCT` is opaque; in `lattice_proof_map` it is `PCTCert` (ProofMapLattice.lean:108; `pctNodes`, ProofMapLattice.lean:114): `θ_g` mode-compatible (an antilinear automorphism) ∧ `θ_g S₂ = S₂` ∧ `θ_g U = U`, discharged in `lattice_proof_map` (`certPCT_latD`, ProofMapLattice.lean:443) from `pctModeCompatible` (Lattice/PCTModes.lean:470, a theorem with no hypotheses), `certPCT_latticeD` and `pctV_mem_U_latD` (ProofMapLattice.lean:380) |  |
| 4 | `RI.C_structural` | ProofMapConcrete.lean:205 (nodes ProofMapConcreteBranching.lean:139, ProofMapConcretePF13.lean:90, ProofMapConcreteRegularity.lean:104) | Conjunction of: the opaque part `R.certStructural` (Potts/PF13 fields, the core `T` and its spectral witnesses, cert:structural-inputs); `CurrentsIrreducible D u` (ProofMapConcreteBranching.lean:74: `B₁/K` has no proper nonzero subspace stable under the zero modes of `U`); `PF13SelfRow P.A P.L P.a P.b P.d P.c` (`c = 8/5`) (ProofMapConcretePF13.lean:51–67: the 16 one-sided OPE identities of the generated pair `L, a`); and the positive-stress identity `ω = ω_{A₁,₁} + (3403/4563) ω̄_{A₁,₃₉} + (25/6) p̄ + (25/26) z̄` (ProofMapConcreteRegularity.lean:52, 129) | cert:structural-inputs (2645–2682), eq:positive-stress (≈2688), currents 2677–2682, PF13 rows 2660–2667 | not proved |  |
| 5 | `RI.C_discriminant` | ProofMapConcrete.lean:206 (node ProofMap.lean:50, opaque) | The discriminant form of the lattice VOA `B` is `(ℤ/3)²` with `q(a,b) = (2a²+b²)/3`, and `H/B` lies on the isotropic line `L₊` | lines 3326–3333 | not proved (the arithmetic of `q` is in `Data/Weights`) |  |
| 6 | `LowerCertificate.KK0` | Properness/Setup.lean:276 | `K_(0) K ⊆ K` | cert:lower (2253–2266) | **proved for `latticeD`** (`KK0_latD`, ProofMapLattice.lean:201: the kernel-checked current brackets `left_sl2`, `right_sl2`, `left_right_commute`, Lattice/Relations.lean:42, for one order of each pair, skew symmetry for the other) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 7 | `LowerCertificate.KS₂0` | Properness/Setup.lean:277 | `K_(0) S₂ ⊆ S₂` | cert:lower (2253–2266) | **proved for `latticeD`** (`S2Closed_S2span`, Lattice/S2Closure.lean:170: the closure conditions of the minimal-generation record, half of `S2span_eq_closureSpace`; with `T x = x_(-2) 𝟏`) modulo `FLMBorcherds`; discharged in `lattice_proof_map` (`lowerCertificate_latD`, ProofMapLattice.lean:324) |  |
| 8 | `LowerCertificate.KS₂1` | Properness/Setup.lean:278 | `K_(1) S₂ ⊆ K` | cert:lower (2253–2266) | **proved for `latticeD`** (`KS21_latticeDP`, Lattice/KS21.lean:220: `K_(1) S₂ ⊆ K` on the 120 basis vectors of `S₂`, 720 kernel checks with `modeQRF`, about 320 s of kernel time) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 9 | `LowerCertificate.TK` | Properness/Setup.lean:279 | `T K ⊆ S₂` | cert:lower (2253–2266) | **proved for `latticeD`** (`S2Closed_S2span`, Lattice/S2Closure.lean:170: the closure conditions of the minimal-generation record, half of `S2span_eq_closureSpace`; with `T x = x_(-2) 𝟏`) modulo `FLMBorcherds`; discharged in `lattice_proof_map` (`lowerCertificate_latD`, ProofMapLattice.lean:324) |  |
| 10 | `LowerCertificate.KmK` | Properness/Setup.lean:280 | `K_(-1) K ⊆ S₂` | cert:lower (2253–2266) | **proved for `latticeD`** (`S2Closed_S2span`, Lattice/S2Closure.lean:170: the closure conditions of the minimal-generation record, half of `S2span_eq_closureSpace`; with `T x = x_(-2) 𝟏`) modulo `FLMBorcherds`; discharged in `lattice_proof_map` (`lowerCertificate_latD`, ProofMapLattice.lean:324) |  |
| 11 | `LowerCertificate.ω_mem` | Properness/Setup.lean:281 | `ω ∈ S₂` | cert:lower (2253–2266) | **proved for `latticeD`** (`omegaV_mem_S2span`, Lattice/S2Link.lean:79) modulo `FLMBorcherds`; discharged in `lattice_proof_map` (`lowerCertificate_latD`, ProofMapLattice.lean:324) |  |
| 12 | `LowerCertificate.S₂S₂0` | Properness/Setup.lean:282 | `(S₂)_(0) S₂ ⊆ S₃` | cert:lower (2253–2266) | not proved |  |
| 13 | `LowerCertificate.S₂S₂1` | Properness/Setup.lean:283 | `(S₂)_(1) S₂ ⊆ S₂` | cert:lower (2253–2266) | not proved |  |
| 14 | `LowerCertificate.S₂S₂2` | Properness/Setup.lean:284 | `(S₂)_(2) S₂ ⊆ K` | cert:lower (2253–2266) | not proved |  |
| 15 | `LowerCertificate.N₃_le_S₃` | Properness/Setup.lean:285 | `N₃ = K₋₁S₂ + TS₂ ⊆ S₃` | cert:lower (2253–2266) | not proved |  |
| 16 | `LowerCertificate.S₃_prov` | Properness/Setup.lean:286 | `S₃ ⊆ N₃ + (S₂)_(0)S₂` | cert:lower (2253–2266) | not proved |  |
| 17 | `LowerCertificate.P₄_prov` | Properness/Setup.lean:287 | `P₄ ⊆ (S₂)_(0)S₃ + N₄` | cert:lower (2253–2266) | not proved |  |
| 18 | `LowerCertificate.hL_q` | Properness/Setup.lean:288 | `H_L(0)` kills the triplet `P₄` | cert:lower (2253–2266) | **proved for `latticeDP`** (`hL_q_latticeDP`, Lattice/P4Link.lean:101) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 19 | `LowerCertificate.eL_q, fL_q` | Properness/Setup.lean:289–290 | `E_L(0)`, `F_L(0)` kill the triplet `P₄` | cert:lower (2253–2266) | **proved for `latticeDP`** (`eL_q_latticeDP`, `fL_q_latticeDP`, Lattice/P4Left.lean:113, Lattice/P4Left.lean:121) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 20 | `LowerCertificate.hR_qp, hR_q0, hR_qm` | Properness/Setup.lean:291–293 | `H_R(0) q_± = ±2 q_±`, `H_R(0) q₀ = 0` | cert:lower (2253–2266) | **proved for `latticeDP`** (`hR_qp_latticeDP`, `hR_q0_latticeDP`, `hR_qm_latticeDP`, Lattice/P4Link.lean:109, Lattice/P4Link.lean:117, Lattice/P4Link.lean:124) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 21 | `LowerCertificate.eR_qp` | Properness/Setup.lean:294 | `E_R(0) q₊ = 0` | cert:lower (2253–2266) | **proved for `latticeDP`** (`eR_qp_latticeDP`, Lattice/P4RERP.lean:306: kernel replay of `E_R(0) q₊ = 0`) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 22 | `LowerCertificate.eR_q0, eR_qm` | Properness/Setup.lean:295–296 | `E_R(0) q₀ = 2 q₊`, `E_R(0) q₋ = 2 q₀` | cert:lower (2253–2266) | **proved for `latticeDP`** (`eR_q0_latticeDP`, `eR_qm_latticeDP`, Lattice/P4RDerived.lean:59, Lattice/P4RDerived.lean:65: from `F_R(0)` on the triplet and the commutator formula `[E_R(0), F_R(0)] = H_R(0)`) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 23 | `LowerCertificate.fR_qp` | Properness/Setup.lean:297 | `F_R(0) q₊ = q₀` | cert:lower (2253–2266) | **proved for `latticeDP`** (`fR_qp_latticeDP`, Lattice/P4RFRP.lean:292: kernel replay of `F_R(0) q₊ = q₀` for the actual triplet; settles the normalization of `q₀`) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 24 | `LowerCertificate.fR_q0` | Properness/Setup.lean:298 | `F_R(0) q₀ = q₋` | cert:lower (2253–2266) | **proved for `latticeDP`** (`fR_q0_latticeDP`, Lattice/P4RFRZ.lean:288: kernel replay of `F_R(0) q₀ = q₋`) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 25 | `LowerCertificate.fR_qm` | Properness/Setup.lean:299 | `F_R(0) q₋ = 0` | cert:lower (2253–2266) | **proved for `latticeDP`** (`fR_qm_latticeDP`, Lattice/P4RFRM.lean:306: kernel replay of `F_R(0) q₋ = 0`) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 26 | `LowerCertificate.L1_P₄` | Properness/Setup.lean:300 | `L(1) P₄ ⊆ S₃` | cert:lower (2253–2266) | not proved |  |
| 27 | `LowerCertificate.L2_P₄` | Properness/Setup.lean:301 | `L(2) P₄ ⊆ S₂` | cert:lower (2253–2266) | **proved for `latticeDP`** (`L2_P4_latticeDP`, Lattice/P4RL2.lean:79: `L(2) q ∈ S₂` for the actual triplet; `S2Saved.S2savedSpan_eq`: the saved `r2_*` basis spans the replayed `S₂`) modulo `FLMBorcherds`; discharged in `lattice_proof_map` |  |
| 28 | `Gate4Certificate.highest, seed, singletSeed` *(witness data, not a hypothesis)* | Properness/Gate4.lean:129–131 | witness data: the highest-weight vectors of `S₂` and their seeds in `S₃` | Gate 4, sec:gate4 (2268–2343); ledger 5283–5300 | not proved |  |
| 29 | `Gate4Certificate.highest_S₂` | Properness/Gate4.lean:132 | highest vectors lie in `S₂` | Gate 4, sec:gate4 (2268–2343); ledger 5283–5300 | not proved |  |
| 30 | `Gate4Certificate.highest_eL, highest_eR` | Properness/Gate4.lean:133–134 | they are killed by `e_L`, `e_R` | Gate 4, sec:gate4 (2268–2343); ledger 5283–5300 | not proved |  |
| 31 | `Gate4Certificate.seed_S₃, singletSeed_S₃` | Properness/Gate4.lean:135–136 | seeds lie in `S₃` | Gate 4, sec:gate4 (2268–2343); ledger 5283–5300 | not proved |  |
| 32 | `Gate4Certificate.seed_identity` | Properness/Gate4.lean:137 | `a_(0) p ∈ N₄ + P₄` for seeds `p` (the projected identities) | Gate 4, sec:gate4 (2268–2343); ledger 5283–5300 | not proved |  |
| 33 | `Gate4Certificate.singlet_premise_L, singlet_premise_R` | Properness/Gate4.lean:138–141 | singlet recovery premises | Gate 4, sec:gate4 (2268–2343); ledger 5283–5300 | not proved |  |
| 34 | `Gate4Certificate.projected_residual` | Properness/Gate4.lean:142 | the projected residual identity | Gate 4, sec:gate4 (2268–2343); ledger 5283–5300 | not proved |  |
| 35 | `Gate4Certificate.raising_span` | Properness/Gate4.lean:144 | `S₃` is spanned by raisings of the seeds | Gate 4, sec:gate4 (2268–2343); ledger 5283–5300 | not proved |  |
| 36 | `Gate4Certificate.S₂_decomp` | Properness/Gate4.lean:146 | `S₂ ⊆ span(highest currents) + TK + K₋₁K + ℂω` | Gate 4, sec:gate4 (2268–2343); ledger 5283–5300 | not proved |  |
| 37 | `Gate5Certificate.e, charged, a₃, p₃, n₃, c₃, chargedSeeds` *(witness data, not a hypothesis)* | Properness/Gate5.lean:334–349 | witness data | Gate 5, sec:gate5 (2430–2600) | not proved |  |
| 38 | `Gate5Certificate.e_mem, charged_sub, highest_sub` | Properness/Gate5.lean:336–338 | the highest vectors are `e` and the charged ones | Gate 5, sec:gate5 (2430–2600) | not proved |  |
| 39 | `Gate5Certificate.bottom` | Properness/Gate5.lean:339 | each charged highest vector has a charged bottom (`ChargedBottom`) | Gate 5, sec:gate5 (2430–2600) | not proved |  |
| 40 | `Gate5Certificate.a₃_mem, p₃_mem` | Properness/Gate5.lean:344–345 | membership of the distinguished pair | Gate 5, sec:gate5 (2430–2600) | not proved |  |
| 41 | `Gate5Certificate.bottom₃, n₃_mem, c₃_ne` | Properness/Gate5.lean:346–348 | `a₃_(0) p₃ = c₃ q₋ + n₃` with `n₃ ∈ N₄`, `c₃ ≠ 0` | Gate 5, sec:gate5 (2430–2600) | not proved |  |
| 42 | `Gate5Certificate.chargedSeeds_S₃, chargedSeeds_mem` | Properness/Gate5.lean:350–351 | charged seeds in `S₃` with their identities | Gate 5, sec:gate5 (2430–2600) | not proved |  |
| 43 | `Gate5Certificate.lowering_span` | Properness/Gate5.lean:353 | `S₃` is spanned by lowerings of the charged seeds | Gate 5, sec:gate5 (2430–2600) | not proved |  |
| 44 | `certFiniteClosure: raising nilpotence` | ProofMapProperness.lean:41–42 | every word of length 25 in `e_L,(0)`, `e_R,(0)` kills `S₃` | Gate 4 (2268–2343) | not proved |  |
| 45 | `certFiniteClosure: lowering nilpotence` | ProofMapProperness.lean:43–44 | every word of length 25 in `f_L,(0)`, `f_R,(0)` kills `S₃` | Gate 5 | not proved |  |
| 46 | `certFiniteClosure: ω ∈ S₂, u ∈ S₂, S₂ ≤ U` | ProofMapProperness.lean:45 | `ω, u ∈ S₂` and `S₂ ⊆ ⟨K, ω, u⟩` (minimal generation) | cert:initial, minimal-generation record (2047–2055) | **proved for `latticeD` modulo `FLMBorcherds`** (`omegaV_mem_S2span`, `uV_mem_S2span`, `S2span_le_U`: `minimalGeneration_latticeD`, Lattice/S2Link.lean:132); discharged in `lattice_proof_map` (`certFiniteClosure_latD`, ProofMapLattice.lean:360) |  |
| 47 | `CharacterInputs.res₁` | ProofMapConcreteCharacters.lean:341 | the lattice modules `(0, ±1)` have weights in `1/3 + ℤ_{≥0}`; each simple summand has its lowest weight among them | lines 4198–4205 | — | [manuscript step] restriction bookkeeping |
| 48 | `CharacterInputs.top₁` | ProofMapConcreteCharacters.lean:345 | the lowest space of `(0, ±1)` has dimension 3 and is the sum of the tops of the weight-1/3 summands | lines 4198–4205 | — | [manuscript step] |
| 49 | `CharacterInputs.res₂` | ProofMapConcreteCharacters.lean:348 | the same for `(±1, 0)`, weights in `2/3 + ℤ_{≥0}` | lines 4198–4205 | — | [manuscript step] |
| 50 | `CharacterInputs.top₂` | ProofMapConcreteCharacters.lean:351 | the same for `(±1, 0)`, lowest space of dimension 27 | lines 4198–4205 | — | [manuscript step] |
| 51 | `PF13Inputs.rab` | ProofMapConcretePF13.lean:102 | the rows `a_(n) b` are common differential normal polynomials in both algebras | cert:structural-inputs item 2 (2660–2667) | not proved | [external] Linshaw (5.4), (5.7), (A.2) |
| 52 | `PF13Inputs.rad` | ProofMapConcretePF13.lean:105 | the same for the rows `a_(n) d` | cert:structural-inputs item 2 | not proved | [external] Linshaw |
| 53 | `M3FirstVoa.hfin` | ProofMapConcreteRankFourVoa.lean:47 | Table 1, `d = 15 + A + 10B`: the representation `σ` (pinned at the explicit Weil-type `S, T`) has finite image, a property of the explicit matrices alone (the Weil-type representation factors through some `SL(2, ℤ/N)`) | lines 3772–3774; the `SL₂` relations of the matrices are proved (`Theta.WeilSanityST3`, `sl2_relations_*`), finiteness of the generated group is not | not proved | [standard] Weil representations factor through a finite quotient |
| 54 | `M3ReverseVoa.hfin` | ProofMapConcreteRankFourVoa.lean:75 | Table 2, `d = 14 + 42A`: the representation `σ` (pinned at the explicit Weil-type `S, T`) has finite image, a property of the explicit matrices alone (the Weil-type representation factors through some `SL(2, ℤ/N)`) | lines 3772–3774; the `SL₂` relations of the matrices are proved (`Theta.WeilSanityST3`, `sl2_relations_*`), finiteness of the generated group is not | not proved | [standard] Weil representations factor through a finite quotient |
| 55 | `M6FirstVoa.hfin` | ProofMapConcreteRankFourVoa.lean:102 | Table 3, `d = 8 + A`: the representation `σ` (pinned at the explicit Weil-type `S, T`) has finite image, a property of the explicit matrices alone (the Weil-type representation factors through some `SL(2, ℤ/N)`) | lines 3772–3774; the `SL₂` relations of the matrices are proved (`Theta.WeilSanityST3`, `sl2_relations_*`), finiteness of the generated group is not | not proved | [standard] Weil representations factor through a finite quotient |
| 56 | `M6ReverseVoa.hfin` | ProofMapConcreteRankFourVoa.lean:127 | Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`: the representation `σ` (pinned at the explicit Weil-type `S, T`) has finite image, a property of the explicit matrices alone (the Weil-type representation factors through some `SL(2, ℤ/N)`) | lines 3772–3774; the `SL₂` relations of the matrices are proved (`Theta.WeilSanityST3`, `sl2_relations_*`), finiteness of the generated group is not | not proved | [standard] Weil representations factor through a finite quotient |
| 57 | `SectorInputs[I₁ (J)].cert` | ProofMapConcreteBranchH.lean:71 (def ProofMapConcreteBranchH.lean:61) | conditional on `certStructural`: `dim J₁ = 81` and `J₁` is irreducible under the zero modes of `U` | cert:structural-inputs; lines 3224–3230 | not proved |  |
| 58 | `SectorInputs[I₁ (J)].noZero` | ProofMapConcreteBranchH.lean:77 | the mixed sector starts at weight one: no summand of lowest weight 0 | line 3224 | not proved |  |
| 59 | `SectorInputs[I₂ (J²)].cert` | ProofMapConcreteBranchH.lean:71 (def ProofMapConcreteBranchH.lean:61) | conditional on `certStructural`: `dim J₁ = 81` and `J₁` is irreducible under the zero modes of `U` | cert:structural-inputs; lines 3224–3230 | not proved |  |
| 60 | `SectorInputs[I₂ (J²)].noZero` | ProofMapConcreteBranchH.lean:77 | the mixed sector starts at weight one: no summand of lowest weight 0 | line 3224 | not proved |  |
| 61 | `UntwistedInputs.hA` | ProofMapConcreteUntwisted.lean:118 | `H/B ≅ ⊕_{c ∈ ℤ/3} S (c, c)` (supported on `L₊`) | line 3331 | not proved |  |

### 5.3 [manuscript step] (44 entries covering 49 Lean hypotheses; 0 bundles)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `RI.L_rational` | ProofMapConcrete.lean:208 (doc ProofMap.lean:232–235) | `Rep(U)` rigid and semisimple + `C₂`-cofinite + CFT type ⇒ `U` strongly rational | Theorem thm:positive-stress-rationality (lines 3014–3032) | — | open L arrow |
| 2 | `RI.L_reconstruction` | ProofMapConcrete.lean:214 (doc ProofMap.lean:374–379) | A3: reconstruction sends the irreducible `𝒩_U` sectors injectively to unitarizable simple `U`-modules (concrete: `recon` injective, values unitarizable) | Prop. clm:analytic-reconstruction (4477–4577); external Henriques–Tener Thms 8.9, 9.5, Cor. 9.7, Rem. 9.8 | — | open L arrow; [external] Henriques–Tener |
| 3 | `RI.L_annulus` | ProofMapConcrete.lean:216 (doc ProofMap.lean:384–393) | A1: pairwise annulus compatibility of the bounded-insertion and smeared-field nets | Prop. clm:analytic-annulus (4621–4864); external Tener [TenFields], Henriques–Tener [HTAnn], [HTNet] | — | open L arrow; [external] Tener, Henriques–Tener |
| 4 | `RI.L_boundaryUnitary` | ProofMapConcrete.lean:218 (doc ProofMap.lean:397–400) | `U` completely unitary ⇒ `𝓕 = Rep(U)_H` (all modules) is a unitary fusion category | Lemma lem:analytic-unitary-all-modules (4901); external Gui Thms 2.21, 2.28, 3.13; algebraic core in Category/ | — | open L arrow; [external] Gui |
| 5 | `AutExpansion[B].hx` | ProofMapConcreteBoundary.lean:534 | `f ∗ f = f` for algebra automorphisms: the coefficients of `g` are `0` or `d_a` | lines 3283–3285 | — | [external] BJ: primitive convolution idempotents are `d_a[a]` |
| 6 | `AutExpansion[B].hy` | ProofMapConcreteBoundary.lean:536 | the same for `g⁻¹` | lines 3283–3285 | — | [external] BJ |
| 7 | `AutExpansion[Bn].hx` | ProofMapConcreteBoundary.lean:534 | `f ∗ f = f` for algebra automorphisms: the coefficients of `g` are `0` or `d_a` | lines 3283–3285 | — | [external] BJ: primitive convolution idempotents are `d_a[a]` |
| 8 | `AutExpansion[Bn].hy` | ProofMapConcreteBoundary.lean:536 | the same for `g⁻¹` | lines 3283–3285 | — | [external] BJ |
| 9 | `BoundaryInputs.simple1, simpleX, simpleY` | ProofMapConcrete.lean:166–168 | `𝟙 = U`, `X`, `Y` are simple objects of `𝒞 = Rep(U)` | eq:B-branching, eq:H-branching-fork (3219, 3233) | — |  |
| 10 | `BoundaryInputs.ne1X, ne1Y, neXY` | ProofMapConcrete.lean:171–173 | `𝟙, X, Y` are pairwise non-isomorphic (distinct lowest weights `0, 1, 1` and top dimensions `1, 80, 81`) | line 3237 | — |  |
| 11 | `BoundaryInputs.dec` | ProofMapConcrete.lean:180 | At rank six (`Y ≅ Y*`): `H ≅ 𝟙 ⊞ X ⊞ Y ⊞ Y` in `Rep(U)` | eq:rank-fork, lines 3795–3800 | — |  |
| 12 | `InductionFormulas[B].n_pos` | ProofMapConcreteBoundary.lean:177 | the residual central simples have `F(Z_j) = n_j ρ` with `n_j > 0` | lines 3870–3906 | — |  |
| 13 | `InductionFormulas[B].sum_b` | ProofMapConcreteBoundary.lean:179 | `b₀ + b₁ + b₂ = 3m` (adjunction `[F I(a) : ρ] = 3m`) | lines 3877–3880 | — |  |
| 14 | `InductionFormulas[Bn].n_pos` | ProofMapConcreteBoundary.lean:177 | the residual central simples have `F(Z_j) = n_j ρ` with `n_j > 0` | lines 3870–3906 | — |  |
| 15 | `InductionFormulas[Bn].sum_b` | ProofMapConcreteBoundary.lean:179 | `b₀ + b₁ + b₂ = 3m` (adjunction `[F I(a) : ρ] = 3m`) | lines 3877–3880 | — |  |
| 16 | `LI.ident (SimpleLabels.ident)` | ProofMapSimples.lean:50; arg ProofMapConcrete.lean:461 | conditional on `modularData`: the simple `U`-modules are exactly the twelve modules of the character table (`Simp ≃ Label`); with `LI.hw` it respects the twists (`θ = e^{2πiL(0)}`, `C.hw l ∈ t_l + ℤ`) | GSY consequence, line 4053 | — |  |
| 17 | `PF13Inputs.simple` | ProofMapConcretePF13.lean:109 | the vertex algebra generated by `L, a` inside `U` is simple (PCT stability) | lines 2838–2839 (CKLW-type, uncited) | — |  |
| 18 | `TopBoundInputs.mono` | ProofMapConcreteTopBound.lean:61 | conditional on `certStructural`, `pf13Factor`: the core-top charge multiplicities of every lowest space decrease away from 0 (finite-dimensional right 𝔰𝔩₂-representation) | lem:compatible-top (2890), core extension 3048–3079 | — | [certificate] core extension `A_L ⊂ U` |
| 19 | `TopBoundInputs.trace` | ProofMapConcreteTopBound.lean:66 | conditional on `positiveStress`, `certStructural`: eq:top-trace, `W_total = h · D` with the fourteen traces of eq:top-W | line 2949, table 3153–3162 | — |  |
| 20 | `SignInputs.sign` | ProofMapConcreteBranching.lean:369 | if `X` were invertible, `B = U ⊕ X` would be `ℤ/2`-graded with sign automorphism `g`, `B^g = U` | lines 3302–3305 | — |  |
| 21 | `RankFourInputs.rule` | ProofMapConcreteRankFour.lean:78 | at rank four with exactly three invertibles, `ρ ⊗ ρ = 𝟙 + a + a* + mρ` | lines 3356–3358 | — |  |
| 22 | `M3FirstVoa.hsupp` | ProofMapConcreteRankFourVoa.lean:56 | Table 1, `d = 15 + A + 10B`: `δc` is supported on `λ + ℕ` for the coset weights `λ` | lines 3700–3770 | — |  |
| 23 | `M3FirstVoa.hvac0` | ProofMapConcreteRankFourVoa.lean:61 | Table 1, `d = 15 + A + 10B`: `δc_{(0,0)}(0) = 0` | even-block reading of the characters, lines 3700–3770 | — |  |
| 24 | `M3FirstVoa.hpolarB, hpolarA` | ProofMapConcreteRankFourVoa.lean:62–63 | Table 1, `d = 15 + A + 10B`: `δc_{(1,0)}(1/7) = -B`, `δc_{(3,0)}(2/7) = 7 - A` (polar coefficients) | even-block reading of the characters, lines 3700–3770 | — |  |
| 25 | `M3FirstVoa.hother` | ProofMapConcreteRankFourVoa.lean:64 | Table 1, `d = 15 + A + 10B`: below `q^{1/3}`, `δc` vanishes except at `((0,0),0)`, `((1,0),1/7)`, `((3,0),2/7)` | even-block reading of the characters, lines 3700–3770 | — |  |
| 26 | `M3FirstVoa.hvac` | ProofMapConcreteRankFourVoa.lean:66 | Table 1, `d = 15 + A + 10B`: `δc_{(0,0)}(1) = 2(d - 22)`, `d = dim U₁` | even-block reading of the characters, lines 3700–3770 | — |  |
| 27 | `M3ReverseVoa.hsupp` | ProofMapConcreteRankFourVoa.lean:84 | Table 2, `d = 14 + 42A`: `δc` is supported on `λ + ℕ` for the coset weights `λ` | lines 3700–3770 | — |  |
| 28 | `M3ReverseVoa.hvac0` | ProofMapConcreteRankFourVoa.lean:89 | Table 2, `d = 14 + 42A`: `δc_{(0,0)}(0) = 1` | even-block reading of the characters, lines 3700–3770 | — |  |
| 29 | `M3ReverseVoa.hpolar` | ProofMapConcreteRankFourVoa.lean:90 | Table 2, `d = 14 + 42A`: `δc_{(2,1)}(2/21) = -A` | even-block reading of the characters, lines 3700–3770 | — |  |
| 30 | `M3ReverseVoa.hother` | ProofMapConcreteRankFourVoa.lean:91 | Table 2, `d = 14 + 42A`: below `q^{1/3}`, `δc` vanishes except at `((0,0),0)`, `((2,1),2/21)` | even-block reading of the characters, lines 3700–3770 | — |  |
| 31 | `M3ReverseVoa.hvac1` | ProofMapConcreteRankFourVoa.lean:93 | Table 2, `d = 14 + 42A`: `δc_{(0,0)}(1) = 2d - 94` | even-block reading of the characters, lines 3700–3770 | — |  |
| 32 | `M6FirstVoa.hsupp` | ProofMapConcreteRankFourVoa.lean:111 | Table 3, `d = 8 + A`: `δc` is supported on `λ + ℕ` for the coset weights `λ` | lines 3700–3770 | — |  |
| 33 | `M6FirstVoa.hvac0` | ProofMapConcreteRankFourVoa.lean:115 | Table 3, `d = 8 + A`: `δc_{(0,0)}(0) = 0` | even-block reading of the characters, lines 3700–3770 | — |  |
| 34 | `M6FirstVoa.hpolar` | ProofMapConcreteRankFourVoa.lean:116 | Table 3, `d = 8 + A`: `δc_{(1,0)}(1/4) = (8 - A)/2` | even-block reading of the characters, lines 3700–3770 | — |  |
| 35 | `M6FirstVoa.hother` | ProofMapConcreteRankFourVoa.lean:117 | Table 3, `d = 8 + A`: below `q^{1/3}`, `δc` vanishes except at `((0,0),0)`, `((1,0),1/4)` | even-block reading of the characters, lines 3700–3770 | — |  |
| 36 | `M6FirstVoa.hvac` | ProofMapConcreteRankFourVoa.lean:118 | Table 3, `d = 8 + A`: `δc_{(0,0)}(1) = 2(d - 16)` | even-block reading of the characters, lines 3700–3770 | — |  |
| 37 | `M6ReverseVoa.hsupp` | ProofMapConcreteRankFourVoa.lean:136 | Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`: `δc` is supported on `λ + ℕ` for the coset weights `λ` | lines 3700–3770 | — |  |
| 38 | `M6ReverseVoa.hvac0` | ProofMapConcreteRankFourVoa.lean:140 | Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`: `δc_{(0,0)}(0) = 1` | even-block reading of the characters, lines 3700–3770 | — |  |
| 39 | `M6ReverseVoa.hpolar` | ProofMapConcreteRankFourVoa.lean:141 | Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`: `δc_{(2,1)}(1/6) = -P` | even-block reading of the characters, lines 3700–3770 | — |  |
| 40 | `M6ReverseVoa.hother` | ProofMapConcreteRankFourVoa.lean:142 | Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`: below `q^{1/3}`, `δc` vanishes except at `((0,0),0)`, `((2,1),1/6)` | even-block reading of the characters, lines 3700–3770 | — |  |
| 41 | `M6ReverseVoa.hvac1` | ProofMapConcreteRankFourVoa.lean:143 | Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`: `δc_{(0,0)}(1) = 2d - 94` | even-block reading of the characters, lines 3700–3770 | — |  |
| 42 | `NetInputs.rank` | ProofMapConcreteNetCount.lean:78 | conditional on `netCompletelyRational` and the algebraic rank-six ring: `rank 𝓕_net = 6` | graph reduction 4307–4322; center induction 4345–4352 | — | [external] center induction |
| 43 | `NetInputs.untwisted` | ProofMapConcreteNetCount.lean:100 | **the conjunct `ν₃(a) = 1` of `NetHI` is assumed**: given the proved node `UntwistedNode` (free-induction equivalence, monoidal equivalence with the untwisted `Vec_{ℤ/3}`), `certDiscriminant`, `netCompletelyRational` | lines 4383–4406 | — | [standard] FS indicator; lattice-net sector category = `Rep(B)` |
| 44 | `hν` | ProofMapConcrete.lean:478–480 | **the 𝓕-side content**: given the node `UntwistedNode` (free-induction equivalence and the proved monoidal equivalence `𝒞_{H/B} ≃` untwisted `Vec_{ℤ/3}`), `certDiscriminant`, `lagrangianCenter`, `stronglyRational`, three invertibles: `ν₃(a) = 1` | lines 3349–3352 (the tensor embedding into `𝓕` with image `{𝟙, a, a*}`) | — | [standard] Frobenius–Schur indicator of the untwisted `Vec_{ℤ/3}`; the Tannakian (Deligne) step is now proved (`untwisted_vec_equivalence_of_separable`) |

### 5.4 [definitional] (38 entries covering 39 Lean hypotheses; 0 bundles)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `AutExpansion[B].hgid` | ProofMapConcreteBoundary.lean:542 | `g ≠ id`: `x ≠ [𝟙]` | definitional | — |  |
| 2 | `AutExpansion[B].hxa` | ProofMapConcreteBoundary.lean:544 | `a` is the invertible attached to `g`: `x_a ≠ 0` | definitional | — |  |
| 3 | `AutExpansion[Bn].hgid` | ProofMapConcreteBoundary.lean:542 | `g ≠ id`: `x ≠ [𝟙]` | definitional | — |  |
| 4 | `AutExpansion[Bn].hxa` | ProofMapConcreteBoundary.lean:544 | `a` is the invertible attached to `g`: `x_a ≠ 0` | definitional | — |  |
| 5 | `CharacterInputs.qexp` | ProofMapConcreteCharacters.lean:320 | the characters are the `q`-series of the graded dimensions, exponents in `n + t_l - 1/3` | definitional (twists from `modularData`, `h ≥ 0` from `projectiveVacuum`) | — |  |
| 6 | `CharacterInputs.below` | ProofMapConcreteCharacters.lean:327 | `hw l` is the lowest weight of the module labelled `l`: the graded dimensions vanish below `hw l` (its consequence `a l 0 = 0` for `b, a, c₀` is the premise `hpos` of the character arrow, discharged by `noWeightZero_of_vacuum`) | definitional | — |  |
| 7 | `CharacterInputs.low` | ProofMapConcreteCharacters.lean:332–333 | conditional on `projectiveVacuum` (concrete: `VacuumNode`, `h ≥ 0`) and `modularData` (the twists): the lowest weight `hw l` is one of the exponents `n + t_l` and its coefficient is the top dimension `td l > 0` | definitional; line 4178 | — | [external] Huang: twist congruence `hw l ∈ t_l + ℤ` (`θ = e^{2πiL(0)}`) |
| 8 | `CharacterInputs.U1` | ProofMapConcreteCharacters.lean:335 | the `q^{2/3}` coefficient of `ch U` is `dim U₁` | definitional | — |  |
| 9 | `LI.hw` | ProofMapSimples.lean:52 | the identification preserves lowest weights (`C.hw (ident s) = SD.hw s`) | definitional | — |  |
| 10 | `LI.td` | ProofMapSimples.lean:54 | the identification preserves top dimensions (`C.td (ident s) = SD.td s`) | definitional | — |  |
| 11 | `LI.vac` | ProofMapSimples.lean:56 | the identification sends `U` to the label `o` | definitional | — |  |
| 12 | `PF13Inputs.gen` | ProofMapConcretePF13.lean:113 | `A` is generated by `L, a` | definitional | — |  |
| 13 | `hf, μ, f (Haar averages)` | ProofMapConcrete.lean:481–482 | `μ i` are probability measures on the compact current group, `f i g = g · (factor conformal vector)` is integrable | lines 2688–2721 | — | [standard] integrability |
| 14 | `hfK` | ProofMapConcrete.lean:483 | the orbit maps take values in the orbits `St.K i` | definitional | — |  |
| 15 | `havg` | ProofMapConcrete.lean:484 | `St.avg i` is the Haar average `∫ f i dμ i` | definitional | — |  |
| 16 | `[∀ n, FiniteDimensional (St.U.grade n)]` | ProofMapConcrete.lean:491 | the grades of `U` are finite-dimensional | definitional (CFT type) | — |  |
| 17 | `TopBoundInputs.pos` | ProofMapConcreteTopBound.lean:71 | the lowest space of a simple module is nonzero | definitional | — |  |
| 18 | `BranchBInputs.int` | ProofMapConcreteBranching.lean:152 | `B` is `ℤ`-graded: the summands of `B↓U` have integral lowest weights | definitional | — |  |
| 19 | `BranchBInputs.vacT` | ProofMapConcreteBranching.lean:155 | the summand containing `𝟏` is `U`, with weight-one space `U₁` | definitional | — |  |
| 20 | `BranchBInputs.grade` | ProofMapConcreteBranching.lean:160 | `T j` is the weight-one space of `M_j` | definitional | — |  |
| 21 | `ComponentTops.L0_top` | Regularity/VacuumTopZero.lean:293 | `L^{A′}(0) = e_(1)` acts on the top `T k` by its lowest weight | definitional | — |  |
| 22 | `VacuumInputs.labels` | ProofMapConcreteVacuum.lean:170 | conditional on `initialGrades`: each `s : Simp` is the class of a simple module with lowest weight `SD.hw s`, and only `SD.vac` admits a nonzero map from `U` | definitional | — | [standard] Schur |
| 23 | `hunit` | ProofMapConcrete.lean:472 | `𝒞` is `Rep(U)` with unit `U`, so `VacuumIsProjective` means `𝟙_𝒞` is projective | definitional | — |  |
| 24 | `M3FirstVoa.hVq` | ProofMapConcreteRankFourVoa.lean:54 | Table 1, `d = 15 + A + 10B`: `η⁸ V = ∑ δc(x) qˣ` (the `q`-expansion defining `δc`) | definitional | — |  |
| 25 | `M3ReverseVoa.hVq` | ProofMapConcreteRankFourVoa.lean:82 | Table 2, `d = 14 + 42A`: `η⁸ V = ∑ δc(x) qˣ` (the `q`-expansion defining `δc`) | definitional | — |  |
| 26 | `M6FirstVoa.hVq` | ProofMapConcreteRankFourVoa.lean:109 | Table 3, `d = 8 + A`: `η⁸ V = ∑ δc(x) qˣ` (the `q`-expansion defining `δc`) | definitional | — |  |
| 27 | `M6ReverseVoa.hVq` | ProofMapConcreteRankFourVoa.lean:134 | Table 4 (6-dim swap-symmetric block), `d = 5 + 12P`: `η⁸ V = ∑ δc(x) qˣ` (the `q`-expansion defining `δc`) | definitional | — |  |
| 28 | `SectorInputs[I₁ (J)].int` | ProofMapConcreteBranchH.lean:74 | `H` is `ℤ`-graded: integral lowest weights | definitional | — |  |
| 29 | `SectorInputs[I₁ (J)].grade` | ProofMapConcreteBranchH.lean:79 | `T j` is the weight-one space of `M_j` | definitional | — |  |
| 30 | `SectorInputs[I₁ (J)].td` | ProofMapConcreteBranchH.lean:92 | top dimension of a weight-one summand is `dim (M_j)₁` | definitional | — |  |
| 31 | `SectorInputs[I₂ (J²)].int` | ProofMapConcreteBranchH.lean:74 | `H` is `ℤ`-graded: integral lowest weights | definitional | — |  |
| 32 | `SectorInputs[I₂ (J²)].grade` | ProofMapConcreteBranchH.lean:79 | `T j` is the weight-one space of `M_j` | definitional | — |  |
| 33 | `SectorInputs[I₂ (J²)].td` | ProofMapConcreteBranchH.lean:92 | top dimension of a weight-one summand is `dim (M_j)₁` | definitional | — |  |
| 34 | `BranchHInputs.mult` | ProofMapConcreteBranchH.lean:133 | `H↓U = B↓U ⊕ J↓U ⊕ J²↓U`: multiplicities add | line 3231 | — |  |
| 35 | `BranchHInputs.vac` | ProofMapConcreteBranchH.lean:135 | the vacuum summand `U` has lowest weight 0 | definitional (CFT type) | — |  |
| 36 | `BranchHInputs.tdX` | ProofMapConcreteBranchH.lean:137 | the top dimension of `X` is `dim X₁` | definitional | — |  |
| 37 | `Fintype / DecidableEq instances` | ProofMapConcrete.lean:98–108, 445 | the index types `ι, κ, Sec, σ, Simp, τ₁, τ₂` are finite with decidable equality | definitional | — | [external] `[Fintype Simp]`: finitely many simple modules from `C₂`-cofiniteness (Zhu; Dong–Li–Mason), known before `modularData` (ProofMapSimples.lean:20–24) |
| 38 | `[FiniteDimensional ℝ E], measurable/probability instances` | ProofMapConcrete.lean:101, 481–482 | the PCT-fixed weight-two space is finite-dimensional; Haar measures are probability measures | definitional | — |  |

### 5.5 [standard] (11 entries covering 14 Lean hypotheses; 0 bundles)

| # | Lean name | File:line | Statement | Source (citation / manuscript lines) | Lattice model | Further tags |
|---|---|---|---|---|---|---|
| 1 | `hK` | ProofMapConcrete.lean:483 | orbits of the compact current group are compact | standard | — |  |
| 2 | `BranchBInputs.vac_unique` | ProofMapConcreteBranching.lean:158 | `B₀ = ℂ𝟏`: no other summand has weight-zero vectors | standard (lattice VOA of CFT type) | — |  |
| 3 | `SignInputs.rank` | ProofMapConcreteBranching.lean:364 | if `B^g = U` then `(B₁)^g = U₁ ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂` has toral subalgebras of dimension `≤ 2` | lines 3305–3307, 3316–3317 | — |  |
| 4 | `hfp` | ProofMapConcrete.lean:465 | conditional on `stronglyRational`: an object of Frobenius–Perron dimension 1 is invertible (`d_X = 1 ⇒ X` invertible) | EGNO §3.3 | — |  |
| 5 | `UntwistedInputs.hS` | ProofMapConcreteUntwisted.lean:126 | `H/B` is separable (connected étale algebra in a fusion category) | standard (Kirillov–Ostrik / DMNO) | — | [external] |
| 6 | `UntwistedInputs.h3` | ProofMapConcreteUntwisted.lean:128 | `3 ≠ 0` in `𝕜` | standard | — |  |
| 7 | `UntwistedInputs.hidem` | ProofMapConcreteUntwisted.lean:136 | `Rep(B)` is idempotent complete (abelian) | standard | — |  |
| 8 | `𝒞 instances` | ProofMapConcrete.lean:447–449 | `Rep(U)` is a monoidal, preadditive, ℂ-linear category with binary biproducts and kernels, finite-dimensional Hom spaces | Huang–Lepowsky–Zhang / McRae (finite tensor category) | — | [external] |
| 9 | `Cr instances (and 𝕜)` | ProofMapConcrete.lean:451, 476–477 | `Rep(B)` is a monoidal, preadditive, 𝕜-linear category with finite biproducts, linear monoidal structure, finite-dimensional Homs | Dong (lattice VOAs) | — | [external] |
| 10 | `[HasCoequalizers Cr], [PreservesColimits (tensorLeft X)], [PreservesColimits (tensorRight X)]` | ProofMapConcrete.lean:452 | `Rep(B)` has coequalizers and `X ⊗ -`, `- ⊗ X` preserve them (a semisimple abelian category with exact tensor product) | standard (fusion categories) | — |  |
| 11 | `[CharZero k], [CharZero kp]` | ProofMapConcrete.lean:445 | the fields of the closure data and of the PF13 model have characteristic zero | standard | — |  |

## 6. Index by input structure

Every argument of `concrete_proof_map` (ProofMapConcrete.lean:445–494) and every field of its input structures, with the primary tag.

| Structure / argument | Fields (primary tag) |
|---|---|
| RemainingInputs | `C_finiteClosure` [certificate], `C_dimensions` [certificate], `C_pct` [certificate], `C_structural` [certificate], `C_discriminant` [certificate], `E_cklw529` [external], `L_rational` [manuscript step], `E_dmno` [external], `E_gsy` [external], `E_netCR` [external], `L_reconstruction` [manuscript step], `L_annulus` [manuscript step], `E_tener` [external], `L_boundaryUnitary` [manuscript step], `E_izumi` [external], `E_moritaCenter` [external], `E_netCenter` [external], `E_netExtension` [external], `E_diagonal` [external], `E_e8Extension` [external] |
| LowerCertificate | `KK0` [certificate], `KS₂0` [certificate], `KS₂1` [certificate], `TK` [certificate], `KmK` [certificate], `ω_mem` [certificate], `S₂S₂0` [certificate], `S₂S₂1` [certificate], `S₂S₂2` [certificate], `N₃_le_S₃` [certificate], `S₃_prov` [certificate], `P₄_prov` [certificate], `hL_q` [certificate], `eL_q, fL_q` [certificate], `hR_qp, hR_q0, hR_qm` [certificate], `eR_qp` [certificate], `eR_q0, eR_qm` [certificate], `fR_qp` [certificate], `fR_q0` [certificate], `fR_qm` [certificate], `L1_P₄` [certificate], `L2_P₄` [certificate] |
| Gate4Certificate | `highest, seed, singletSeed` (data), `highest_S₂` [certificate], `highest_eL, highest_eR` [certificate], `seed_S₃, singletSeed_S₃` [certificate], `seed_identity` [certificate], `singlet_premise_L, singlet_premise_R` [certificate], `projected_residual` [certificate], `raising_span` [certificate], `S₂_decomp` [certificate] |
| Gate5Certificate | `e, charged, a₃, p₃, n₃, c₃, chargedSeeds` (data), `e_mem, charged_sub, highest_sub` [certificate], `bottom` [certificate], `a₃_mem, p₃_mem` [certificate], `bottom₃, n₃_mem, c₃_ne` [certificate], `chargedSeeds_S₃, chargedSeeds_mem` [certificate], `lowering_span` [certificate] |
| C_finiteClosure (other conjuncts) | `raising nilpotence` [certificate], `lowering nilpotence` [certificate], `ω ∈ S₂, u ∈ S₂, S₂ ≤ U` [certificate] |
| BoundaryInputs | `hBJ` [external], `simple1, simpleX, simpleY` [manuscript step], `ne1X, ne1Y, neXY` [manuscript step], `bj` [external], `dec` [manuscript step], `hInd` [external] |
| AutExpansion[B] | `hx` [manuscript step], `hy` [manuscript step], `hxy` [external], `hxx` [external], `hgid` [definitional], `hxa` [definitional] |
| AutExpansion[Bn] | `hx` [manuscript step], `hy` [manuscript step], `hxy` [external], `hxx` [external], `hgid` [definitional], `hxa` [definitional] |
| InductionFormulas[B] | `codegree_X` [external], `codegree_Y` [external], `rootC` [external], `root` [external], `n_pos` [manuscript step], `sum_b` [manuscript step], `nu1_a` [external], `nu3_a` [external], `nu1_ρ` [external], `nu2_ρ` [external], `eps` [external], `center_dim` [external] |
| InductionFormulas[Bn] | `codegree_X` [external], `codegree_Y` [external], `rootC` [external], `root` [external], `n_pos` [manuscript step], `sum_b` [manuscript step], `nu1_a` [external], `nu3_a` [external], `nu1_ρ` [external], `nu2_ρ` [external], `eps` [external], `center_dim` [external] |
| CharacterInputs | `fin` [external], `T_diag` [external], `S_ne` [external], `hol` [external], `cov` [external], `qexp` [definitional], `summ` [external], `below` [definitional], `low` [definitional], `U1` [definitional], `EG` [external], `res₁` [certificate], `top₁` [certificate], `res₂` [certificate], `top₂` [certificate] |
| EvansGannon | `hol₀, hol₃` [external], `cov₀, cov₃` [external], `q₀, q₃` [external], `sum₀, sum₃` [external], `pp₃_o, pp₃, pp₃_d3` [external], `vac₀, vac₃` [external], `table` [external] |
| LI | `ident (SimpleLabels.ident)` [manuscript step], `hw` [definitional], `td` [definitional], `vac` [definitional] |
| PF13Inputs | `row'` [external], `rab` [certificate], `rad` [certificate], `simple` [manuscript step], `simple'` [external], `gen` [definitional], `gen'` [external] |
| direct arguments of `concrete_proof_map` | `hf, μ, f (Haar averages)` [definitional], `hK` [standard], `hfK` [definitional], `havg` [definitional], `hfac` [external], `hnonneg` [external], `[∀ n, FiniteDimensional (St.U.grade n)]` [definitional], `hadj` [external], `hfp` [standard], `hunit` [definitional], `hEP` [external], `hν` [manuscript step], `𝒞 instances` [standard], `Cr instances (and 𝕜)` [standard], `[BraidedCategory Cr]` [external], `[HasCoequalizers Cr], [PreservesColimits (tensorLeft X)], [PreservesColimits (tensorRight X)]` [standard], `[IsCommMonObj Ah.X]` [external], `[CharZero k], [CharZero kp]` [standard], `Fintype / DecidableEq instances` [definitional], `[FiniteDimensional ℝ E], measurable/probability instances` [definitional] |
| TopBoundInputs | `mono` [manuscript step], `trace` [manuscript step], `pos` [definitional] |
| BranchBInputs | `int` [definitional], `vacT` [definitional], `vac_unique` [standard], `grade` [definitional], `stable` [external], `disj` [external], `top` [external], `sum` [external] |
| SignInputs | `rlyg` [external], `rank` [standard], `sign` [manuscript step] |
| VacuumInputs | `reg` [external], `noNeg` [external], `labels` [definitional] |
| ComponentTops | `eqv` [external], `wt_nonneg` [external], `L0_top` [definitional], `Lm1_vac` [external] |
| RankFourInputs | `rule` [manuscript step], `larson` [external], `case2` [external], `case3` [external], `case6` [external] |
| M3FirstVoa | `hfin` [certificate], `hσS, hσT` [external], `hVhol, hVcov` [external], `hVq` [definitional], `hsupp` [manuscript step], `hsum` [external], `hvac0` [manuscript step], `hpolarB, hpolarA` [manuscript step], `hother` [manuscript step], `hvac` [manuscript step] |
| M3ReverseVoa | `hfin` [certificate], `hσS, hσT` [external], `hVhol, hVcov` [external], `hVq` [definitional], `hsupp` [manuscript step], `hsum` [external], `hvac0` [manuscript step], `hpolar` [manuscript step], `hother` [manuscript step], `hvac1` [manuscript step] |
| M6FirstVoa | `hfin` [certificate], `hσS, hσT` [external], `hVhol, hVcov` [external], `hVq` [definitional], `hsupp` [manuscript step], `hsum` [external], `hvac0` [manuscript step], `hpolar` [manuscript step], `hother` [manuscript step], `hvac` [manuscript step] |
| M6ReverseVoa | `hfin` [certificate], `hσS, hσT` [external], `hVhol, hVcov` [external], `hVq` [definitional], `hsupp` [manuscript step], `hsum` [external], `hvac0` [manuscript step], `hpolar` [manuscript step], `hother` [manuscript step], `hvac1` [manuscript step] |
| SectorInputs[I₁ (J)] | `cert` [certificate], `int` [definitional], `noZero` [certificate], `grade` [definitional], `stable` [external], `disj` [external], `top` [external], `sum` [external], `td` [definitional] |
| SectorInputs[I₂ (J²)] | `cert` [certificate], `int` [definitional], `noZero` [certificate], `grade` [definitional], `stable` [external], `disj` [external], `top` [external], `sum` [external], `td` [definitional] |
| BranchHInputs | `mult` [definitional], `vac` [definitional], `tdX` [definitional] |
| NetInputs | `dims` [external], `rank` [manuscript step], `iso` [external], `bj` [external], `pointed` [external], `untwisted` [manuscript step], `ind` [external], `count` [external] |
| UntwistedInputs | `hSchur` [external], `hfusion` [external], `hA` [certificate], `hunitS` [external], `hS` [standard], `h3` [standard], `hss` [external], `hidem` [standard], `hθ` [external] |

## 7. Summary counts

Counting conventions: a *Lean hypothesis* is one proposition-valued argument of `concrete_proof_map` or one proposition-valued field of an input structure (fields listed together in one row are counted individually; bundle headers and witness data are not counted, their fields are).  `AutExpansion` and `InductionFormulas` are counted once per use (for `𝓕` and for `𝓕_net`).  The 20 `RemainingInputs` fields are counted as 19 hypotheses plus the bundle `C_finiteClosure`, whose 54 certificate fields are counted individually.

Entries in Section 5: 249 (plus 9 bundle headers); **Lean hypotheses of `concrete_proof_map`: 288**.

For `lattice_proof_map` (ProofMapLattice.lean:471) the 24 Lean hypotheses of the entries `RI.C_dimensions`, `RI.C_pct`, `LowerCertificate.KK0`, `LowerCertificate.KS₂0`, `LowerCertificate.KS₂1`, `LowerCertificate.TK`, `LowerCertificate.KmK`, `LowerCertificate.ω_mem`, `LowerCertificate.hL_q`, `LowerCertificate.eL_q, fL_q`, `LowerCertificate.hR_qp, hR_q0, hR_qm`, `LowerCertificate.eR_qp`, `LowerCertificate.eR_q0, eR_qm`, `LowerCertificate.fR_qp`, `LowerCertificate.fR_q0`, `LowerCertificate.fR_qm`, `LowerCertificate.L2_P₄`, `certFiniteClosure: ω ∈ S₂, u ∈ S₂, S₂ ≤ U` are theorems (modulo `FLMBorcherds`), and it has one new hypothesis: `hB : FLMBorcherds` **[external]** (the Borcherds identity for the Fock-model modes, FLM Theorem 8.10.2).  The PCT node needs no input: `PCTModeCompatible` (Lattice/PCTLink.lean:471; `θ_g = pctV`, the map `eq:pct` of lines 1975–1989, is compatible with all modes, an antilinear automorphism of the lattice VOA) is the theorem `pctModeCompatible` (Lattice/PCTModes.lean:470), and the PCT-stability `θ_g U = U` of line 2604 follows (`pctV_mem_U_lattice`); `E_cklw529` still carries Dong–Lin unitarity (the transported form is positive definite with PCT operator `θ_g`) and CKLW Proposition 5.29.  The instance argument `[CharZero k]` ([standard], one of the two fields of the entry `[CharZero k], [CharZero kp]`) is not a hypothesis of `lattice_proof_map`, since `k = ℂ`.

| Tag | Lean hypotheses of `concrete_proof_map` | Entries | `RemainingInputs` fields | Lean hypotheses of `lattice_proof_map` |
|---|---|---|---|---|
| [external] | 113 | 98 | 11 | 114 |
| [certificate] | 73 | 58 | 5 | 49 |
| [manuscript step] | 49 | 44 | 4 | 49 |
| [definitional] | 39 | 38 | 0 | 39 |
| [standard] | 14 | 11 | 0 | 13 |
| **total** | **288** | **249** | 20 | **264** |

[external] hypotheses by source:

| Source | Hypotheses |
|---|---|
| Ostrik / Ng–Schauenburg / Vafa | 20 |
| Zhu / Huang (even-block modularity) | 20 |
| Evans–Gannon | 14 |
| Dong–Li–Mason (complete reducibility) | 12 |
| Bischoff–Jones | 6 |
| Dong / Dong–Lepowsky (lattice modules) | 6 |
| Zhu / Huang (modularity) | 5 |
| Abe–Buhl–Dong / regularity of the factors | 5 |
| Dong–Lam–Yamada / Linshaw | 3 |
| Kawahigashi–Longo / CKLW (nets) | 3 |
| Davydov–Müger–Nikshych–Ostrik | 2 |
| Tener / Longo (nets) | 2 |
| Grossman–Snyder / DMNO / Reutter | 2 |
| HKL / Gui / ABD / Dong–Mason (E₈) | 2 |
| Carpi–Kawahigashi–Longo–Weiner | 1 |
| Gannon–Schopieray–Yadav | 1 |
| Izumi | 1 |
| Longo–Rehren / Müger / DMNO | 1 |
| Rehren | 1 |
| Dong–Lin–Ng | 1 |
| RLYG | 1 |
| Huang / Miyamoto (finite length) | 1 |
| McRae / Etingof–Penneys | 1 |
| Larson | 1 |
| EGO / HKL / Dong–Mason (m = 2) | 1 |

Entries whose statement the lattice model proves, fully or in part (modulo `FLMBorcherds`): 19 — `RI.C_finiteClosure`, `RI.C_dimensions`, `RI.C_pct`, `LowerCertificate.KK0`, `LowerCertificate.KS₂0`, `LowerCertificate.KS₂1`, `LowerCertificate.TK`, `LowerCertificate.KmK`, `LowerCertificate.ω_mem`, `LowerCertificate.hL_q`, `LowerCertificate.eL_q, fL_q`, `LowerCertificate.hR_qp, hR_q0, hR_qm`, `LowerCertificate.eR_qp`, `LowerCertificate.eR_q0, eR_qm`, `LowerCertificate.fR_qp`, `LowerCertificate.fR_q0`, `LowerCertificate.fR_qm`, `LowerCertificate.L2_P₄`, `certFiniteClosure: ω ∈ S₂, u ∈ S₂, S₂ ≤ U`.


## 8. Points a reviewer should check

1. **Assumed conclusions.**  Two hypotheses supply a conclusion directly rather than a premise of
   an argument: `hν` (ProofMapConcrete.lean:478) supplies `ν₃(a) = 1` for the boundary category
   (the only content of the node `untwistedPointed` used downstream, by `L_rankSixMoments` and
   `E_izumi`), and `NetInputs.untwisted` (ProofMapConcreteNetCount.lean:100) supplies the
   conjunct `ν₃(a) = 1` of `NetHI`.  Both are conditional on the proved node `UntwistedNode`
   (free-induction equivalence, and the monoidal equivalence of the `H/B`-module category with the
   untwisted `Vec_{ℤ/3}`, `untwisted_vec_equivalence_of_separable`), but the tensor embedding into
   `𝓕` and the Frobenius–Schur indicator are not formalized: neither `𝓕` nor `ν₃` is part of the
   categorical model.
2. **Concrete content concluded by external arrows.**  `E_dmno` concludes the positive dimension
   character of `𝓕` with `∑ d_i² = 3s`, `d_X = s - 1`; `E_cklw529` concludes `dim U₀ = 1`;
   `L_reconstruction` (open) concludes that `recon` is injective with unitarizable values.
3. **Unmodelled predicates.**  `Unitarizable`, `SignData.XInvertible`, `SignData.toral`,
   `StressData.factorNonneg`, and the opaque nodes of Section 2 are propositions whose meaning is
   fixed only by their docstrings and the inputs that mention them.
4. **Unlinked models.**  `U` appears as `D.U u` (properness, over an arbitrary field `k`) and as
   `St.U` (regularity, over `ℂ` with a positive form); these are not identified in Lean.  `𝒞`
   (`Rep(U)`) is linked to `St.U` only through `hunit`; `Cr` (`Rep(B)`) is not linked to `A`;
   `B` and `Bn` are independent `BoundaryData`; `ι`, `κ` are not linked to `Simp`.  `Simp` is
   linked to `Label` by `LI` (conditional on `modularData`).
5. **Lattice model.**  The entries proved for `latticeD`/`latticeDP` hold modulo the single
   hypothesis `FLMBorcherds` (the Borcherds identity for the Fock-model modes, FLM Theorem
   8.10.2), and are discharged together in `lattice_proof_map` (ProofMapLattice.lean).  There the
   PCT node is no longer opaque: it is *defined* as "`θ_g` is mode-compatible, `θ_g S₂ = S₂` and
   `θ_g U = U`" (`pctNodes`); all three conjuncts are proved (`pctModeCompatible`,
   Lattice/PCTModes.lean; `certPCT_latticeD`; `pctV_mem_U_lattice`).  `E_cklw529` still carries Dong–Lin unitarity (the transported form is positive definite
   with PCT operator `θ_g`) and CKLW Prop. 5.29 itself; a reviewer should check that this is the
   reading of `certPCT` the manuscript uses (lines 1975–1992, 2604).  `S₃` (dimension 956) is not
   yet exported from the lattice data, so 7 `LowerCertificate` fields, Gates 4/5 and the
   nilpotence statements remain certificate inputs (`LatticeClosureInputs`).  The other models
   of item 4 (`St.U`, `𝒞`, `Cr`, `B`, `Bn`) are not instantiated at the lattice VOA.
6. **Open manuscript lemmas.**  `L_rational`, `L_reconstruction`, `L_annulus`,
   `L_boundaryUnitary` are not made concrete: their nodes involve module categories, nets and
   unitary structures that are not modelled.

