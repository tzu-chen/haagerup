# Formalization of the central-charge-eight Haagerup construction

Started 30 September 2026 (first six-hour session).  Lean `v4.33.1`, Mathlib `0df444a3`,
package `HaagerupIzumi`, namespace `HaagerupIzumi.C8`.  Source:
`c8_expanded_20260929/haagerup_c8_expanded.tex` (line numbers below refer to it); scope
assessment ("formalization scout"): `c8_expanded_20260929/lean_scope.tex`.

**Status (4 October 2026; third session).** See the counts in `ROADMAP.md` §0.  New in the third
session:
* **Theta identities:** the `hcancel` identities of `prop:near-group-current-obstructions` are theorems
  relative to VOA-side inputs (`Theta/ObstructionsOfVoa`), with the SL₂ relations of the four Weil
  blocks proved.
* **Lattice certificates:** kernel replays about the computable lattice VOA: minimal generation and
  the full closure of `S₂`, the PCT certificate, and the actual triplet `P₄` with all 18 of its
  current identities.  The PCT map `θ_g` is proved to be an antilinear automorphism of the model
  (`PCTModes.pctModeCompatible`).  The model's one assumption is the Borcherds identity (`FLMBorcherds`), now reduced to
  closure under products plus the identity for 24 generator fields (Dong's lemma and local-field
  theory formalized, W3).
* **Proof map:** 26 of 30 `L_` arrows are proved for concrete nodes, and `lattice_proof_map`
  instantiates the proof map at the actual lattice VOA.  `TRUST_BOUNDARY.md` lists every remaining
  hypothesis.
* **Categorical (`L_untwisted` and neighbours):** a monoidal equivalence `𝒞_{H/B} ≃` untwisted
  symmetric `Vec_{ℤ/3}` (modulo the lattice self-braiding `hθ`), the double dual and pivotal
  uniqueness, the split coequalizer, the three simple modules, and the module tower.
* **Smaller items:** the vacuum-top step on `N_[0]`, and the Schur part of `Ψ`.

Every file compiles with no `sorry`, no `axiom` and no `native_decide`, and every `#print axioms`
report is a subset of `[propext, Classical.choice, Quot.sound]`.  Finite checks use kernel `decide` /
`decide +kernel`.  `C8All.lean` imports all 1253 modules of `HaagerupIzumi/C8/` (all except
`Lattice/Bench.lean`); `C8Axioms.lean` audits 320 headline theorems (integration build of
4 October, 1257 modules, green).

## How the whole proof is represented

1. **`ProofMap.lean`** states the entire argument (Appendices A–K) as a kernel-checked
   deduction.  Every claim is a node; every step is an arrow labelled *certificate input*
   (`C_`), *external theorem* (`E_`, with citation) or *manuscript lemma* (`L_`).
   `prop_mainproper`, `thm_main_net` and `thm_claim_main` derive the three main results.
   This checks that the arrows compose with nothing missing; by itself it verifies no arrow.
2. **Concrete modules** prove the mathematical content of the `L_` arrows from explicitly
   stated, tagged inputs (table below; `TRUST_BOUNDARY.md` lists all of them).  External
   theorems and finite lattice certificates enter as named hypotheses phrased as the statement
   cited, mostly as premises of a Lean argument.  **A few inputs supply a conjunct of a concrete
   node directly** (the argument is in the manuscript or the literature, not in Lean):
   * `hν` (ProofMapConcrete.lean) supplies `ν₃(a) = 1` for the boundary category, the conjunct
     `B.ν₃ = 1` of the node `untwistedPointed`.  `L_untwisted` proves the other conjunct,
     `UntwistedNode`: free `H/B`-induction from the additive closure of `L₋` is an equivalence onto
     all `H/B`-modules, and the `H/B`-module category is monoidally equivalent to the untwisted
     `Vec_{ℤ/3}` (the Tannakian step of lines 3335–3348 is therefore proved, given the tagged
     inputs on `Rep(B)` and `H/B`).  The rest is the input `hν`: the tensor embedding into `𝓕`
     with image `{𝟙, a, a*}` ([manuscript step], lines 3349–3352) and the Frobenius–Schur indicator
     of the generator of the untwisted `Vec_{ℤ/3}` ([standard]).
   * `NetInputs.untwisted` (ProofMapConcreteNetCount.lean) supplies the same conjunct
     `Bn.ν₃ = 1` of `NetHI` (node `netCount`) on the net side.
   * `hEP` (ProofMapConcrete.lean) supplies rigidity, the conjunct "every object of `𝒞` has a
     right dual" of `RigidSemisimple` (node `rigidSemisimple`), from `C₂`-cofiniteness,
     unitarity and a projective unit ([external] McRae, Etingof–Penneys; [manuscript step]
     moderate growth and non-negligibility, lines 2992–3006, the growth estimate formalized).
     `L_rigid` proves the other conjunct (every object projective, `projective_of_rigid`), and
     the projective unit comes from the concrete `lem:vacuum-projective` through the
     [definitional] link `hunit`.
   * `hadj` (ProofMapConcrete.lean) supplies `rank 𝓕 = ∑_l [H↓U : M_l]²`, the first conjunct of
     the node `rankFork` ([external] DMNO adjunction `FI(𝟏) = ⊕ a ⊗ a*`, [standard] Schur);
     `L_rankFork` proves the second, `rank 𝓕 ∈ {4, 6}`.
   * Intermediate claims supplied in the same way: `RankFourInputs.case2` gives the `m = 2`
     result `dim U₁ ≥ 16` (EGO, HKL, Dong–Mason; the bound `dim 𝔢₈^{A₄} ≥ 16` is proved), from
     which `L_notRankFour` concludes; `NetInputs.rank` gives `rank 𝓕_net = 6` and
     `NetInputs.count` gives `#Sec = 6 + #κ`, from which `L_netCount` derives the ring and
     `#Sec = 12`.
   * By design the `E_` arrows and the four open `L_` arrows of `RemainingInputs` conclude their
     nodes; the concrete conjuncts concluded this way are `dim U₀ = 1` (`E_cklw529`, node
     `initialGrades`), the positive dimension character with `∑ d_i² = 3s`, `d_X = s − 1`
     (`E_dmno`, node `lagrangianCenter`), and the injectivity of `recon` with unitarizable values
     (`L_reconstruction`, node `reconstruction`).
3. **Properness is assembled end to end** (`MainProperness`, `InitialGrades`,
   `Nilpotence`), and `ProofMapProperness.properness_arrows` proves the four properness arrows
   of the proof map for the concrete nodes.

## Trust boundary

* **Vertex algebra.**  `VertexAlgebra/Basic.lean` is the working interface; every one of its
  fields is *derived* in `VertexAlgebra/Borcherds.lean` from the Borcherds identity, the vacuum
  axioms and an `ℕ`-grading of CFT type (`BorcherdsVertexAlgebra.toVertexAlgebra`).  `Lattice/` is a
  computable model of `B = V_{E₆⊕A₂}` (Fock space, FLM vertex operators), cross-checked against the
  Python engine.  `Lattice/VOA.lean` builds `latticeVOA` from one hypothesis, now reduced to the
  Borcherds identity alone (`FLMReduce.flmInput_of_borcherds`); W3 reduces that further
  (`FLMBorcherdsIter`: closure under products plus 24 generator fields).
  `ProofMapLattice.lattice_proof_map` runs the whole proof map on this model.
* **Finite certificates** (ledger, lines 5236–5297) are hypotheses stated as subspace
  memberships of actual vectors (for the lattice model, several are now kernel-checked theorems:
  `certDimensions_latticeD`, `minimalGeneration_latticeD`, `S2span_eq_closureSpace`,
  `certPCT_latticeD`, the 18 triplet controls in `P4Link`/`P4Left`/`P4RFRP`/`P4RFRZ`/`P4RFRM`/`P4RERP`/`P4RDerived`, `P4NonZero`, `S2savedSpan_eq`, `L2_P4_latticeDP`, `KS21_latticeDP`): `LowerCertificate`, `Gate4Certificate`, `Gate5Certificate`
  (Properness/Setup, Gate4, Gate5), minimal generation `hmin`, `dim K = 6`, `dim B₁ = 86`.
  The gates themselves are derived, not assumed.
* **External theorems** (Zhu, Huang, McRae, Etingof–Penneys, Ostrik, Ng–Schauenburg, Verlinde,
  DLN, GSY, Izumi, Grossman–Snyder, DMNO, Henriques–Tener, Tener, Longo, Kawahigashi–Longo,
  CKLW, Gui, Longo–Rehren, Rehren, Reutter, Müger, HKL, Dong–Mason, Kac) appear as `E_` arrows
  of `ProofMap` and, where a concrete module needs them, as hypotheses with the cited content.
  Larson's Theorem 1.3 is no longer external: `NumberTheory.larsonRootCount` proves it for
  squarefree `c > 1`.

## Module map

| Area | Modules | What is proved (manuscript statement) |
|---|---|---|
| Whole proof | `ProofMap`, `ProofMapProperness`, `ProofMapConcrete*` (`Boundary`, `Branching`, `BranchH`, `Characters`, `NetCount`, `PF13`, `RankFour`, `RankFourVoa`, `Regularity`, `Rigid`, `TopBound`, `Unitarity`, `Untwisted`, `Vacuum`; combined in `ProofMapConcrete`), `ProofMapSimples`, `ProofMapLattice` | dependency skeleton of Appendices A–K (`Nodes`, `Inputs`: 5 `C_`, 11 `E_`, 30 `L_`) and the three main theorems `prop_mainproper`, `thm_main_net`, `thm_claim_main`; concrete node functions composed in `allConcreteNodes`; **26 of 30 `L_` arrows proved for concrete nodes** (`inputs_of_concrete`, `concrete_conclusions`, `concrete_proof_map`); the simple `U`-modules as an arbitrary finite type `Simp` with lowest weights and top dimensions, identified with the twelve character labels only after the modular data (`ProofMapSimples`: `SimpleData`, `SimpleLabels`); the untwisted pointed node as free-induction equivalence plus the monoidal equivalence with the untwisted `Vec_{ℤ/3}` (`ProofMapConcreteUntwisted`, via `Category/UntwistedVecEquivalence`); the VOA-side data of the four rank-four theta tables with the proved obstruction formulas (`ProofMapConcreteRankFourVoa`: `M3FirstVoa`, `M3ReverseVoa`, `M6FirstVoa`, `M6ReverseVoa`, `case3_of_voa`, `case6_of_voa`); the instance at the actual lattice VOA (`ProofMapLattice`: `lattice_proof_map`, with `KK0_latD`, `lowerCertificate_latD`, `pctV_mem_U_latD`); every remaining hypothesis listed in `TRUST_BOUNDARY.md` |
| Lattice VOA model | `Lattice/Fock`, `Modes`, `Semantic`, `Data`, `Roots`, `Dimensions`, `Relations`, `CentralCharge`, `Samples*` (`Bench`, `Benchmark.md`) | computable Fock space of `V_{E₆⊕A₂}` with FLM vertex operators, kernel-evaluable; agrees with the Python engine on all 822 exported samples; the norm-2 vectors are the 78 roots; `dim K = 6`, `dim B₁ = 86` (`certDimensions_model`); current OPEs at levels 1, 39; `c = 8`; kernel benchmark for the certificate checker.  **4 Oct:** `S2*`, `S2Close*` (minimal generation, `S₂` = its closure space), `PCT*` (θ_g S₂ = S₂), `P4*` (the triplet, current identities), `ModeQ`, `ModeQR`, `ModeHH` (fast evaluators with link theorems), `FLMGen`/`FLMChecks`/`FLMReduce` (`FLMInput` from the Borcherds identity), `FLMBorcherdsGen`/`Iter` (reduction to generators); `Benchmark.md` §5 |
| Vertex algebras | `VertexAlgebra/Basic`, `Borcherds`, `NormalWords`, `FilteredWick`, `Recursive`, `Weak` (weak VAs, e.g. products, not of CFT type) | interface from the Borcherds identity; `def:normal-span` (graded description); `lem:filtered-wick` (both parts); `thm:recursive` (`recursive_strong_generation`, incl. `U₁ = S₁`); **4 Oct (W3):** `BorcherdsReduce` … `BorcherdsFieldE`: Good-vector calculus (Borcherds identity ⇐ commutator + iterate families), Dong's lemma for all `n`, abstract local fields (`OpField.borcherds_of_local`, `OpField.dong`, weak associativity); plan `Lattice/W3_PLAN.md` |
| Finite gates | `Properness/Setup`, `ModeLemmas`, `Lower`, `FullNormal`, `Gate4`, `Gate5`, `Final`, `Corollary` | Virasoro commutators for weight-two fields; `lem:bootstrap`; `lem:normal-controls`; `lem:jacobi`; `lem:raising`; `lem:singlet`; Gate 4 (eq:gate4) and Gate 5 (eq:gate5) from the certificates; full normal spaces `𝒩₃, 𝒩₄` equal the displayed spans; hypotheses (1),(2) of `thm:recursive` |
| Properness | `MainProperness`, `MinimalGeneration`, `InitialGrades`, `Nilpotence`, `LatticeNilpotence` | **`prop:mainproper`**: `U = 𝒩(K,S₂,S₃,P₄)`, `U₁ = K`, `U ≠ B`; minimal generation from the record's closure computation (`S₂_le_U_of_closure`); graded pieces of `cor:initial-grades`: `U₂ = S₂`, `U₃ = S₃` (simplicity, `c = 8`, character not formalized); nilpotence of raising words derived from the lattice (`lem:current-bounds`): `prop_mainproper_of_lattice` needs only the Fock momentum decomposition of `B₃` and the momentum shifts of current zero modes |
| Lattice data | `Data/Lattice`, `Data/Spectra`, `Data/Weights`, `Sl2/CurrentBounds`, `Sl2/Projectors` | Gram matrix (= Cartan `E₆ ⊕ A₂`), positive definite, `det = 9`; cocycle identities; `lem:levels` (levels 1, 39; central charges sum to 8); eq:u momenta; multiplet table; `lem:current-bounds`; FE eigenvalues and the projectors of eq:projector on Mathlib's `IsSl2Triple`; Gate 5 weight table; isotropic lines in `(ℤ/13)²`, `(ℤ/3)²`; free `H/B`-module induction count on `L₋` |
| Regularity | `PositiveStress`, `Regularity/Energy`, `Regularity/CompatibleTop`, `VacuumLike`, `SimpleQuotient`, `VertexAlgebra/Diagonal`, `VertexAlgebra/PF13`, `PF13Product` | eq:finite-positive-stress (compact convex hulls, Haar averages, Carathéodory); `lem:positive-c2` (energy bound); eq:top-trace and the nilpotent version (`lem:vacuum-projective`); **`lem:compatible-top`**, algebraic core (`compatible_top_sum`: every Zhu-submodule is a sum of tops; `compatible_top`: eigenbasis with eigenvalues among the lowest weights; `isNonnegDiagonalizable_of_compatible`: the input `hL` of `top_trace_nonneg` for an operator on the common space `E`; `commutator_step`: a mode of degree `d` shifts `L(0)`-eigenvalues by `d`, so the lowest space is killed by lowering modes and stable under zero modes; `vacuum_top_step`: `L^A(0) = 0` on `v` forces `L^A(-1)v = 0` when `L(-1)` kills the weight-zero tops; the decomposition `Ω_A(M) ≅ ⨁ tops` is the external regularity input); growth estimate of `lem:projective-unit`; `lem:vacuum-like` (with the section `vacuumLike_section` of `lem:vacuum-projective`); `Regularity/VacuumProjective`, `NoNegativeWeights`: the module commutator relation `[L(0), a_(n)] = (wt a - n - 1) a_(n)` derived from the weak-module axioms, modes shift generalized weight spaces, no negative weights through a composition series ⇒ lowering modes kill `N_[0]`, the choice of `v ∈ N_[0]` with `π v = 𝟏`, the splitting with `L_N(-1) = ω_(0)`; `Regularity/VacuumTopZero`: the vacuum-top step on `N_[0]` from the `Ω_{Aᵢ}` decomposition (`omega_zero_on_genZero`, `vacuum_splitting_of_tops`); **`prop:pf13-finite-reconstruction`**: uniqueness half (`diagonal_reconstruction`); OPE recovery unconditional (`PF13Wick`: the Wick claims `A₆, A₇, A₈, B₇` proved; `pf13_reconstruction'`, `pf13_reconstruction_of_rows`; paper pass `PF13_PAPER_PASS.md`) |
| Top bound | `CoreTops`, `Data/CoreTops`, `Data/CoreTopsBridge`, `CFT/TopBound` | the fourteen core tops reproduced from the charge formulas (minima over all integer charges, dimensions, `4680 W`); sl₂ character inequalities; **eq:sharp-top-bound** `h ≤ 17/10` given eq:top-trace (`lowest_weight_le_of_trace`) |
| Branching | `Branching` | integral weights `0,1`; `86 - 6 = 80`; eq:rank-fork; extension dimensions; six invertibles impossible; diagram automorphism group of `E₆` is `{1, flip}` (`e6_diagram_automorphisms`), diagram orbits of `E₆`, `A₂` (`lem:no-sign-extension` arithmetic); index arithmetic of the full theory |
| Fusion rings | `Fusion/BasedRing`, `Rank6`, `FusionAlgebra`, `Rank6Iso`, `Pivotal`, `AutInvertible`, `Center`, `Rank6Indicators`, `CenterDimension`, `TwistTraces`, `Category/MonoidalAutomorphism` | based rings; **eq:rank6-ring** (`rank6_ring`, from `ℂ⊕ℂ⊕M₂(ℂ)`); `lem:automorphisms-invertibles`; center dimension identities (also from `Dim Z(𝓕) = (Dim 𝓕)²` stated generally); twist moments from the Ng–Schauenburg formula stated generally; pivotal uniqueness (based ring, and categorically: monoidal automorphisms of `𝟭` are trivial on a categorification, two monoidal isomorphisms `𝟭 ≅ F` agree; with `Category/DoubleDual`, `Category/Pivotal`: pivotal structures on an HI ring are unique); `ℂˣ = (ℂˣ)³`; `Fusion/EndHSchur`: `End(1 ⊕ X ⊕ 2Y) ≅ ℂ × ℂ × M₂(ℂ)` (Schur part of `Ψ`) |
| Rank four | `RankFour`, `Fusion/NearGroup*`, `Fusion/E8FixedPoints`, `CubeRootTwists`, `NearGroupMoments`, `ModularLinearAlgebra`, `FormalCodegrees`, `Theta/*` | near-group dimensions and eq:near-group-length; twist separation; eq:near-group-moments; `lem:m6-balanced` (Verlinde = 4/3; also from the Verlinde formula and DLN II(iii) stated generally, `Fusion/M6BalancedModular`); `lem:m6-projection` (twists and S-matrix derivation); `prop:m3-modular` (twists, row uniqueness); E₈ fixed points (`dim E₈^{A₄} ≥ 16`); all four theta tables of `prop:near-group-current-obstructions` kernel-verified, and the four `dim U₁` formulas; **4 Oct (W6):** `hcancel` derived from `pole_cancellation` relative to VOA-side inputs (`Theta/ObstructionsOfVoa.*_obstruction_of_voa`, lattice theta series and their S/T laws, `Eta8`, Serre derivative and `E₂`, polar parts, SL₂ relations of the Weil blocks); assembled in `rank_four_excluded` |
| Rank six, m = 1 | `RankSixMoments`, `CubeRootTwists`, `NumberTheory/Squareclass`, `MultiplicityOne`, `Thirteen`, `Conductor40`, `GaloisAverage`, `Conductor40Proof`, `ThirteenOrbit`, `LarsonProof` | eq:indicator-first/second from the twist traces; `b_j = m`, twists `1, ζ, ζ²`; eq:squareclass-bound; **`m = 1` with no external hypothesis** (`multiplicity_eq_one_unconditional`); Galois averaging for sums of roots of unity; **`lem:conductor40`** (`conductor40Bound`); **Larson's Theorem 1.3** for squarefree `c > 1` (`larsonRootCount`); Gauss periods of 13; **`lem:six-residual-twists`** (`six_residual_twists_proved`, `six_residual_twists_literal`); Haagerup dimensions |
| Characters | `Characters`, `Analytic/PoleCancellation`, `CharacterUniqueness` | twist list, only allowed pole `q^{-7/39}`, unique `T`-fixed coordinate, `γ = 0`, lowest weights ≤ 15/13, `cor:unmixed-lattice-restrictions`; **`lem:pole-cancellation` fully proved** (Mathlib modular forms); **`lem:haagerup-character-unique`** (`character_vector_unique`: no invariant vector from the twist table and `S_{0,c₁} ≠ 0`, then pole cancellation; inputs: finite image (DLN), the diagonal `T` (twist list of `lem:six-residual-twists`, `c = 8`), `S_{0,c₁} ≠ 0` (Huang's identification of Zhu's `S` with the categorical `S`); the lemma as stated is `haagerup_character_unique`: same vacuum coefficient, strict positivity and the same `γ` give `F = G`, via `polar_cases` and `character_vector_unique_of_qexp`) |
| Categorical | `Category/BraidedModules`, `Category/RelativeTensor`, `Category/FreeModule*`, `Category/MonoidalAutomorphism` | `lem:analytic-unitary-all-modules`, algebraic core: a right module over a commutative algebra in a braided category is a bimodule via `l = r ∘ c` (unit, associativity, commuting actions, morphisms); this full subcategory of bimodules is closed under `⊗_A`; locality ⇔ both braiding orientations agree; free-module adjunction, free induction bijective on Hom-sets between the three simples of `L₋`, retracts of free modules for separable algebras, the object-level isomorphism `(X⊗A) ⊗_A (Y⊗A) ≅ (X⊗Y) ⊗ A` (`L_untwisted`); monoidal automorphisms of `𝟭` act on simples by scalars (pivotal uniqueness); **4 Oct:** free induction monoidal/additive/an equivalence/a monoidal equivalence (`FreeModuleMonoidalEquivalence`, `UntwistedFromSeparable`), `SeparableCoequalizer` (split coequalizer), `SimpleModulesLminus` (three simples), `AbelianCocycleZ3`, `PointedCocycle*`, `LminusBraidedVec`, `LminusEnvelope`, `LminusClosureFunctor`, `GradedMat*` (untwisted symmetric `Vec_M`), **`UntwistedVecEquivalence`** (`𝒞_{H/B} ≃ Vec_{ℤ/3}`, monoidal, modulo `hθ`), `ModuleTower*` (forgetful embedding, algebraic core); manuscript feedback `CATEGORY_PAPER_PASS.md` |
| Analytic | `Analytic/GraphReduction`, `Comparison`, `NetCount`, `AnalyticContinuation` | `lem:analytic-graph-reduction` (closure and adjoint); `lem:analytic-inverse-domain`; `lem:analytic-insertion-continuation`; Haag-duality squeeze; deck cancellation; Schur step; counting; irreducibility step of `clm:analytic-net-count` |

## Status of the arrows of `ProofMap`

`ProofMap.Inputs` has 46 fields: 5 certificate inputs (`C_`), 11 external-theorem arrows (`E_`)
and 30 manuscript-lemma arrows (`L_`).  Status of the manuscript-lemma arrows (4 October 2026):
**26 of 30 are theorems about concrete nodes**; the other 4 are open and, with the 5 `C_` and
11 `E_` fields, form the hypothesis `RemainingInputs` (ProofMapConcrete.lean).

| Status | Arrows (file: theorem) |
|---|---|
| **Proved for concrete nodes (26)** | properness (`ProofMapProperness`: `properness_arrows`): `L_gates`, `L_recursive`, `L_weightOne`, `L_proper`; regularity (`ProofMapConcreteRegularity`: `positiveStress_arrow`, `c2_arrow`): `L_positiveStress`, `L_c2`; `L_pf13` (`ProofMapConcretePF13`: `pf13_arrow`, via `PF13Wick.pf13_reconstruction_of_rows`); `L_projectiveVacuum` (`ProofMapConcreteVacuum`: `projectiveVacuum_arrow`, with `Regularity/VacuumTopZero`); `L_rigid` (`ProofMapConcreteRigid`: `rigid_arrow`); `L_topBound` (`ProofMapConcreteTopBound`: `topBound_arrow`); branching (`ProofMapConcreteBranching`): `L_branchB` (`branchB_arrow`), `L_rankFork` (`branchRankFork_arrow`), `L_noSign` (`noSign_arrow`); `L_branchH` (`ProofMapConcreteBranchH`: `branchH_arrow`); boundary ring (`ProofMapConcreteBoundary`: `boundary_arrows`): `L_autInvertible`, `L_threeInvertibles`, `L_rankSixRing` (with `Fusion/EndHSchur`), `L_rankSixMoments`, `L_multiplicityOne` (no external hypothesis: `conductor40Bound`, `larsonRootCount`), `L_twelveTwists`; `L_untwisted` (`ProofMapConcreteUntwisted`: `untwisted_arrow`, `untwistedNode_of_inputs`; the node `UntwistedNode` is free `H/B`-induction from `L₋` an equivalence, `freeLminus_isEquivalence_of_separable`, **and** the module category of `H/B` monoidally equivalent to the untwisted symmetric `Vec_{ℤ/3}`, braided on the leg `Vec_{ℤ/3} ≃` additive closure of `L₋`, `untwisted_vec_equivalence_of_separable` of `Category/UntwistedVecEquivalence`; `ν₃(a) = 1` is the input `hν`); `L_notRankFour` (`ProofMapConcreteRankFour`: `notRankFour_arrow`; `m = 3, 6` through `ProofMapConcreteRankFourVoa.case3_of_voa`, `case6_of_voa` and the proved `Theta.*_obstruction_of_voa`); `L_netCount` (`ProofMapConcreteNetCount`: `netCount_arrow`, reusing the boundary-ring arrows for the net data); characters (`ProofMapConcreteCharacters`: `character_arrows`): `L_characters`, `L_unmixed`; `L_stronglyUnitary` (`ProofMapConcreteUnitarity`: `stronglyUnitary_arrow`).  The remaining inputs of each arrow are tagged in its docstring (external / certificate / manuscript step / definitional / standard). |
| **Open (4)**: fields of `RemainingInputs` | `L_rational` (`Rep(U)` rigid and semisimple, `C₂`-cofinite, CFT type ⇒ strongly rational, thm:positive-stress-rationality): its conclusion `stronglyRational` is an opaque node, since the module category of `U` is not modelled (`𝒞` is an abstract category linked to `U` only through `hunit`). `L_reconstruction` (clm:analytic-reconstruction, Henriques–Tener): conformal nets and their DHR sectors are not modelled. `L_annulus` (clm:analytic-annulus, Tener, Henriques–Tener): the bounded-insertion and smeared-field nets are not modelled. `L_boundaryUnitary` (lem:analytic-unitary-all-modules, Gui): unitary structures are not modelled; the braided-module algebraic core is proved in `Category/BraidedModules`, `Category/RelativeTensor`. |

* **`concrete_proof_map`** (ProofMapConcrete.lean): from `RemainingInputs` (20 fields) and the
  tagged inputs of the 26 concrete arrows, the concrete conclusions (the `HI(ℤ/3)` ring with
  `d_ρ = (3 + √13)/2` and its twists, the `γ = 0` character vector, the lowest-weight table,
  `0 ≤ h ≤ 17/10`, `lem:vacuum-projective`, rigidity, the branchings, the net count, free
  induction and `ν₃(a) = 1`, no sign extension, strong unitarity, `U₁ = K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂`,
  `U ⊊ B`, `C₂`-cofiniteness, `K(𝔰𝔩₂, 13)`) for arbitrary closure data: **288 Lean hypotheses**
  (113 external, 73 certificate, 49 manuscript step, 39 definitional, 14 standard).
* **`lattice_proof_map`** (ProofMapLattice.lean): the same for the actual lattice VOA
  (`latticeVOA` from `FLMBorcherds`, closure data `latticeDP` with the actual currents, `S₂`, `u`,
  `P₄`; `S₃` a parameter).  `C_dimensions`, `C_pct` (the PCT node read as: `θ_g` mode-compatible,
  `θ_g S₂ = S₂`, `θ_g U = U`, all three proved; mode compatibility is
  `LatticeVOA.pctModeCompatible`, Lattice/PCTModes) and the minimal-generation part of
  `C_finiteClosure` with 19 of the 26 `LowerCertificate` fields are theorems; one new
  hypothesis, `FLMBorcherds` ([external]): **264 Lean hypotheses** (114 external, 49
  certificate, 49 manuscript step, 39 definitional, 13 standard).  `E_cklw529` still carries
  Dong–Lin unitarity (positivity of the transported form) and CKLW 5.29.
  History on 4 October: 270, then 267 after the audit fixes (`eL_q`, `fL_q`
  discharged; `[CharZero k]` is not a hypothesis for `k = ℂ`), then 273 after the monoidal
  upgrade of `UntwistedNode` (six new tagged inputs, in both theorems: `hθ` trivial
  self-braidings on `L₋`, `Rep(B)` braided, coequalizers and their preservation by `X ⊗ -`,
  `- ⊗ X`, `H/B` commutative), then 270 with the three `F_R` controls `fR_qp`, `fR_q0`, `fR_qm`
  (Lattice/P4RFRP, P4RFRZ, P4RFRM; `F_R(0) q₊ = q₀` settles the normalization of `q₀`), then
  269 when `PCTModeCompatible` became a theorem (`pctModeCompatible`, the input `hθ` removed),
  then 266 with the three `E_R` controls `eR_qp`, `eR_q0`, `eR_qm` (Lattice/P4RERP, P4RDerived),
  then 265 with the Virasoro control `L2_P₄` (`L(2) P₄ ⊆ S₂`, Lattice/P4RL2), then 264 with
  `KS₂1` (`K_(1) S₂ ⊆ K`, Lattice/KS21, 720 checks with `modeQRF`).
* **`TRUST_BOUNDARY.md`**: every hypothesis of both theorems, with Lean name and file:line, tag,
  one-line statement, citation or manuscript lines, and lattice-model status; generated by
  `lean/tools/trust_boundary/tb_gen.py`, references checked by `tb_check.py`.

The external arrows (`E_cklw529`, `E_dmno`, `E_gsy`, `E_netCR`, `E_tener`, `E_izumi`,
`E_moritaCenter`, `E_netCenter`, `E_netExtension`, `E_diagonal`, `E_e8Extension`) carry the
cited theorems of CKLW, DMNO, GSY, Tener/Longo, Izumi, Grossman–Snyder, Reutter, Longo–Rehren,
Rehren, HKL, Gui, Dong–Mason and Müger.

## Independent review (30 September – 4 October)

Two read-only audits checked every file against the manuscript.  Findings: no hypothesis is
false, unsatisfiable or circular; every number, sign and convention checked matches the
manuscript (including all sixteen theta-table entries and the core-top table); the properness
chain assumes no gate or conclusion, and every certificate field corresponds to a ledger
record.  Fixed after review: the formally empty `Fusion.nearGroup_m0` is superseded by
`RankFour.nearGroup_m0_impossible`; `h ≤ 17/10` is now stated
(`CoreTops.lowest_weight_le_of_trace`); cube-root twists are derived
(`CubeRootTwists.eq_one_of_weighted_sum`); the PF13 Wick claims are named as unformalized
manuscript claims; several provenance labels ("external" for manuscript steps) were corrected.
Larson's Theorem 1.3 must be quoted with `c > 1`: as printed (`c ≥ 0` squarefree) it fails at
`c = 1`.

Two further audits on 1 October.  (i) `CharacterUniqueness` and `Regularity/CompatibleTop`: no
errors; GSY is Gannon–Schopieray–Yadav, and `L_characters` gained its strict-positivity premise.
(ii) Every arrow of `ProofMap` against the manuscript's proofs: nine arrows lacked premises that
their manuscript steps use.  Three of these were not available upstream at all: `L_branchB`
needs the top bound (integer weights `0, 1`), `L_noSign` needs `B↓U = U ⊕ X` in the tensor
category `Rep(U)`, and `L_netCount` needs the rank-six ring (multiplicities `1, 1, 2`).  The
others are `L_notRankFour`, `L_topBound`, `L_projectiveVacuum`, `L_rigid`, `E_gsy`,
`E_e8Extension`.  All were added, with the chain theorems updated.  Mislabelled premises were
replaced: `L_stronglyUnitary` now uses the twelve simples of the modular data, `E_e8Extension`
strict positivity, `L_annulus` the reconstructed modules, and `L_netCount` the net-side
discriminant form.  Hence `thm_claim_main` no longer passes through the character analysis.
`thm_main_net` also returns `initialGrades` (`c = 8`).  Citations are now split by paper
(TenFusion/TenFields, HTAnn/HTNet).  The node graph remains acyclic, and the three chain
theorems use no axioms.

Eight read-only audits on 4 October covered the files written that day:
* the category files, in three groups;
* the extension of the concrete proof map, and its label refactor;
* the theta capstones;
* the lattice instantiation, and the statement layer of the lattice kernel replays;
* the W3 files.

No logical or mathematical error was found.  The should-fix items were applied:
* missing premises on the rank-four cases;
* inputs that supply conclusion conjuncts, now documented;
* the forward dependency on the twelve labels, removed;
* the `G₆⁻` block, now 6-dimensional;
* the SL₂ sanity relations, added;
* the PCT anti-automorphism, now an explicit input;
* stale docstrings;
* the categorical paper pass, corrected against the manuscript.

## What remains

The scoped plan is [`ROADMAP.md`](ROADMAP.md) (§1 inventory, §3 order).  The precise list of
hypotheses is [`TRUST_BOUNDARY.md`](TRUST_BOUNDARY.md).  In short:
* **Decision needed (user):** a compiled checker (option (b)) for Gates 4/5 and the 3,970 lower
  relations, which are out of reach for kernel replay (`Lattice/Benchmark.md` §5).
* **W2:** `L(1)P₄ ⊂ S₃`, `P₄_prov`, `S₂S₂1`, `S₂S₂2`, the S₃ import (done: the 18 triplet current
  identities, the saved-`S₂` equality, `L(2)P₄`, `K_(1) S₂ ⊆ K`).
* **W3:** the bridge to local fields, Li's E-level locality and weak associativity (closure under
  products), then the 24 generator fields.
* **Other:** the VOA-side inputs of the theta argument; the
  external theorems cited in `ProofMap` (`E_` arrows) and in the concrete inputs; the four open
  arrows (`L_rational`, `L_reconstruction`, `L_annulus`, `L_boundaryUnitary`), which need module,
  net and unitary-category foundations.
* **Notes for the manuscript:** `ROADMAP.md` §4, which collects:
  - Larson's Theorem 1.3 for `c > 1`;
  - the PF13 paper pass, G1–G6;
  - the categorical paper pass;
  - the EGO citation check in the rank-four `m = 2` case.

## Building

Compilation goes through the root-coordinated queue `lean/tools/c8q.py`, which admits each job
through `~/.local/bin/research-safe-run` (no subagent launches jobs).  `~/.elan/bin` must be on
`PATH` (it is set only in login shells). Every request requires a reviewed memory estimate:
`c8q.py check|build FILE --memory-mib N`, or an explicitly set `C8Q_MEMORY_MIB`.
There is no guessed budget for an unknown module and no automatic retry at a larger cap.
To build everything in dependency order:

```sh
export PATH="$HOME/.elan/bin:$PATH"
python3 lean/tools/c8q.py runner             # root-controlled foreground session
# In a separate root-controlled tool session, after allocation review:
python3 lean/tools/c8_build_all.py --memory-mib REVIEWED_MIB --keep-going
```

Replace `REVIEWED_MIB` with a justified estimate for the selected build scope. A resource
failure stops new admission even with `--keep-going`, and `MEMORY_STOP.json` prevents an
unreviewed restart. Preserve that record and the failed attempt log; review the actual
allocation path and revise the design/estimate before archiving the record and resuming.
An already-running independent job may finish, but no further queued job is admitted.
The [notification audit](../../../memory_notice_audit_20261004/README.md) records why
these controls changed. The central guard and canonical machine policy remain in force.
