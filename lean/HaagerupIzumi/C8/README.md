# Formalization of the central-charge-eight Haagerup construction

Started 30 September 2026 (first six-hour session).  Lean `v4.33.1`, Mathlib `0df444a3`,
package `HaagerupIzumi`, namespace `HaagerupIzumi.C8`.  Source:
`c8_expanded_20260929/haagerup_c8_expanded.tex` (line numbers below refer to it); scope
assessment ("formalization scout"): `c8_expanded_20260929/lean_scope.tex`.

**Status (1 October 2026, ~02:00).** 76 files, about 18,500 lines and 1,110 theorems.
Every file compiles with no `sorry`, no `axiom`, and no `native_decide`; every
`#print axioms` report is a subset of `[propext, Classical.choice, Quot.sound]`.  Finite
checks use kernel `decide` / `decide +kernel`.

## How the whole proof is represented

1. **`ProofMap.lean`** states the entire argument (Appendices A–K) as a kernel-checked
   deduction.  Every claim is a node; every step is an arrow labelled *certificate input*
   (`C_`), *external theorem* (`E_`, with citation) or *manuscript lemma* (`L_`).
   `prop_mainproper`, `thm_main_net` and `thm_claim_main` derive the three main results.
   This checks that the arrows compose with nothing missing; by itself it verifies no arrow.
2. **Concrete modules** prove the mathematical content of the `L_` arrows from explicitly
   stated inputs (table below).  External theorems and finite lattice certificates enter only
   as named hypotheses phrased as the statement cited, never as the conclusion.
3. **Properness is assembled end to end** (`MainProperness`, `InitialGrades`,
   `Nilpotence`), and `ProofMapProperness.properness_arrows` proves the four properness arrows
   of the proof map for the concrete nodes.

## Trust boundary

* **Vertex algebra.**  `VertexAlgebra/Basic.lean` is the working interface; every one of its
  fields is *derived* in `VertexAlgebra/Borcherds.lean` from the Borcherds identity, the
  vacuum axioms and an `ℕ`-grading of CFT type (`BorcherdsVertexAlgebra.toVertexAlgebra`).
  The lattice VOA `B = V_{E₆⊕A₂}` itself is not constructed: it is an object satisfying this
  definition (FLM), together with the finite certificates below.
* **Finite certificates** (ledger, lines 5236–5297) are hypotheses stated as subspace
  memberships of actual vectors: `LowerCertificate`, `Gate4Certificate`, `Gate5Certificate`
  (Properness/Setup, Gate4, Gate5), minimal generation `hmin`, `dim K = 6`, `dim B₁ = 86`.
  The gates themselves are derived, not assumed.
* **External theorems** (Zhu, Huang, McRae, Etingof–Penneys, Ostrik, Ng–Schauenburg, Larson,
  DLN, GSY, Izumi, Grossman–Snyder, DMNO, Henriques–Tener, Tener, Longo, Kawahigashi–Longo,
  CKLW, Gui, Longo–Rehren, Rehren, Reutter, Müger, HKL, Dong–Mason, Kac) appear as `E_` arrows
  of `ProofMap` and, where a concrete module needs them, as hypotheses with the cited content.

## Module map

| Area | Modules | What is proved (manuscript statement) |
|---|---|---|
| Whole proof | `ProofMap`, `ProofMapProperness` | dependency skeleton of Appendices A–K; three main theorems; properness arrows proved |
| Vertex algebras | `VertexAlgebra/Basic`, `Borcherds`, `NormalWords`, `FilteredWick`, `Recursive`, `Weak` (weak VAs, e.g. products, not of CFT type) | interface from the Borcherds identity; `def:normal-span` (graded description); `lem:filtered-wick` (both parts); `thm:recursive` (`recursive_strong_generation`, incl. `U₁ = S₁`) |
| Finite gates | `Properness/Setup`, `ModeLemmas`, `Lower`, `FullNormal`, `Gate4`, `Gate5`, `Final`, `Corollary` | Virasoro commutators for weight-two fields; `lem:bootstrap`; `lem:normal-controls`; `lem:jacobi`; `lem:raising`; `lem:singlet`; Gate 4 (eq:gate4) and Gate 5 (eq:gate5) from the certificates; full normal spaces `𝒩₃, 𝒩₄` equal the displayed spans; hypotheses (1),(2) of `thm:recursive` |
| Properness | `MainProperness`, `MinimalGeneration`, `InitialGrades`, `Nilpotence`, `LatticeNilpotence` | **`prop:mainproper`**: `U = 𝒩(K,S₂,S₃,P₄)`, `U₁ = K`, `U ≠ B`; minimal generation from the record's closure computation (`S₂_le_U_of_closure`); graded pieces of `cor:initial-grades`: `U₂ = S₂`, `U₃ = S₃` (simplicity, `c = 8`, character not formalized); nilpotence of raising words derived from the lattice (`lem:current-bounds`): `prop_mainproper_of_lattice` needs only the Fock momentum decomposition of `B₃` and the momentum shifts of current zero modes |
| Lattice data | `Data/Lattice`, `Data/Spectra`, `Data/Weights`, `Sl2/CurrentBounds`, `Sl2/Projectors` | Gram matrix (= Cartan `E₆ ⊕ A₂`), positive definite, `det = 9`; cocycle identities; `lem:levels` (levels 1, 39; central charges sum to 8); eq:u momenta; multiplet table; `lem:current-bounds`; FE eigenvalues and the projectors of eq:projector on Mathlib's `IsSl2Triple`; Gate 5 weight table; isotropic lines in `(ℤ/13)²`, `(ℤ/3)²`; free `H/B`-module induction count on `L₋` |
| Regularity | `PositiveStress`, `Regularity/Energy`, `Regularity/CompatibleTop`, `VacuumLike`, `SimpleQuotient`, `VertexAlgebra/Diagonal`, `VertexAlgebra/PF13`, `PF13Product` | eq:finite-positive-stress (compact convex hulls, Haar averages, Carathéodory); `lem:positive-c2` (energy bound); eq:top-trace and the nilpotent version (`lem:vacuum-projective`); **`lem:compatible-top`**, algebraic core (`compatible_top_sum`: every Zhu-submodule is a sum of tops; `compatible_top`: eigenbasis with eigenvalues among the lowest weights; `isNonnegDiagonalizable_of_compatible`: the input `hL` of `top_trace_nonneg` for an operator on the common space `E`; `commutator_step`: a mode of degree `d` shifts `L(0)`-eigenvalues by `d`, so the lowest space is killed by lowering modes and stable under zero modes; `vacuum_top_step`: `L^A(0) = 0` on `v` forces `L^A(-1)v = 0` when `L(-1)` kills the weight-zero tops; the decomposition `Ω_A(M) ≅ ⨁ tops` is the external regularity input); growth estimate of `lem:projective-unit`; `lem:vacuum-like` (with the section `vacuumLike_section` of `lem:vacuum-projective`); **`prop:pf13-finite-reconstruction`**: uniqueness half (`diagonal_reconstruction`); OPE recovery (`all_pairs`, `pf13_reconstruction`) conditional on the manuscript's Wick claims `A₆, A₇, A₈, B₇` |
| Top bound | `CoreTops`, `Data/CoreTops`, `Data/CoreTopsBridge`, `CFT/TopBound` | the fourteen core tops reproduced from the charge formulas (minima over all integer charges, dimensions, `4680 W`); sl₂ character inequalities; **eq:sharp-top-bound** `h ≤ 17/10` given eq:top-trace (`lowest_weight_le_of_trace`) |
| Branching | `Branching` | integral weights `0,1`; `86 - 6 = 80`; eq:rank-fork; extension dimensions; six invertibles impossible; diagram automorphism group of `E₆` is `{1, flip}` (`e6_diagram_automorphisms`), diagram orbits of `E₆`, `A₂` (`lem:no-sign-extension` arithmetic); index arithmetic of the full theory |
| Fusion rings | `Fusion/BasedRing`, `Rank6`, `FusionAlgebra`, `Rank6Iso`, `Pivotal`, `AutInvertible`, `Center`, `Rank6Indicators` | based rings; **eq:rank6-ring** (`rank6_ring`, from `ℂ⊕ℂ⊕M₂(ℂ)`); `lem:automorphisms-invertibles`; center dimension identities; pivotal uniqueness; `ℂˣ = (ℂˣ)³` |
| Rank four | `RankFour`, `Fusion/NearGroup*`, `Fusion/E8FixedPoints`, `CubeRootTwists`, `NearGroupMoments`, `ModularLinearAlgebra`, `FormalCodegrees`, `Theta/*` | near-group dimensions and eq:near-group-length; twist separation; eq:near-group-moments; `lem:m6-balanced` (Verlinde = 4/3); `lem:m6-projection` (twists and S-matrix derivation); `prop:m3-modular` (twists, row uniqueness); E₈ fixed points (`dim E₈^{A₄} ≥ 16`); all four theta tables of `prop:near-group-current-obstructions` kernel-verified, and the four `dim U₁` formulas (conditional on the applied pole-cancellation identity); assembled in `rank_four_excluded` |
| Rank six, m = 1 | `RankSixMoments`, `CubeRootTwists`, `NumberTheory/Squareclass`, `MultiplicityOne`, `Thirteen`, `Conductor40` | eq:indicator-first/second from the twist traces; `b_j = m`, twists `1, ζ, ζ²`; eq:squareclass-bound; **`m = 1`** (`multiplicity_eq_one`); Gauss periods of 13; `lem:six-residual-twists` given the Galois-orbit step; Haagerup dimensions |
| Characters | `Characters`, `Analytic/PoleCancellation`, `CharacterUniqueness` | twist list, only allowed pole `q^{-7/39}`, unique `T`-fixed coordinate, `γ = 0`, lowest weights ≤ 15/13, `cor:unmixed-lattice-restrictions`; **`lem:pole-cancellation` fully proved** (Mathlib modular forms); **`lem:haagerup-character-unique`** (`character_vector_unique`: no invariant vector from the twist table and `S_{0,c₁} ≠ 0`, then pole cancellation; inputs: finite image (DLN), the diagonal `T` (twist list of `lem:six-residual-twists`, `c = 8`), `S_{0,c₁} ≠ 0` (Huang's identification of Zhu's `S` with the categorical `S`); the lemma as stated is `haagerup_character_unique`: same vacuum coefficient, strict positivity and the same `γ` give `F = G`, via `polar_cases` and `character_vector_unique_of_qexp`) |
| Categorical | `Category/BraidedModules`, `Category/RelativeTensor` | `lem:analytic-unitary-all-modules`, algebraic core: a right module over a commutative algebra in a braided category is a bimodule via `l = r ∘ c` (unit, associativity, commuting actions, morphisms); this full subcategory of bimodules is closed under `⊗_A`; locality ⇔ both braiding orientations agree |
| Analytic | `Analytic/GraphReduction`, `Comparison`, `NetCount`, `AnalyticContinuation` | `lem:analytic-graph-reduction` (closure and adjoint); `lem:analytic-inverse-domain`; `lem:analytic-insertion-continuation`; Haag-duality squeeze; deck cancellation; Schur step; counting; irreducibility step of `clm:analytic-net-count` |

## Status of the arrows of `ProofMap`

`ProofMap.Inputs` has 5 certificate inputs, 30 manuscript-lemma arrows and 11 external-theorem
arrows.  Status of the manuscript-lemma arrows (`L_pf13` appears in two rows: its uniqueness half is proved, its OPE recovery is conditional):

| Status | Arrows |
|---|---|
| **Proved for concrete nodes** (`ProofMapProperness.properness_arrows`) | `L_gates`, `L_recursive`, `L_weightOne`, `L_proper` |
| **Core argument proved** (remaining inputs are external theorems or certificates) | `L_positiveStress`, `L_c2`, `L_projectiveVacuum` (trace steps and the core of `lem:compatible-top`; the commutator step (given the module commutator relation), the vacuum-top step and the section are proved; the representation-theoretic parts of the splitting are listed under "What remains"), `L_rigid` (growth step), `L_topBound`, `L_branchB`, `L_branchH`, `L_rankFork`, `L_autInvertible`, `L_noSign` (arithmetic), `L_threeInvertibles`, `L_notRankFour`, `L_rankSixRing`, `L_rankSixMoments`, `L_characters`, `L_unmixed`, `L_netCount`, `L_reconstruction`, `L_stronglyUnitary`, `L_annulus`, `L_pf13` (uniqueness half) |
| **Proved modulo a manuscript lemma not yet formalized** | `L_multiplicityOne` (needs `lem:conductor40`), `L_twelveTwists` (needs the Galois-orbit step of `lem:six-residual-twists`), `L_pf13` (needs the Wick claims `A₆, A₇, A₈, B₇`) |
| **Categorical, partly formalized** | `L_boundaryUnitary` (braided-module core proved in `Category/`; Gui's unitarization external), `L_untwisted` (isotropy, trivial twists on `L₋`, cosets and the Hom count `δ_{x,y}` of free induction proved; the free-module adjunction and Tannakian identification external), `L_rational` (bookkeeping) |

The external arrows (`E_cklw529`, `E_dmno`, `E_gsy`, `E_netCR`, `E_tener`, `E_izumi`,
`E_moritaCenter`, `E_netCenter`, `E_netExtension`, `E_diagonal`, `E_e8Extension`) carry the
cited theorems of CKLW, DMNO, GSY, Tener/Longo, Izumi, Grossman–Snyder, Reutter, Longo–Rehren,
Rehren, HKL, Gui, Dong–Mason and Müger.

`C8Axioms.lean` prints the axioms of 63 headline theorems (all `⊆ [propext, Classical.choice,
Quot.sound]`); `C8All.lean` imports all modules together.

## Independent review (30 September – 1 October)

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

## What remains

The scoped work plan (inventory, work items W1–W9, suggested order, start-up commands) is
[`ROADMAP.md`](ROADMAP.md).  Summary:


* **Manuscript lemmas still hypotheses:** `lem:conductor40` (`Conductor40Bound`), the
  Galois-orbit step of `lem:six-residual-twists` (`NonresidueOrbitStep`); the weight-bounded
  Wick claims `A₆, A₇, A₈, B₇` of `prop:pf13-finite-reconstruction` (`claimA6_a0b`, `claimA7`,
  `claimA8`, `claimB7`); the Verlinde rows in `lem:m6-balanced` (rows forced by DLN's signed
  Galois symmetry) and the moment values in `lem:m6-projection`, `prop:m3-modular`
  (computations of the manuscript entered as hypotheses); the application of
  pole cancellation to the theta identities (`hcancel`); the von Neumann algebra sentence of
  `lem:analytic-graph-reduction` (needs polar decomposition of unbounded operators); in
  `lem:vacuum-projective`, the module commutator relation `[L(0), a_(n)] = (wt a - n - 1) a_(n)`
  behind the commutator step (whose algebra is `CompatibleTop.commutator_step`, lines 2941–2943),
  and in the splitting (2959–2978) the finite length from
  `C₂`-cofiniteness, the absence of negative weights and the choice of `v ∈ N_[0]` with
  `π v = 𝟏` (the vacuum-top step `L^{eᵢ}(0)|_E = 0 ⇒ L^{eᵢ}(-1)E = 0` is
  `CompatibleTop.vacuum_top_step`, given that `L(-1)` kills the weight-zero tops, and the section
  `a ↦ a_(-1) v` with `π ∘ s = id` is `VacuumLike.vacuumLike_section`).
* **Foundations:** a construction of `V_{E₆⊕A₂}` as a `BorcherdsVertexAlgebra`; a Lean checker
  for the finite certificates (thousands of identities over `ℚ(√13, √-3)`); Zhu algebras and
  module categories; tensor categories, centers, Izumi's classification; conformal nets and
  the Henriques–Tener/Tener analytic theorems.
* **Citation precision found during formalization:** Larson, Theorem 1.3 (cited at line 3936)
  is false as printed for `c = 1`; the manuscript only uses `c = 13, 10, …` (`c > 1`).

## Building

Compilation goes through the root-coordinated queue `lean/tools/c8q.py`, which admits each job
through `~/.local/bin/research-safe-run` (no subagent launches jobs).  To build everything in
dependency order:

```sh
python3 lean/tools/c8q.py runner &           # root only; C8Q_MAX_PARALLEL=2 uses a second
                                             # guard slot only when no other session holds one
python3 lean/tools/c8_build_all.py --keep-going
```
