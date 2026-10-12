# What remains to formalize: scope and plan

Hand-off of 4 October 2026 (end of the third session).  Earlier hand-off notes are kept in the
work items below, each with its date.  This is the work list for the
next sessions.  `README.md` has the module map, the arrow-status table and the trust boundary;
`BRIEF.md` has the agent rules and Lean pitfalls.  Manuscript line numbers refer to
`c8_expanded_20260929/haagerup_c8_expanded.tex`.

## 0. Starting a session

### State at hand-off

* **Size:** about 1,250 Lean files in `HaagerupIzumi/C8/` (most are generated kernel-replay files
  under `Lattice/`), about 416,000 lines, about 8,350 theorems.
* **Build and axioms:** the final integration build of 4 October (17:10 CDT) was green
  (1257 modules).  `C8Axioms.lean` audits 320 headline theorems; all use only `propext`,
  `Classical.choice`, `Quot.sound`.  There is no `sorry`, `axiom` or `native_decide` in the tree.
* **Trust boundary:** `TRUST_BOUNDARY.md` lists every remaining hypothesis of the concrete proof map
  (`ProofMapConcrete.concrete_proof_map`) and of its instance at the actual lattice VOA
  (`ProofMapLattice.lattice_proof_map`), tagged and located (regenerate with
  `python3 lean/tools/trust_boundary/tb_gen.py && python3 lean/tools/trust_boundary/tb_check.py`).
* **Git:** nothing was committed in the third session (last commit `f3cfd4c`).  Commit a checkpoint
  before new work.
* **Queue changes (4 October):** `c8q.py` treats `std::bad_alloc` / Lean exit 134 as a memory
  breach (requeued with a doubled estimate), and the client takes `--memory-mib N` to declare a
  reservation measured by a probe; prefer that to breach-and-retry.  Rule of thumb: kernel memory
  grows by about 0.2 GiB per second of kernel time in one file, so size generated files from a probe.
* **Drafts outside the tree:** `lean/tools/lattice_export/drafts/p4ctl/` (superseded single-merge
  versions of the triplet controls, now all built in the tree; `pending/` is empty; deletable),
  `lean/tools/lattice_export/drafts/` (probes),
  `lean/tools/category_drafts/` (copies of compiled drafts and the superseded `VecZ3`; deletable).

### Environment

```sh
export PATH="$HOME/.elan/bin:$PATH"      # elan is on PATH only in login shells (~/.zprofile)
cd ~/Codes/haagerup
C8Q_MAX_PARALLEL=2 python3 lean/tools/c8q.py runner &   # root only; stop: touch /tmp/haagerup-c8q-1000/STOP
python3 lean/tools/c8_build_all.py --skip-built --keep-going lean/HaagerupIzumi/C8Axioms.lean
python3 lean/tools/c8q.py build lean/HaagerupIzumi/C8Axioms.lean      # headline axiom report
```

Without the PATH line, every queued job fails at once with
`No such file or directory: 'lean'`.

To check that nothing needs rebuilding, without compiling anything, mirror the environment of
`lean/safe_lean.py`.  Bare `lake` under the guard aborts with "failed to create thread"
(address-space cap).

```sh
cd ~/Codes/haagerup/lean
LEAN_NUM_THREADS=2 MIMALLOC_DISALLOW_ARENA_ALLOC=1 MALLOC_ARENA_MAX=2 \
LD_PRELOAD="$PWD/$(ls .lake/safe-runtime/lean-stack-*.so | grep -v building | head -1)" \
~/.local/bin/research-safe-run --memory-mib 1536 --limit-mib 6144 --threads 1 -- \
  lake build --no-build HaagerupIzumi HaagerupIzumi.C8Axioms
```

### Rules

Resource rules (from `AGENTS.md` and the machine policy):

* Only `research-safe-run` admits jobs, at most two at a time.
* Subagents never launch jobs; the root runs the queue.
* A job that exceeds its budget is redesigned, never rerun blindly.

Lean conventions:

* No `sorry`, `axiom` or `native_decide`.
* External theorems enter as named hypotheses that state the cited content.

After each item:

* update `README.md` (module map and arrow table);
* update the docstring of the affected `ProofMap` arrow;
* add new headline theorems to `C8Axioms.lean`;
* run an independent read-only audit against the manuscript.

## 1. Inventory: what is still assumed

### 1.1 Manuscript steps that are still hypotheses

**Closed in the session of 1 October 2026 (evening)** (details in the work items below):

| Item | Manuscript | Now a theorem | Arrow affected |
|---|---|---|---|
| `lem:conductor40` | 3950–3995 | `conductor40Bound : Conductor40Bound` (`NumberTheory/Conductor40Proof`) | `L_multiplicityOne` |
| Galois-orbit step of `lem:six-residual-twists` | 4019, 4025–4039 | `nonresidueOrbitStep : NonresidueOrbitStep` (`NumberTheory/ThirteenOrbit`) | `L_twelveTwists` |
| Larson, Theorem 1.3 (external, cited at 3936), squarefree `c > 1` | — | `larsonRootCount : LarsonRootCount` (`NumberTheory/LarsonProof`) | `L_multiplicityOne` |
| PF13 Wick claims `A₆` (on `a₀b`), `A₇`, `A₈`, `B₇` | 2777–2811 (prop. at 2733) | `PF13Wick.Data.claims`; unconditional `PF13Wick.pf13_reconstruction'` (`VertexAlgebra/PF13Wick`) | `L_pf13` (OPE recovery) |
| Verlinde rows of `lem:m6-balanced` (`hVerlinde`, pre-evaluated) | 3516–3548 | `Fusion.m6_balanced_impossible_of_modular` from the Verlinde formula, `S_{𝟏j} = d_j/Dim 𝓕`, DLN II(iii) and `Dim Z(𝓕) = (Dim 𝓕)²`, each stated generally (`Fusion/M6BalancedModular`) | `L_notRankFour` (`m = 6`) |
| Twist traces `trace1`, `trace2` (pre-evaluated) | 3392–3449, 3836–3913 | `TwistTraces.indicator_moments_of_trace`, `neargroup_moments_of_trace` from the Ng–Schauenburg formula stated generally (`TwistTraces`) | `L_notRankFour`, `L_rankSixMoments` |
| Center-dimension identities `hcenter` (pre-evaluated) | 3409, 3900 | `CenterDimension.rank6_length_of_center`, `nearGroup_length_of_center` from `Dim Z(𝓕) = (Dim 𝓕)²` (`CenterDimension`) | `L_notRankFour`, `L_rankSixMoments` |
| `lem:vacuum-projective`: module commutator relation | 2941–2943 | `VacuumProjective.L0_commutator` (derived from the `WeakModule` axioms), `act_mem_maxGenEigenspace` (generalized weight spaces, 2962–2964) | `L_projectiveVacuum` |
| `lem:vacuum-projective`: choice of `v ∈ N_[0]` with `π v = 𝟏`, and the splitting | 2971–2978 | `VacuumProjective.exists_vacuum_preimage`, `omega_vacuumLike_section` (with `L_N(-1) = ω_(0)`) | `L_projectiveVacuum` |

The new "stated generally" inputs (Verlinde formula, DLN II(iii), Ng–Schauenburg Theorem 4.1, Müger's
`Dim Z(𝓕) = (Dim 𝓕)²`, the normalization `S_{𝟏j} = d_j/Dim 𝓕`, `ν₁(ρ) = 0`, `ν₂(ρ) = ε`) are external
theorems; the lists of center simples with dimensions, twists and multiplicities (Ostrik's
induction–codegree correspondence) remain external inputs.

**Closed in the session of 4 October 2026:**

| Item | Manuscript | Now a theorem | Remaining input |
|---|---|---|---|
| Theta identities after pole cancellation (`hcancel`) | 3615–3770 | `Theta.m{3,6}_{first,reverse}_obstruction_of_voa` (`Theta/ObstructionsOfVoa`; capstones `*_hcancel_of_voa`; SL₂ relations of the four Weil blocks `sl2_relations_*`, `gauss7_eq`) | VOA side: σ with finite image identified with the even Weil block (Zhu, DLN, Huang), the vector `V`, its `q`-expansion and polar data |
| `End(1 ⊕ X ⊕ 2Y) ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` (Schur part of `Ψ`) | 3794–3800 | `Fusion.endHIsoOfSimple`, `fusionAlgebraIsoOfSimple` (`Fusion/EndHSchur`) | Bischoff–Jones identification `BJIso` (external) |
| Vacuum-top step on `N_[0]` | 2966–2970 | `VacuumTopZero.omega_zero_on_genZero`, `vacuum_splitting_of_tops` | `ComponentTops` (regularity of the factors, external) |
| Free-module induction and the Tannakian step (`L_untwisted`) | 3320–3352 | `untwisted_vec_equivalence_of_separable` (monoidal equivalence `𝒞_{H/B} ≃` untwisted symmetric `Vec_{ℤ/3}`), with `freeLminus_monoidalEquivalence_of_separable`, `PointedCocycle.Lminus_untwisted_symmetric`, `AbelianCocycle.isTrivial_iff`, `GrMat` | pointed structure of `Rep(B)` (Dong), separability of `H/B` (connected étale), `hθ`: self-braiding trivial on `L₋` (Huang / Dong–Lepowsky) |
| Coequalizer identification | 4900–4934 | `SeparableTensor.isSplitCoequalizer` (`Category/SeparableCoequalizer`) | — |
| "9/3 = 3" | 4383–4406 | `RightMod.netCount_simple_modules(_of_separable)` | as for `L_untwisted` |
| Pivotal uniqueness | 4109–4115 | `Fusion.IsHIRing.pivotalStructure_eq` (`Category/DoubleDual`, `Category/Pivotal`) | — |
| Forgetful embedding, algebraic core | 3349–3352 | `ModuleTower.TowerMod.forget_isEquivalence`, `tensorComparisonIsColimit`, `tensorComparison_assoc` | the braided specialization to local modules |
| Lattice certificates (modulo `FLMBorcherds`) | ledger 5236–5297 | `certDimensions_latticeD`, `minimalGeneration_latticeD`, `S2span_eq_closureSpace`, `certPCT_latticeD`, `pctModeCompatible` (unconditional), the 18 triplet controls in `P4Link`, `P4Left`, `P4RFRP`, `P4RFRZ`, `P4RFRM`, `P4RERP`, `P4RDerived`, `P4NonZero`; `S2savedSpan_eq`; `L2_P4_latticeDP`, `KS21_latticeDP` | see W2 |

**Still hypotheses:**

| Item | Manuscript | Lean form (file) | Arrow affected |
|---|---|---|---|
| Lists of center simples (forgetful images, dimensions, twists) | 3392–3449, 3836–3913 | parameters of `TwistTraces`, `CenterDimension`, `M6BalancedModular` (Ostrik's induction–codegree correspondence) | `L_notRankFour`, `L_rankSixMoments` |
| Bischoff–Jones `K₀(𝓕)⊗ℂ ≅ End(H)` | 3799 | `BJIso` (`Fusion/EndHSchur`) | `L_rankSixRing` |
| `lem:vacuum-projective`: finite length from `C₂`-cofiniteness (Huang, Miyamoto) | 2959–2961 | hypotheses of `VacuumProjective.maxGenEigenspace_eq_bot_of_filtration` | `L_projectiveVacuum` |
| Characters as `q`-series; finite image (DLN); `S_{0,c₁} ≠ 0` (Huang) | 4140–4159 | hypotheses of `CharacterUniqueness.haagerup_character_unique` | `L_characters` |
| Self-braiding of `L₋` trivial (`hθ`) | 3335 | input of `untwisted_vec_equivalence_of_separable` | `L_untwisted` |
| von Neumann algebra clause of `lem:analytic-graph-reduction` | 4455– | not stated (`Analytic/GraphReduction`) | `L_netCount` |
| VOA-side data of the rank-four theta argument | 3615–3770 | fields of `ProofMapConcreteRankFourVoa` | `L_notRankFour` |

Not formalized at all: the braided specialization of the module tower to local modules, Gui's
unitarity (`L_boundaryUnitary`), and the module, net and unitary-category foundations behind the four
open arrows `L_rational`, `L_reconstruction`, `L_annulus`, `L_boundaryUnitary`.

### 1.2 Certificates (the five `C_` inputs of `ProofMap`)

**Lean form.** The certificates are stated as subspace memberships of actual vectors:

* `LowerCertificate`, `Gate4Certificate` and `Gate5Certificate` (`Properness/Setup`, `Gate4`,
  `Gate5`);
* minimal generation `hmin`;
* `dim K = 6` and `dim B₁ = 86`;
* PCT `θ_g S₂ = S₂`;
* the structural inputs: Potts and PF13 fields, the positive stress identity, the core `T` and
  its spectral witnesses, and irreducibility of the 80 currents and the four 81-dimensional
  tops;
* the discriminant form.

**The ledger records are mostly attestations.**  The JSON files listed in the ledger (manuscript
5236–5297) hold hashes, counts and status flags, typically 4–100 KB each.  The exception is
`c8two_structure_saturation.json` at 1.7 MB.

**The witness data lives elsewhere** (sizes measured 1 October):

| Data | Size |
|---|---|
| `hi_cft_20260923_c8two_targeted_h4_{trimmed_v2,normalized,support}/` | about 250 MB each |
| `hi_cft_20260923_c8two_targeted_h4_bulk/` | 194 MB |
| `hi_cft_20260923_next_grade4_checkpoint/` | 46 MB |
| `hi_cft_20260923_c8two_structure_h4_raised_exact/` | 27 MB |
| `*.sqlite` stores | 2–12 MB each |

**The Python engine never builds ambient weight bases.**
`hi_cft_20260923_proof_general_modes_v2.py` computes modes recursively, with a grade ceiling of
4.  Field elements are written in the basis `1, s, t, st` with `s² = 13`, `t² = -3`.

### 1.3 External theorems

There are 11 `E_` arrows in `ProofMap`, plus external inputs stated inline in the modules.

The `E_` arrows cite:

* CKLW 5.29;
* DMNO;
* Gannon–Schopieray–Yadav (GSY);
* Tener and Longo;
* Izumi;
* Grossman–Snyder and Reutter;
* Longo–Rehren and Müger;
* Rehren;
* the E₈ extension (HKL, Gui, Dong–Mason).

The inline inputs cite:

* Larson Theorems 1.1 and 1.3 (1.3 for `c > 1`);
* DLN Theorems I and II(iii);
* Ostrik;
* Ng–Schauenburg;
* EGO;
* Zhu, Huang, McRae and Etingof–Penneys;
* RLYG;
* Abe–Buhl–Dong.

`README.md` lists them under "Trust boundary".

### 1.4 Foundations

* **The lattice VOA is not constructed.**  `B = V_{E₆⊕A₂}` is an object that satisfies the
  `BorcherdsVertexAlgebra` interface (FLM).
* **Modules are only partly modelled.**  `VacuumLike.WeakModule` has modes, translation,
  truncation and the iterate formula, but no `L(0)` grading.
* **Missing entirely:** Zhu algebras, regularity, tensor categories of modules, and conformal
  nets.

## 2. Work items

Sizes are in six-hour sessions and are rough.

### W1. Lattice VOA in Lean: definition and first kernel checks (feasibility study for W2)

**Done (1 October 2026, evening).** `Lattice/` (namespace `LatticeVOA`): computable Fock model
(`Fock`, `Modes`: states `Mom × List ℕ`, sorted sparse vectors over `ℚ`, Heisenberg modes, Schur
coefficients, the FLM vertex operator with `ε`, the iterate recursion, exact at every grade),
semantic layer (`Semantic`: `toFock_mode`, `Y`, `gradeSpace`), `Roots` (`norm_eq_two_iff`: the
norm-2 vectors are exactly the 78 roots, by a Fincke–Pohst tree in the kernel), `Dimensions`
(`certDimensions_model : finrank K = 6 ∧ finrank (gradeSpace 1) = 86`, the two dimension facts of
`certDimensions`; its third conjunct, the 𝔰𝔩₂ ⊕ 𝔰𝔩₂ brackets, follows from `Relations`), `Relations` (current
OPEs at levels 1 and 39, left/right commute), `CentralCharge` (`ω_(3) ω = 4·𝟏`, `c = 8`),
`Samples*` (all 822 exported samples of `basis_mode` agree with the Python engine; no convention
mismatch).  Benchmark and W2 estimates: `Lattice/Benchmark.md` (about 1.5 ms kernel time per
output term; `ℚ(√13,√-3)` multiplication with 400-bit coefficients about 2 ms; one heavy
declaration keeps about 0.45 MiB per ms of kernel time, so files are split to ≤ 2 s of kernel
time).  Estimates: minimal generation and PCT minutes; Gate 5 5–30 min; `P₄` controls 1–2 h;
3,970 lower relations 2–8 h; Gate 4 out of reach for the kernel (option (b) or the reduced
witness format).  Reference data: `lean/tools/lattice_export/` (`samples.json`, `fields.json`,
`s2.json`; generators `export_*.py`, run by root through the guard).  The original plan follows.

* **Goal.** A computable Lean definition of `B` and its modes that matches
  `hi_cft_20260923_proof_general_modes_v2.py` and `hi_cft_20260923_c8_exact.py`.  The pieces
  are:
  - the Fock space `S(ĥ⁻) ⊗ ℚ[L]` with its grading;
  - the Heisenberg modes;
  - the cocycle `ε`;
  - the modes of `e^α`;
  - the iterate recursion for oscillator states.
* **Already have.**
  - `Data/Lattice`: Gram matrix equal to the Cartan matrix of `E₆ ⊕ A₂`, `det = 9`, and the
    cocycle identities.
  - `Data/Spectra` and `Data/Weights`.
  - `Sl2/CurrentBounds` describes the charge of Fock monomials.
* **Mathlib.** `Algebra/Vertex/{VertexOperator,HVertexOperator}` define formal series of linear
  maps only.  There is no Heisenberg or lattice vertex algebra.
* **Steps.**
  1. Data representation (sparse, computable, over ℚ or ℤ, so that `decide +kernel` can
     evaluate it).
  2. Modes on bounded grades.
  3. Cross-check a sample of modes against vectors exported by the Python engine.
  4. Prove `dim B₁ = 86` and that the six currents span `K`, by kernel computation.
  5. Check one grade-2 OPE identity from the unitary certificate.
* **Deliverable.** The checks above, plus recorded time and memory figures.  Those figures decide
  the strategy for W2.
* **Size.** 1–2 sessions.
* **Risk.** Kernel-reduction performance of the chosen representation.
* **Done when.** The `certDimensions` node holds for the Lean `B` as a theorem, and the benchmark
  is recorded here.

### W2. Certificate checker

**Session 3 (4 October 2026).** Kernel replays about the lattice model, all modulo `FLMBorcherds`
(measurements and the summary for the decision on option (b) in `Lattice/Benchmark.md` §5):
minimal generation (`S2Link.minimalGeneration_latticeD`, `finrank_S2span`), the full closure of `S₂`
(`S2Closure.S2span_eq_closureSpace`: all 644 operator images, the 120 that create the basis and
the 524 closure relations), PCT (`PCTLink.certPCT_latticeD`, θ_g = eq:pct; and **θ_g is an
antilinear automorphism of the model**, `PCTModes.pctModeCompatible`, unconditional: a
sesquilinear reduction to basis states plus `ε(−α,−β) = ε(α,β)`), the actual triplet `P₄` in
`latticeDP` (`P4Link`) with **all 18 current identities** (`P4Link`, `P4Left`; the `F_R`
controls `P4RFRP`, `P4RFRZ`, `P4RFRM`; `eR_qp` in `P4RERP`; `eR_q0`, `eR_qm` from the `𝔰𝔩₂`
bracket in `P4RDerived`), and the triplet vectors are nonzero (`P4NonZero`).  The saved `S₂` basis
(`r2_*` rows of the record) spans exactly `S2span` (`S2Saved.S2savedSpan_eq`; lemma
`toV4_combo_saved_mem` for importing records keyed to it), and `L(2)P₄ ⊂ S₂`
(`P4RL2.L2_P4_latticeDP`: `ω_(3) q₊` replayed, `q₀, q₋` by `[L(2), F_R(0)] = 0`, `P4L2Red`), and
`K_(1) S₂ ⊆ K` (`KS21.KS21_latticeDP`: 720 `modeQRF` checks, 320 s of kernel time, peak 1.41 GiB).  Faster evaluators `ModeQ`, `ModeQR`, `ModeHH` (24× on `ω_(3)`)
with link theorems to `modeC`.  Written, not run: `gen_s3.py` (S₃ import), `p4_chunks.py` (shared
chunking).  Open: `L(1)P₄ ⊂ S₃` (needs an `L1_qp` export by the root and `S₃` as a concrete
submodule: about 140 of the 956 `r3_*` rows suffice for membership; about 15 queue-minutes of checks
per vector), `P₄_prov` (not scoped), `S₂S₂1`, `S₂S₂2` (`120 × 120` products; by the `KS₂1` method
about 10⁴ s of kernel time each, probe first), the S₃ import (3–4 queue-hours), the
3,970 lower relations (10–50 queue-hours), Gates 4/5 (out of kernel reach): **decision needed on
option (b)**.  An audit of the statement layer (4 October) found no errors.

**Option (c) largely done (1 October 2026, evening):** `Lattice/QA` (`ℚ(√13,√-3)`), `Model`,
`ModelGrading`, `ModelVacuum`, `VOA`, `S2Data`: the model on the sorted subspace
`V = ValidState →₀ ℂ`, every field of `BorcherdsVertexAlgebra` except the Borcherds identity proved
(grading, CFT type, `mode_grade`, truncation, vacuum axioms), `latticeVOA` from the single
hypothesis `FLMInput` (the Borcherds identity, `L(0)` grading, `L(-1) = ω_(0)`), and
`certDimensions_lattice`: the full `certDimensions` node (incl. `IsSl2SumSpan`) for this algebra.
**Not yet compiled** (the queue was blocked by another session's exclusive guard job for the last
hour): the kernel replay of minimal generation, drafted in `lean/tools/lattice_export/drafts/`
(`S2Core`, `S2Pivots`, `S2Rel00–43`, `S2MinGen`, `S2Link`; pilot checked: relations agree with
`s2.json`; estimate about 200 s of kernel time), giving `minimalGeneration_latticeD`,
`proper_latticeD`.  Remaining: the 524 closure relations (about 490 s, 100 files), exports of the
`S₃` basis, `q±, q₀`, the PCT map; `LowerCertificate`, Gates 4/5; reducing `FLMInput.L0`/`Lm1` to
finite checks (details: `Lattice/Benchmark.md` §5).  **Decision needed from you:** option (b) (compiled checker, `native_decide`) is the
only realistic route for Gate 4 and probably for the 3,970 lower relations; it adds Lean's compiler
to the trusted base.

* **Goal.** Replace the certificate hypotheses by theorems about W1's `B`, or at least state
  them about W1's `B`.
* **Option (c), semantic link.**  Restate every certificate field about W1's `B`, keeping the
  Python verification as provenance.  About one session after W1, with no new trust.
* **Option (a), kernel replay.**  Re-export each record as compact sparse witnesses (integer
  cleared, basis `1, s, t, st`) and prove each field by `decide +kernel`.
  - Plausible for the small records: minimal generation (24 → 120), PCT, the 3,970 lower
    relations, P₄ controls, and Gate 5's 24 channels.
  - For Gate 4, replaying the about 250 MB targeted-identity directories is unrealistic.  The
    manuscript's own reduction is the witness format to target: 12 projected residuals, 644
    saturation images in a quotient of dimension 322, and singlet recovery.
* **Option (b), compiled checker** (`native_decide` / `Lean.ofReduceBool`).  Much faster, but it
  adds Lean's compiler to the trusted base, which this project has avoided so far.  **This needs
  your decision.**
* **Recommendation.** Do (c) right after W1.  Then do (a) record by record, smallest first.
  Consider (b) only for the records where (a) exceeds the budget.
* **Size.** (c) about 1 session.  (a) several sessions; the number depends on the W1 benchmark.

### W3. Borcherds identity for `B` (FLM)

**Session 3 (4 October 2026).** See `Lattice/W3_PLAN.md` (state-of-W3 summary).  `FLMInput` reduces
to `FLMBorcherds` (`FLMReduce`; `L(0)`, `L(-1)` derived).  New: Good-vector calculus, Dong's lemma for
all `n`, abstract local fields (`VertexAlgebra/BorcherdsReduce` … `BorcherdsFieldE`:
`OpField.borcherds_of_local`, `OpField.dong`, `OpField.assoc_of_local`), and
`Lattice/FLMBorcherdsGen`, `FLMBorcherdsIter`: `FLMBorcherds` follows from (1) closure under
products (`IterClosed` or `AssocStep`; open: the bridge `ModeAlgebra → OpField`, Li's E-level
locality, weak associativity of the E-action; 1.5–2 sessions) and (2) `Good` for the 24 generator
fields (several sessions).  An audit (4 October) found no errors.

* **Goal.** A `BorcherdsVertexAlgebra` instance for W1's `B`.
* **What it takes.**
  - Formal distributions and delta functions.
  - Locality of the Heisenberg fields and of `Γ_α(z)Γ_β(w) = ε(α,β)(z-w)^{(α,β)}:Γ_αΓ_β:`.
  - Either the existence theorem (mutually local, translation-covariant fields with a vacuum
    generate a vertex algebra) or FLM's direct Jacobi-identity proof.
  - Dong's lemma.
* **Size.** Many sessions (weeks); this would also be a substantial Mathlib contribution.
* **Until then.** Keep a single named hypothesis, "`B` satisfies the Borcherds identity" (FLM),
  after W1/W2.  That moves the trust boundary from "the Python records are correct" to "FLM".

### W4. Galois averaging for sums of roots of unity (closes `Conductor40Bound` and `NonresidueOrbitStep`)

**Done (1 October 2026, evening).** `NumberTheory/GaloisAverage.lean` (general machinery for a real
primitive character of conductor `c`: conjugation principle via the cyclotomic minimal polynomial,
traces over `(ℤ/N)ˣ`, fibre lemma, shift vanishing, character-twist vanishing, CRT product,
triangle-equality bound), `Conductor40Proof.lean` (`conductor40Bound`), `ThirteenOrbit.lean`
(`nonresidueOrbitStep`, `six_residual_twists_proved`).  Corollaries `multiplicity_eq_one_of_larson`,
`multiplicity_eq_one_of_family_of_larson`, `rank6_multiplicity_one_and_twists_of_larson` keep only
`LarsonRootCount`, and **Larson's Theorem 1.3 itself is proved** for squarefree `c > 1`
(`NumberTheory/LarsonProof.lean`, `larsonRootCount`: Legendre characters via Mathlib's quadratic
Gauss sums, products of real primitive characters with coprime conductors, `χ₄`, `χ₈`, `χ₈'`), so
`multiplicity_eq_one_unconditional` and `rank6_multiplicity_one_and_twists_unconditional` have no
external hypothesis.  The route needs no Ramanujan sums, Möbius values or imprimitive Gauss sums.  The
original plan follows for the record.

* **Math.**
  1. Place the roots in `ℚ(ζ_N) ⊂ ℂ`.
  2. Average over the index-2 subgroup of `Gal(ℚ(ζ_N)/ℚ) ≅ (ℤ/N)ˣ` that fixes `√D`, with
     `D = 10` or `13`.
  3. Evaluate the orbit averages through Ramanujan sums and imprimitive quadratic Gauss sums.
  4. Compare the `√D`-coefficients.
* **Already have.**
  - `NumberTheory/Conductor40`: the explicit orbits `O₊`, `O₋`, orbit sums `±√10`, and
    sharpness.
  - `NumberTheory/Thirteen`: the periods `(-1 ± √13)/2` and independence of the nonresidue
    powers.
  - `LarsonRootCount` (external, `c > 1`).
* **Mathlib.**
  - `IsCyclotomicExtension.autEquivPow` (`NumberTheory/Cyclotomic/Gal`).
  - Irreducibility of cyclotomic polynomials over ℚ.
  - `gaussSum`, `gaussSum_sq` (`NumberTheory/GaussSum`).
  - No Ramanujan sums: prove the needed Möbius evaluation directly.
* **Size.** 2–3 sessions.  It is self-contained, needs no heavy computation, and closes two of the
  three conditional arrows.
* **Risk.**
  - Embedding bookkeeping: abstract cyclotomic fields versus roots of unity in `ℂ`.
  - The all-conductor case analysis in `lem:conductor40`.
* **First step.** An explicit formula for the average of `ζ_N^a` over `Gal(ℚ(ζ_N)/ℚ(√D))`; test it
  on `N = 40` and on multiples of `13`.

### W5. PF13 Wick claims `A₆` (on `a₀b`), `A₇`, `A₈`, `B₇` (closes `L_pf13`)

**Done (1 October 2026, evening).** `VertexAlgebra/PF13WickBasic.lean` (`rnf`: right-normed
spanning from the iterate formula; `probe`: mode form of the DSK Wick identity),
`VertexAlgebra/PF13Wick.lean` (stages `A₆, A₇, B₆, A₈, B₇` for all normal polynomials of the given
weight, rows `b_n b`, `b_n d`, `Data.claims`, `Data.all_pairs`, `pf13_reconstruction'` and
`pf13_reconstruction_of_rows` without `hab2, hab3, hab4`).  Paper pass:
`VertexAlgebra/PF13_PAPER_PASS.md` (findings G1–G6, summarized in §4).  The original plan follows.

* **Math** (manuscript 2760–2811).
  - Normal polynomials of weight `≤ 8`, with the table of two-factor cores.
  - The noncommutative Wick identity (DSK).
  - The acyclic order `A₆ → b_n b → A₇ → b_n d → B₆ → A₈ → B₇ → d_n d`.
* **Already have.** `VertexAlgebra/{FilteredWick, NormalWords, PF13, Diagonal}`, with
  `PF13.iterate_one_mem` and `all_pairs`.
* **Size.** About 2 sessions.
* **Risk.** Medium to high.  The manuscript argument is a sketch ("reversing the order of a core
  uses skew symmetry…"), so formalizing it also checks the proof.  Do a careful paper pass first.

### W6. Theta identities `hcancel` (closes the `m = 3, 6` rank-four cases)

**Done (4 October 2026) up to VOA-side inputs.** Phases 0–5 of `Theta/W6_PLAN.md`; the four
`Theta.*_obstruction_of_voa` theorems give the `dim U₁` formulas without `hcancel`; the SL₂ relations
of the four even Weil blocks are proved (`WeilSanity*`), so the capstones are not vacuous through a
sign slip; the `G₆⁻` capstone uses the 6-dimensional swap-symmetric block (`M6ReverseSym`).
Remaining inputs (VOA side): σ, `V`, its `q`-expansion and polar data.  An audit (4 October) found
all capstones sound.

**Phase 1 done (1 October 2026, evening):** `Theta/PoissonPi` (multi-dimensional Poisson summation
`tsum_eq_tsum_fourierPi`, via Fourier series on `UnitAddTorus d`), `PoissonGaussian` (Gaussian
Fourier transforms for quadratic forms, `tsum_exp_qf_poisson`), `LatticeTheta` (`latticeTheta_S`,
`latticeTheta_T`, coset invariance), `LatticeThetaHarmonic` (Hecke's identity for quadratic
harmonic weights, `latticeThetaQ_S`, weight `d/2 + 2`), `LatticeThetaHolomorphic` (holomorphy on
`ℍ` in the `MDiff` form of `pole_cancellation`), `LatticeThetaModular` (`covariant_of_S_T`: `S`- and
`T`-covariance give `SL(2, ℤ)`-covariance).  No hypotheses beyond the definitions.  Remaining
plan (about 5–7 sessions): `Theta/W6_PLAN.md`.  Phase 2 (audit fixes compiled; `latticeThetaQ_add_intVec`,
`_neg`): lattice data for the four lattices (Smith-form residue systems, isometries, explicit S/T
exponents), `η⁸` transformation laws and polar bound, and the shell `q`-expansions are written but
**not compiled** (queue blocked) and parked in `lean/tools/w6_drafts/`.  Correction to the text below: Mathlib does have
the `S`-transformation of `η` (`ModularForm.eta_comp_eq_csqrt_I_inv`, `Discriminant.lean`).

* **Math.**
  1. Build vector-valued modular forms from lattice theta series with harmonic coefficients
     (`Theta/Harmonic`, `Theta/NearGroup`) and `η⁸`.
  2. Establish the Weil representation of the discriminant group.
  3. Apply `pole_cancellation`, which is already fully proved.
* **Mathlib.**
  - `η` is defined and holomorphic, with `logDeriv η = (πi/12) E₂`.  I found no `S`-transformation.
  - `jacobiTheta` has its `S`-transformation.
  - Poisson summation is available.
  - There are no lattice theta series and no Weil representation.
* **Size.** 3–5 sessions.

### W7. Link `ProofMap` to the concrete theorems

**Session 3 (4 October 2026):** 26 of 30 `L_` arrows concrete (new: `L_branchB`, `L_branchH`,
`L_rankFork`, `L_noSign`, `L_projectiveVacuum`, `L_rigid`, `L_notRankFour`, `L_netCount`,
`L_untwisted`); simple modules indexed by an arbitrary type, identified with the twelve labels only
under `modularData` (`ProofMapSimples`); `ProofMapLattice.lattice_proof_map` instantiates the proof
map at the actual lattice VOA (264 Lean hypotheses at hand-off, against 288 for
`concrete_proof_map`: the PCT node and 19 of the 26 `LowerCertificate` fields are theorems; the only
new input is `FLMBorcherds`); `TRUST_BOUNDARY.md`.  Open: `L_rational`, `L_reconstruction`,
`L_annulus`, `L_boundaryUnitary`.  Three audits (4 October): no logical errors; all should-fix items
applied (missing premises, inputs supplying conclusion conjuncts are now documented, label forward
dependency removed).

**Done (1 October 2026, evening)** for 13 further arrows (17 of 30 in total; list in `README.md`):
`ProofMapConcreteBoundary`, `Characters`, `PF13`, `Regularity`, `TopBound`, `Unitarity`, combined in
`ProofMapConcrete` (`inputs_of_concrete`, `concrete_proof_map`).  Adversarial audit: no trivialized
arrow; the error found (`Ψ` forcing rank six) and the imprecisions were fixed; `ProofMap` gained the
premise `certDiscriminant` for `L_autInvertible` and `L_unmixed`; `certDimensions`/`weightOne` now
include the 𝔰𝔩₂ ⊕ 𝔰𝔩₂ brackets of `K` (`IsSl2SumSpan`).  Skipped (nodes about objects not
modelled: module categories, tensor categories, nets): `L_projectiveVacuum`, `L_rigid`,
`L_rational`, `L_branchB`, `L_branchH`, `L_rankFork`, `L_noSign`, `L_notRankFour`, `L_untwisted`,
`L_boundaryUnitary`, `L_netCount`, `L_reconstruction`, `L_annulus`.  The original plan follows.

* **Current state.** Only the properness arrows have concrete nodes (`ProofMapProperness.concreteNodes`).
* **Plan.** For each arrow whose core is proved:
  1. Define its node as the conclusion of the concrete Lean theorem.  Remaining inputs become
     visible hypotheses inside the node definitions.
  2. Prove the arrow.
* **Done when.** Every "core argument proved" arrow is a theorem for concrete nodes.
* **Size.** 1–2 sessions.
* **Risk.** A node definition could trivialize its arrow; the audit must check for this.

### W8. Smaller items (each at most one session)

**Session 3 (4 October 2026):** the categorical items are done (§1.1): double dual and pivotal
uniqueness, free induction (monoidal, additive, essentially surjective, an equivalence, a monoidal
equivalence), separable coequalizer, three simple modules, abelian 3-cocycles on ℤ/3, the cocycle of a
pointed braided category, the braided monoidal equivalence `Vec_{ℤ/3} ≃` closure of `L₋`, and the
module tower.  `Category/CATEGORY_PAPER_PASS.md` collects the resulting manuscript feedback.

**Partly done (1 October 2026, evening):** the modular-data items (`Fusion/M6BalancedModular`,
`TwistTraces`, `CenterDimension`) and, for `lem:vacuum-projective`, the module commutator relation,
the generalized-weight-space version, the choice of `v` and the splitting with `L_N(-1) = ω_(0)`
(`Regularity/VacuumProjective`), and the linear algebra of "no negative weights through a composition
series ⇒ lowering modes kill `N_[0]`" (`Regularity/NoNegativeWeights`).  Remaining: the categorical
partials (finite length itself is external: Huang, Miyamoto).

* **`lem:vacuum-projective`.**
  - The choice of `v ∈ N_[0]` with `π v = 𝟏`: generalized eigenspaces of a locally finite
    `L(0)` (`Module.End.genEigenspace`) and their preservation by `π`.
  - The no-negative-weights bookkeeping.
  - The module commutator relation, once `WeakModule` has a conformal vector.
* **Modular-data framework.** An abstract modular datum (`S`, `T`), with the Verlinde formula
  and DLN Galois symmetry as hypotheses.  Derive the rows that `lem:m6-balanced` forces, and
  replace `hVerlinde` by these stated theorems.  `trace1`, `trace2` and `hcenter` would be
  handled the same way, with Ng–Schauenburg as the hypothesis.
* **Categorical partials** (status 4 October 2026; the 1 October list is superseded):
  - **done:** the free-module adjunction and free induction: additive, essentially surjective, an
    equivalence, and a monoidal equivalence onto `𝒞_A` (`Category/FreeModule*`,
    `UntwistedFromSeparable`); the separable coequalizer (`SeparableTensor.isSplitCoequalizer`);
    the "9/3 = 3" count (`RightMod.netCount_simple_modules`); `hmul`, `hnondeg`, `hsplit` from
    categorical properties (`TwistedGroupAlgebraOfUnit`, `NondegFromSeparable`, `LminusSplitting`);
    the untwisted `Vec_{ℤ/3}` (`untwisted_vec_equivalence_of_separable`, modulo `hθ`); the double
    dual and pivotal uniqueness (`Category/DoubleDual`, `Category/Pivotal`); the algebraic core of
    the module tower (`ModuleTower*`);
  - **remaining:** `hθ` (trivial self-braidings on `L₋`) from the lattice braiding; the facts
    behind `hSchur`, `hfusion`, `hA`, `hss` (the pointed structure and semisimplicity of
    `Rep(B)`); the tower comparison as a `Functor.Monoidal` (needs coequalizers in `Bimod B B`
    preserved by `⊗_B`) and its braided specialization; the embedding into `Rep(U)` and `𝓕`.

### W9. Keep cited (not recommended now)

* **The von Neumann algebra clause of graph reduction.**  It needs polar decomposition of
  unbounded operators, which Mathlib lacks.
* **All `E_` arrows and inline external theorems** (1.3).  Each is a research-level
  formalization; they already enter as named hypotheses stating the cited content.
* **`Ψ`** (Bischoff–Jones) and **Larson's restriction `m ∈ {0,2,3,6}`.**

## 3. Suggested order

1. Health check and integration build (§0); commit a checkpoint.
2. **Decision (user):** option (b), a compiled checker, for Gates 4/5 and the lower relations
   (`Lattice/Benchmark.md` §5, "Summary for the decision on option (b)").
3. **W2** with `modeQRF`: `L(1)P₄` (export `L1_qp` partial images first; `S₃` membership from the
   named `r3_*` rows), `P₄_prov`; probe `S₂S₂1`/`S₂S₂2`; the full S₃ import after the decision.
   (Done: the 18 triplet controls, the saved-`S₂` equality, `L(2)P₄`, `KS₂1`.)
4. **W3:** the bridge `ModeAlgebra → OpField`, Li's E-level locality and weak associativity →
   `IterClosed`; then `Good` for the 24 generators.
5. ~~`PCTModeCompatible` for the model~~: done (`Lattice/PCTModes.lean`, 4 October, 16:22).
6. Categorical: the braided specialization of the module tower; `hθ` from the lattice braiding once
   lattice modules exist.
7. The four open arrows need module-category, net and unitary-category foundations (long term).

All compilation goes through the root queue; subagents never admit jobs.

## 4. Notes for the manuscript (collected so far)

* `eq:pct` (lines 1975–1989) is correct as printed: no extra sign on `e^{−α}` is needed for the
  bilinear cocycle.  That `θ_g` is an antilinear automorphism follows directly, with no appeal to
  Dong–Lin, from `ε(−α,−β) = ε(α,β)`, `(−α,−β) = (α,β)` and the multiplicativity of `∏ c̃ᵢ^{αᵢ}`
  (`Lattice/PCTModes.lean`).  A remark could say so.  Dong–Lin is still needed for positivity
  (`E_cklw529`).
* Larson, Theorem 1.3 (line 3936), is false as printed for `c = 1`: `1 = 3 - 2√1` is one root of
  unity.  Quote it for squarefree `c > 1`.
* No citation is given for the regularity and unitarity of `K(𝔰𝔩₂,3)`, `K(𝔰𝔩₂,13)`, `A₁,₁` and
  `A₁,₃₉` (around lines 2697–2721).  ALY is cited only for the top formula.
* "Henriques–Tener Lemma 4.15" (line 4656) does not say which paper it is from.
* `lem:compatible-top` (line 2890) cites nothing; Zhu or Dong–Li–Mason would be natural.
* PF13 sketch (lines 2750–2811), from the W5 paper pass (`VertexAlgebra/PF13_PAPER_PASS.md`): the
  argument is correct and the order `A₆ → b_n b → A₇ → b_n d → B₆ → A₈ → B₇ → d_n d` is acyclic, but
  - (G1, 2759–2760) moving Virasoro operators outside an arbitrarily parenthesized normal word uses
    products of composite factors; state that `lem:filtered-wick`(a) with `w = 8` gives right-normed
    spanning through weight 8;
  - (G2, 2773–2775) commuting `b_n` past Virasoro creation operators also produces nonnegative modes
    `L_(k)` (since `L(m)b ∋ TL, L, 1`); state that Virasoro modes preserve the diagonal span on
    normal polynomials of weight ≤ 8 once the rows up to total weight 8 are known;
  - (G3, 2777–2779) "evaluation of `a_n P`" should read "`a_n P` lies in `D` for every `P ∈ D` of
    weight ≤ r";
  - (G4, 2761–2771) cores also occur with derivatives (`:(Ta)(Ta):`); sesquilinearity reduces their
    brackets but does not remove the derivatives (reversed cores are handled at 2772–2773);
  - (G5, around 2784, 2794) that `a_0 a` has no `d`-component is essential at `A₇` and `A₈`, not at
    `A₆` where it is mentioned; it is automatic by skew symmetry
    (`a_0 a = ½T(a_1 a) − ¼T²(a_2 a) + (1/12)T³(a_3 a) − …`);
  - (G6, 2744–2745) given the full rows `a_n b` in `D`, the hypotheses `a_n b = 0` (`n ≥ 4`),
    `a_3 b ∈ ℂa`, `a_2 b ∈ ℂTa` are never used (`pf13_reconstruction_of_rows`); if they are dropped,
    line 2758 ("linear in generators … under the displayed hypotheses") must be reworded ("lie in
    `D`", via G1/G2).  Independently, `a_0 a`, `a_2 a`, `a_4 a` in the self-row follow from
    `a_1 a = b`, `a_3 a = 2L`, `a_5 a = c/3` by skew symmetry, so the displayed self-row is
    consistent.
* `lem:conductor40` and `lem:six-residual-twists` (W4): the squarefreeness of `u` (lines 3970, 4029)
  is not needed: the sum of the primitive `u`-th powers of a root has absolute value at most `φ(u)`,
  with equality only for `u ≤ 2`.
* Twist traces (`lem:near-group-induction`): the manuscript's `ζ` is an existential primitive cube
  root; both choices are covered (`TwistTraces.neargroup_moments_gen`).
* Categorical arguments (`Category/CATEGORY_PAPER_PASS.md`, 4 October; corrected after an audit):
  correct, with unstated steps.  G1: the identification of the self-braiding on `L₋` with the
  metric-group form `q` (line 3327, "metric group `(ℤ/3)², q`"; line 4383) needs a citation (DGNO
  convention `q(x) = c_{x,x}`; Huang's `θ = e^{2πiL₀}`; or the Dong–Lepowsky lattice braiding).  G4
  (3345–3346): "every free module is a sum of these three simple modules" uses that every homogeneous
  component of the multiplication of `H/B` is nonzero, a standard but unstated fact (it also follows
  from separability).  G5 (3346): the source of separability (connected étale; HKL, KO, DMNO) is not
  cited.  G6 (3346–3348): "summand of a free module ⇒ sub-sum" follows from Krull–Schmidt (`End F_a =
  𝕜`).  H2, P2: small wording fixes.  Shorter arguments: G3 (Eilenberg–Mac Lane for ℤ/3 instead of
  Tannakian reconstruction), G7, H1, H3, P1, R1 (only the direct-ideal argument at 3806–3809).
* Rank four, case `m = 2` (around line 3370): the cited Etingof–Gelaki–Ostrik results concern fusion
  categories of dimension `pq`; check that the cited theorem covers the dimension-12 category there
  (flagged by an audit, not checked against the paper).
