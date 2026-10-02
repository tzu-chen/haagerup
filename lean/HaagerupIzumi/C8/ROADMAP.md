# What remains to formalize: scope and plan

Hand-off of 1 October 2026 (evening, end of the second session).  This is the work list for the
next sessions.  `README.md` has the module map, the arrow-status table and the trust boundary;
`BRIEF.md` has the agent rules and Lean pitfalls.  Manuscript line numbers refer to
`c8_expanded_20260929/haagerup_c8_expanded.tex`.

## 0. Starting a session

### State at hand-off

* **Size:** about 134 Lean files in `HaagerupIzumi/C8/`, about 55,000 lines (the lattice sample
  data are a large part), about 2,650 theorems.
* **Axiom audit:** `C8Axioms.lean` audits 119 headline theorems.  At the last green integration
  build (19:47) all 117 then listed used only `propext`, `Classical.choice`, `Quot.sound`.  There is
  no `sorry`, `axiom` or `native_decide` in the source tree.
* **Build state — must be refreshed first.**  The integration build
  `c8_build_all.py --skip-built --keep-going lean/HaagerupIzumi/C8Axioms.lean` was green at 19:47
  (124 of 124 modules).  After that, from about 20:03, another session (`~/Codes/vcc`) held an
  exclusive guard job and every queue job was refused, so these later changes are **not
  re-verified**:
  - `Lattice/Fock.lean`, `Modes.lean` (changed by W2; their direct dependants `Semantic`, `QA`,
    `Model*`, `VOA`, `S2Data` were rebuilt at 19:50–19:52, but `Samples*`, `CentralCharge`, `Bench`
    were not re-checked against them, and `Data`, `Roots`, `Dimensions`, `Relations` have unverified
    docstring edits);
  - the free-module files `Category/FreeModule*.lean` (audit-fix edits in progress when the queue
    blocked; see the agent report in the session log);
  - docstring-only edits by root in `ProofMap.lean` (`certDimensions`), `Data/Weights.lean`, and the
    new registrations in `C8All.lean`, `C8Axioms.lean`.
  So: restart the runner, run the integration build, fix whatever it reports, then continue.
* **Drafts outside the source tree (written, never compiled):**
  `lean/tools/lattice_export/drafts/` (W2: kernel replay of minimal generation),
  `lean/tools/w6_drafts/` (W6 phase 2: `LatticeData`, `Eta8`, `QExpansion`),
  `lean/tools/category_drafts/DoubleDual.lean` (monoidal double dual).
* **Git:** session-start checkpoint `8c79800`; end-of-session checkpoint committed after this
  hand-off (see `git log`).

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

**Still hypotheses:**

| Item | Manuscript | Lean form (file) | Arrow affected |
|---|---|---|---|
| Theta identities after pole cancellation | 3615–3770 | `hcancel` (`Theta/M3First`, `M3Reverse`, `M6First`, `M6Reverse`) | `L_notRankFour` (`m = 3, 6`) |
| Lists of center simples (forgetful images, dimensions, twists) | 3392–3449, 3836–3913 | parameters of `TwistTraces`, `CenterDimension`, `M6BalancedModular` (Ostrik's induction–codegree correspondence) | `L_notRankFour`, `L_rankSixMoments` |
| `K₀(𝓕)⊗ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` (via Bischoff–Jones) | 3799 | `Ψ : FusionAlgebraIso` (`Fusion/Rank6Iso`) | `L_rankSixRing` |
| `lem:vacuum-projective`: finite length from `C₂`-cofiniteness (Huang, Miyamoto); `L(0) - μ` injective on each composition factor for `μ < 0` | 2959–2961 | hypotheses `F`, `hstep` of `VacuumProjective.maxGenEigenspace_eq_bot_of_filtration` (`Regularity/NoNegativeWeights`; the consequence for lowering modes is `lowering_mode_eq_zero`) | `L_projectiveVacuum` |
| `lem:vacuum-projective`: `ω_(0) v = 0` on `N_[0]` (vacuum-top step applied to `N_[0]`) | 2966–2970 | input of `omega_vacuumLike_section` (`CompatibleTop.vacuum_top_step` gives the algebra) | `L_projectiveVacuum` |
| Characters as `q`-series; finite image (DLN); `S_{0,c₁} ≠ 0` (Huang) | 4140–4159 | hypotheses of `CharacterUniqueness.haagerup_character_unique` | `L_characters` |
| von Neumann algebra clause of `lem:analytic-graph-reduction` | 4455– | not stated (`Analytic/GraphReduction`) | `L_netCount` |
| Categorical parts that are only partly formalized | §G, App. J | see the list below | `L_untwisted`, `L_boundaryUnitary`, `L_netCount` |

The categorical parts in the last row:

* the free-module adjunction and the Tannakian identification (`L_untwisted`);
* the coequalizer identification (`Category/RelativeTensor`);
* the "9/3 = 3" module equivalence (`Analytic/NetCount`);
* pivotal uniqueness beyond the based ring (`Fusion/Pivotal`).

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
* **Categorical partials:**
  - the free-module adjunction for `L_untwisted`: **done** (`Category/FreeModule*`: `freeAdjunction`,
    `Hom_A(X⊗A, Y⊗A) ≃ Hom(X, Y⊗A)` linearly, free induction bijective on Hom-sets between the
    three simples of `L₋` (`freeMap_bijective_Lminus`, with `Weights.free_induction_hom_count`),
    every module a retract of a free module for a separable algebra (`retractFree`), and the
    object-level isomorphism `(X⊗A) ⊗_A (Y⊗A) ≅ (X⊗Y) ⊗ A` (`freeTensorIso`)).  Remaining for
    `L_untwisted`: naturality, unit and coherence of `freeTensorIso` and the monoidal structure on
    `𝒞_A`; additivity of free induction; semisimplicity of `𝒞_A` (from separability) and of `Rep(B)`;
    `ℓ ⊗ A ≅ A` for `ℓ ∈ L₊` and hence essential surjectivity; the existence of a separability
    section for `H/B`; the facts behind `hSchur`, `hfusion`, `hA`; the Tannakian identification
    (external: Deligne/EGNO); the embedding into `Rep(U)`;
  - the coequalizer identification;
  - the "9/3 = 3" equivalence;
  - pivotal uniqueness: **done** except the double-dual monoidal functor (Mathlib has no pivotal
    categories): `Category/MonoidalAutomorphism.lean` proves that a monoidal automorphism of
    `𝟭 C` acts on simples by scalars `t` with `t_X t_Y = t_Z` whenever `Z → X ⊗ Y` is nonzero
    (Schur), hence is the identity on a categorification of eq:rank6-ring
    (`IsHIRing.monoidalAut_eq_refl`), and two monoidal isomorphisms `𝟭 ≅ F` agree
    (`IsHIRing.monoidalIso_eq`).  The monoidal double-dual functor is drafted (not compiled; queue
    blocked) in `lean/tools/category_drafts/DoubleDual.lean`; then `Category/Pivotal.lean` is a
    short application of `monoidalIso_eq`.

### W9. Keep cited (not recommended now)

* **The von Neumann algebra clause of graph reduction.**  It needs polar decomposition of
  unbounded operators, which Mathlib lacks.
* **All `E_` arrows and inline external theorems** (1.3).  Each is a research-level
  formalization; they already enter as named hypotheses stating the cited content.
* **`Ψ`** (Bischoff–Jones) and **Larson's restriction `m ∈ {0,2,3,6}`.**

## 3. Suggested order

1. Restart the runner and run the integration build (section 0); fix stale or broken modules.
2. Compile the parked drafts: W2 `S2*` (minimal generation as theorems about `latticeVOA`), W6
   `LatticeData`, `Eta8`, `QExpansion`, and `DoubleDual` + a short `Category/Pivotal.lean`.
3. **W6** phases 3–5 (`Theta/W6_PLAN.md`): λ, μ from the data, the representation σ (external
   inputs named), full polar-part matching, coefficient extraction → `hcancel` as a theorem.
4. **W2** (a), record by record (`Lattice/Benchmark.md` §5): closure relations of `S₂`, exports of
   `S₃`, `q±`, PCT; **decision needed** on option (b) (compiled checker) for Gate 4 and the lower
   relations.
5. **W8**: the rest of `L_untwisted` (naturality/coherence, essential surjectivity); the
   `lem:m6-projection`/`prop:m3-modular` moments from the modular centralizer.
6. **W3** (Borcherds identity for the lattice model, i.e. `FLMInput`), long term.

All compilation goes through the root queue; subagents never admit jobs.

## 4. Notes for the manuscript (collected so far)

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
