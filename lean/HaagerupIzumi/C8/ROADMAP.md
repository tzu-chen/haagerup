# What remains to formalize: scope and plan

Hand-off of 1 October 2026 (afternoon).  This is the work list for the next sessions.
`README.md` has the module map, the arrow-status table and the trust boundary; `BRIEF.md` has the
agent rules and Lean pitfalls.  Manuscript line numbers refer to
`c8_expanded_20260929/haagerup_c8_expanded.tex`.

## 0. Starting a session

### State at hand-off

* **Size:** 76 files in `HaagerupIzumi/C8/`, about 18,500 lines.
* **Axiom audit:** `C8Axioms.lean` audits 63 headline theorems.  All use only `propext`,
  `Classical.choice` and `Quot.sound`.  There is no `sorry`, `axiom` or `native_decide`.
* **Build state:** `lake build --no-build HaagerupIzumi HaagerupIzumi.C8Axioms` reports *All
  targets up-to-date (4049 jobs)*.
* **After the SSD migration of `~/Codes`:** it is now a bind mount from `/dev/nvme1n1p1`.
  - File times were preserved.
  - All nine Lake packages are at their manifest revisions with no local changes.
  - The toolchain is `v4.33.1`.
* **Git:** nothing is committed (branch `c8-checkpoint-20260927`).  Commit a checkpoint before
  starting new work.

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

| Item | Manuscript | Lean form (file) | Arrow affected |
|---|---|---|---|
| `lem:conductor40` | 3950–3988 | `Conductor40Bound` (`NumberTheory/MultiplicityOne`) | `L_multiplicityOne` |
| Galois-orbit step of `lem:six-residual-twists` | 4019, 4026–4037 | `NonresidueOrbitStep` (`NumberTheory/Thirteen`) | `L_twelveTwists` |
| PF13 Wick claims `A₆` (on `a₀b`), `A₇`, `A₈`, `B₇` | 2777–2811 (prop. at 2733) | `claimA6_a0b`, `claimA7`, `claimA8`, `claimB7` (`VertexAlgebra/PF13Product`) | `L_pf13` (OPE recovery) |
| Theta identities after pole cancellation | 3615–3770 | `hcancel` (`Theta/M3First`, `M3Reverse`, `M6First`, `M6Reverse`) | `L_notRankFour` (`m = 3, 6`) |
| Verlinde rows of `lem:m6-balanced` | 3517–3548 | `hVerlinde` (`Fusion/NearGroup`) | `L_notRankFour` (`m = 6`) |
| Twist traces evaluated on the induction decompositions | 3392–3449, 3835– | `trace1`, `trace2` (`NearGroupMoments`, `RankSixMoments`), `hcenter` (`Fusion/NearGroup`) | `L_notRankFour`, `L_rankSixMoments` |
| `K₀(𝓕)⊗ℂ ≅ ℂ ⊕ ℂ ⊕ M₂(ℂ)` (via Bischoff–Jones) | 3799 | `Ψ : FusionAlgebraIso` (`Fusion/Rank6Iso`) | `L_rankSixRing` |
| `lem:vacuum-projective`, leftovers (rows below) | 2932–2978 | see the three rows below | `L_projectiveVacuum` |
| — module commutator relation `[L(0), a_(n)] = (wt a - n - 1) a_(n)` | 2941–2943 | hypothesis of `CompatibleTop.commutator_step` | `L_projectiveVacuum` |
| — finite length from `C₂`-cofiniteness; no negative weights in the composition factors | 2959–2961 | not stated | `L_projectiveVacuum` |
| — choice of `v ∈ N_[0]` with `π v = 𝟏` | 2971–2973 | not stated (the section itself is `VacuumLike.vacuumLike_section`) | `L_projectiveVacuum` |
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

* **Current state.** Only the properness arrows have concrete nodes (`ProofMapProperness.concreteNodes`).
* **Plan.** For each arrow whose core is proved:
  1. Define its node as the conclusion of the concrete Lean theorem.  Remaining inputs become
     visible hypotheses inside the node definitions.
  2. Prove the arrow.
* **Done when.** Every "core argument proved" arrow is a theorem for concrete nodes.
* **Size.** 1–2 sessions.
* **Risk.** A node definition could trivialize its arrow; the audit must check for this.

### W8. Smaller items (each at most one session)

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
  - the free-module adjunction for `L_untwisted`;
  - the coequalizer identification;
  - the "9/3 = 3" equivalence;
  - pivotal uniqueness.

### W9. Keep cited (not recommended now)

* **The von Neumann algebra clause of graph reduction.**  It needs polar decomposition of
  unbounded operators, which Mathlib lacks.
* **All `E_` arrows and inline external theorems** (1.3).  Each is a research-level
  formalization; they already enter as named hypotheses stating the cited content.
* **`Ψ`** (Bischoff–Jones) and **Larson's restriction `m ∈ {0,2,3,6}`.**

## 3. Suggested order

1. Commit a checkpoint and run the health check (section 0).
2. **W1** (definition and benchmark).  It decides the W2 and W3 strategy.
3. **W4** (Galois averaging).  It is independent of W1 and can run in parallel; no heavy compute.
4. **W5** (PF13 Wick claims).  It also checks the proof.
5. **W7** (concrete nodes).  It is cheap and strengthens the formal guarantee.
6. **W2**, using the option chosen after W1.
7. **W6** and **W8**.
8. **W3**, long term.

W4, W5 and W7 touch disjoint files, so they can go to separate subagents.  All compilation still
goes through the root queue.

## 4. Notes for the manuscript (collected so far)

* Larson, Theorem 1.3 (line 3936), is false as printed for `c = 1`: `1 = 3 - 2√1` is one root of
  unity.  Quote it for squarefree `c > 1`.
* No citation is given for the regularity and unitarity of `K(𝔰𝔩₂,3)`, `K(𝔰𝔩₂,13)`, `A₁,₁` and
  `A₁,₃₉` (around lines 2697–2721).  ALY is cited only for the top formula.
* "Henriques–Tener Lemma 4.15" (line 4656) does not say which paper it is from.
* `lem:compatible-top` (line 2890) cites nothing; Zhu or Dong–Li–Mason would be natural.
* W5 may produce further notes on the PF13 sketch (lines 2760–2811).
