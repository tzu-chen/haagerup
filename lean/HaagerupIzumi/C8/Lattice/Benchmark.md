# W1 benchmark: the lattice VOA `B = V_{E₆⊕A₂}` in the Lean kernel

Measured 1 October 2026 through the root compile queue (`lean/tools/c8q.py`, one Lean process per
file, `-j2`, resource guard).  Every job ran 3–8 s of wall time (about 2–3 s of it is Lean
start-up and `.olean` loading); waiting in the shared queue took 0–485 s.  Times are the kernel times printed by `set_option profiler true`
("type checking took …", sequential elaboration `Elab.async false`, so per declaration); memory is
the guard's "sampled peak scope memory" of the whole Lean process.  The baseline of a process
that imports this directory (Mathlib `.olean` mappings) is about 350–370 MiB.

## 1. What was built

| File | Content |
|---|---|
| `Fock.lean` | `Mom` (8 integer coordinates), `State = Mom × List ℕ` (Python code list), sparse `Vec = List (State × ℚ)` kept strictly sorted; `addVec` = linear merge, `normalize` = insertion sort, `bindVec`; links `Mom.form = Lattice.form`, `Mom.cocycleExp = Lattice.cocycleExp`, `Mom.eps = Lattice.epsilon`; natural-number data encoding (`unzig`, `decState`, `decVec`). |
| `Modes.lean` | `heis` (`hᵢ(m)`), `schur` (Schur coefficients of `E⁻(-α,z)`, enumerated in sorted order), `contract` (`E⁺(-α,z)`), `vertexOp` (`(e^α)_(m)`), `basisModeAux` (iterate recursion), `basisMode`, `mode`.  All structurally recursive. |
| `Semantic.lean` | `Fock = State →₀ ℚ`, `toFock`, `modeOp`, `Y`; `toFock_mode : toFock (mode a m b) = Y (toFock a) m (toFock b)`; `gradeSpace d`; `finrank_gradeSpace_eq`. |
| `Data.lean` (generated) | the 78 roots, the six currents, `ω`. |
| `Roots.lean` | `norm_eq_two_iff : x.norm = 2 ↔ x ∈ roots` (Fincke–Pohst tree from the SOS certificate of `Data/Lattice`). |
| `Dimensions.lean` | `finrank_gradeSpace_one : dim V₁ = 86`, `finrank_K : dim K = 6`, `K_le_gradeSpace_one`, `certDimensions_model` (the two dimension facts; the full node with `IsSl2SumSpan` is `certDimensions_lattice` in `VOA.lean`). |
| `Relations.lean` | full current OPE of `A₁,₁ ⊗ A₁,₃₉` (levels 1 and 39), the two `sl₂` commute, `L(-1), L(0), L(1)` on currents. |
| `CentralCharge.lean` (generated) | `ω_(3) ω = 4 𝟏` (`c = 8`), 24 kernel checks + linearity. |
| `Samples*.lean` (generated) | the 822 exported mode samples, one theorem each. |
| `Bench.lean` | micro-benchmarks (field arithmetic, duplicate checks). |

Generator: `lean/tools/lattice_export/gen_lean.py` (string processing of `samples.json` only).

**Cross-check result: all 822 samples agree** with `basis_mode` of
`hi_cft_20260923_proof_general_modes_v2.py` (`install(4)`), 1,973 output terms, output grades 0–4,
`u` ∈ {𝟏, h₀(-1), h₁(-1), h₂(-1), six `e^α`, h₀(-2), h₀(-1)h₁(-1), e^{α_L}h₂(-1), h₆(-1)²}.  No convention
mismatch was found.  The Lean modes have no grade ceiling (Python returns `()` above
`MAX_GRADE = 4`), so they agree with Python exactly where Python computes.

## 2. Measurements

### Mode evaluation (`decide +kernel` on `basisMode u n v = expected`)

| File | samples | output terms | kernel (s) | elaboration (s) | peak MiB |
|---|---|---|---|---|---|
| `SamplesA` (u = 𝟏, h₀, h₁, h₂) | 228 | 123 | 1.53 | 0.55 | 415 |
| `SamplesB` (u = e^{α_L}, e^{-α₂-α₅}) | 118 | 326 | 0.72 | 0.51 | 421 |
| `SamplesC` (three roots) | 177 | 179 | 0.77 | 0.49 | 413 |
| `SamplesD` (h₀(-2), h₀h₁, h₆²) | 180 | 134 | 1.62 | 0.48 | 429 |
| `SamplesE`, `SamplesF` (e^{α_L}h₂(-1)) | 60 | 379 | 1.09 | 0.56 | 448 |
| `Samples` (u = e^{θ}, θ highest root) | 59 | 832 | 1.32 | 1.11 | 692 |
| **total** | **822** | **1,973** | **7.0** | **3.7** | |

Per sample: about 5 ms for tiny outputs (fixed cost: decoding, grade bookkeeping, recursion
set-up), 140–230 ms for 98-term outputs, 490–640 ms for the 315-term output
(`e^θ_(-3) e^{-θ} = -S₄(θ)`, since `ε(θ,-θ) = -1`).  Decomposition of that sample: decoding the expected vector
≈ 95 ms, computing `basisMode` ≈ 300 ms (of which the Schur polynomial `S₄(θ)` ≈ 140 ms).
**Rule of thumb: ≈ 1.5 ms of kernel time per output term** (grade ≤ 4, small rational
coefficients); oscillator states `u` cost ≈ 1.5× more (iterate recursion).
For comparison, Python computes such a mode in milliseconds: the kernel is roughly 50–100×
slower than the Python engine.

### Dimension facts

| Check | kernel |
|---|---|
| `roots_check` (Fincke–Pohst tree, leaves tested with the SOS partial sum) | 549 ms (1.01 s when the leaves evaluate `Mom.norm`) |
| `roots_keys_nodup` (`List.Nodup` of 78 integer keys, 3,003 comparisons) | 234 ms |
| `Dimensions.lean` (86 states, currents, `K`) | well under 1 s in total; peak 386 MiB |
| `Roots.lean` (build) | peak 651 MiB |

### Grade-two identities

| Check | kernel |
|---|---|
| `left_sl2` (12 modes, `A₁,₁`) | 160 ms |
| `right_sl2` (12 modes on 7-term vectors, `A₁,₃₉`) | 671 ms |
| `left_right_commute` (18 modes) | 416 ms |
| `omega_on_currents` (6 modes of the 24-term `ω`) | 313 ms |
| `central_charge`: 24 checks `(hₐhᵦ)_(3) ω` | 52–105 ms each, 1.81 s total, peak 421 MiB |

### Arithmetic and overheads (`Bench.lean`)

| Check | kernel | per operation |
|---|---|---|
| 73 multiplications in `ℚ(√13,√-3)` (coefficients up to a few hundred bits) | 157 ms | ≈ 2 ms per field multiplication |
| 400 additions of rationals with ≈ 570-bit denominators | 139 ms | ≈ 0.35 ms per addition |
| duplicate check, 3,003 comparisons: `List.Nodup` via `Decidable` | 234 ms | 78 µs |
| same, Boolean checker with `Int` equality | 136 ms | 45 µs |
| same, Boolean checker with `Nat.beq` | 66 ms | 22 µs |

### Elaboration of data

* `ℕ` literals: ≈ 0.16 ms per literal (2,700 literals in 430 ms).
* `ℤ` literals in nested `List (List (List ℤ))` data: the same 2,700 literals exceeded
  1,000,000 heartbeats (24 s of type-class inference).  Hence the zigzag `ℕ` encoding.
* Data defs are `noncomputable` (skips code generation; the kernel does not need it).

### Memory behaviour (important for W2)

* The kernel memory of one declaration grows with the work: ≈ 0.4–0.5 MiB per ms of kernel time
  for a single heavy evaluation (the 315-term sample: ≈ 230 MiB in 0.5 s).
* It is **not returned** after the declaration: two copies of that sample in one file peak at
  +450 MiB, three at +590 MiB above the baseline.  Many light declarations accumulate much less
  (≈ 0.04 MiB per ms: `SamplesA`, 228 declarations, 1.5 s, peak 415 MiB).
* With the default `Elab.async true`, kernel checks of different declarations run concurrently
  and their peaks add up.
* The first version (one theorem per group of 59 samples, parallel elaboration) was killed at
  640 MiB, 1,031 MiB and 808 MiB.  The working layout: one theorem per sample, `Elab.async
  false`, ≤ ~2 s of kernel time per file.
* Note for the queue: a new file path gets the 640 MiB floor reservation; a file whose peak is
  above it is killed with SIGTERM (exit 143), which the runner does not treat as a breach, so
  the reservation only grows on the next manual submission.  Keep new files small.

## 3. Extrapolation to the certificates (ROADMAP §1.2, W2)

Assumptions: ≈ 1.5 ms per output term over ℚ, ×3–5 for coefficients in `ℚ(√13,√-3)` with
~300-bit numbers (one field multiplication ≈ 2 ms); kernel ≈ 50–100× slower than the
Python records' own timings for the same algorithm; data elaboration ≈ 0.16 ms per literal.

| Record | Python | Kernel estimate | Verdict for option (a) |
|---|---|---|---|
| `dim K = 6`, `dim B₁ = 86`, `K ≅ 𝔰𝔩₂ ⊕ 𝔰𝔩₂` | — | done (< 2 s) | **done** (`certDimensions_lattice`, W2) |
| Minimal generation 24 → 120 | 1.6 s | 3–15 min of products, plus a rank-120 certificate (pivot/echelon form, not a 120×120 determinant) | feasible |
| PCT `θ_g S₂ = S₂` | (in the unitary certificate, 18 s total) | minutes, given coordinates of `θ_g v` in the `S₂` basis | feasible |
| Gate 5, 24 channels (4,104 grade-2 input terms) | 1.4 s | 5–30 min | feasible, but it consumes Gate 4 |
| P₄ controls (3 fields × 2,313 terms, 24 controls) | 12.8 s | 1–2 h | borderline; split into ~50 files |
| Lower relations: 3,970 identities, 224,480 input sparse terms, 290-bit coefficients | 78 s | 2–8 h kernel, ≈ 10 min elaboration, ≥ 100 files of ≤ 1 GiB | possible as a long batch only |
| Gate 4 as replayed by the Python verifier (2,145 precomputed seeds from the ~250 MB directories) | 2.9 s *given the seeds* | the seeds themselves are 10⁷–10⁸ terms: 10³–10⁵ h | out of reach |
| Gate 4 in the manuscript's reduced form (12 projected residuals, 644 images in a 322-dim quotient, singlet recovery) | — | grade-5 modes + a rank-322 certificate over `ℚ(√13,√-3)`: days | out of reach without a 10–100× faster representation, or (b) |

## 4. Recommendation for W2

1. **Do option (c) now.**  The concrete model exists: restate every certificate field about
   `Fock` and `Y` of `Lattice/Semantic.lean` (vectors as `toFock` of explicit lists), keeping the
   Python records as provenance.  Every identity that is later proved by kernel evaluation
   plugs in through `Y_eq_of_mode_eq`.  The remaining gap to the abstract
   `VertexOperatorAlgebra` interface is the Borcherds identity for `Y` (W3), to be kept as one
   named hypothesis (FLM) until then.
2. **Option (a), record by record, smallest first** — minimal generation, PCT, Gate 5, the
   P₄ controls — after these performance changes (expected 3–10× together):
   * states as single natural-number keys (comparisons by kernel-accelerated `Nat.blt`/`Nat.beq`
     instead of eight `Int` comparisons; measured 2–3.5× on comparisons);
   * Boolean checkers with soundness lemmas instead of `Decidable` instances on big
     propositions (measured 1.7–3.5×);
   * integer-cleared coefficients in `ℤ⁴` (basis `1, s, t, st`) with one denominator per
     vector instead of `ℚ` normalisation (`gcd`) at every operation;
   * coefficients generalized from `ℚ` to `ℚ(√13,√-3)` (`QA` of `Bench.lean`): the present
     `Vec` is over `ℚ`, enough for the currents and `ω` but not for `u` and the `S₂` basis;
   * one declaration per identity, ≤ ~0.5 s each, `Elab.async false`, ≤ ~30 s per file.
3. **The lower relations** are possible in principle (hours of kernel time, hundreds of
   generated files), **Gate 4** is not, with the kernel alone.  If they are wanted as
   theorems rather than hypotheses, option (b) (a compiled checker, `native_decide`) is the
   realistic route; this enlarges the trusted base by the Lean compiler and needs your decision.

## 5. W2 (option (c) and first option-(a) replay), state at the end of 1 October

### The semantic link (built, exit 0)

| File | Content |
|---|---|
| `QA.lean` | `ℚ(√13,√-3)` (`QA`, multiplication table of `A.__mul__`, `QA.inv`), `QA.toC` into `ℂ` (`s ↦ √13`, `t ↦ √3 i`, multiplicative: `QA.toC_mul`); `Vec4` = four rational components, `Vec4.smulQA`, `Vec4.mode` (sixteen rational modes). |
| `Model.lean` | `V = ValidState →₀ ℂ` (canonical monomials; outputs are canonicalized by sorting, so unsorted code lists never enter), `modeC : ℤ → V →ₗ V →ₗ V`, links `toV_mode`, `toV4_mode`; `gradeC`, `gradeC_internal` (direct sum), `gradeC_zero` (CFT type). |
| `ModelGrading.lean` | `modeC_mem_gradeC` (`mode_grade`), `modeC_eq_zero_of_le` (`mode_trunc`), from the definitions of the modes. |
| `ModelVacuum.lean` | `modeC_vac`, `modeC_vac_nonneg`, `modeC_vac_neg_one` (the vacuum axioms), from the definitions. |
| `VOA.lean` | **`FLMInput`** (the one hypothesis), `latticeBVA : BorcherdsVertexAlgebra ℂ V`, `latticeVOA : VertexOperatorAlgebra ℂ V`, `latticeClosureData`, `certDimensions_lattice` (the full new node: `dim K = 6`, `dim B₁ = 86`, `IsSl2SumSpan`). |
| `S2Data.lean` | data of the minimal-generation record (`u`, 120 echelon vectors, pivots): build 17 s, peak 1.2 GiB (elaboration of ≈ 60,000 literals). |

`FLMInput` = Borcherds identity for `modeC` on homogeneous vectors (exactly the field
`BorcherdsVertexAlgebra.borcherds`) + `L(0) = ω_(1)` acts by the grade + `L(-1) = ω_(0)` is
`a ↦ a_(-2)𝟏`.  Everything else in `BorcherdsVertexAlgebra` is proved.

### Minimal-generation replay (option (a)), measured

* Pilot (`drafts/S2Pilot.lean`, checked exit 0): relations 0 (`c_(-2)𝟏`), 6 (`c_(-1)d`),
  42 (`ω`), 43 (`u`) and the heaviest one, 352 (`F_R(0) r₆₁ = s r₆₅ + ∑ 8 terms`):
  48 ms, 223 ms, 76 ms, < 10 ms and 4.7 s of kernel time; peak 1.4 GiB.  All agree with the
  record (the Lean modes reproduce the Python engine on `QA` vectors).
* Cost model: ≈ 2 ms per rational `basisMode` call (root or `u` on a grade-two state), i.e.
  ≈ 8.5 ms per (operator term × basis state) since each of the four `Vec4` components is
  processed separately; plus ≈ 1 ms per term of the right-hand side.
* The 120 relations that create basis vectors: ≈ 200 s of kernel time, generated as 44 files of
  ≈ 5 s (`drafts/S2Rel00–43.lean`), with `drafts/S2Pivots.lean` (triangularity at the pivots,
  ≈ 10 s), `drafts/S2MinGen.lean` (generated membership proofs, no kernel work) and
  `drafts/S2Link.lean` (`finrank_S2span = 120`, `ω, u ∈ S₂`, `S₂ ≤ U`, the
  `certFiniteClosure` tail, and `proper_latticeD`: properness from `FLMInput` + the remaining
  certificates).  **Not yet compiled**: the queue was blocked by an exclusive job of another
  session.
* The remaining 524 closure relations (`S₂` closed under the five operators): ≈ 490 s of kernel
  time (≈ 100 files) with the present representation.
* Balanced merging in `bindVec` (`mergeAll`, now in `Fock.lean`) made no difference here
  (+10 %): the cost is in the modes and in rational arithmetic, not in accumulation.

### Plan for the remaining records

1. Compile the drafts (≈ 50 queue jobs of ≈ 10 s).  Expected result: `S₂ ≤ U`, `dim S₂ = 120`,
   `ω, u ∈ S₂` as theorems about `latticeVOA`, i.e. the minimal-generation record replayed.
2. Speed-ups before the closure relations, P₄ controls and Gate 5: a sparse type with `QA`
   coefficients (one `basisMode` per state instead of one per component: 2.5× fewer calls on
   the `S₂` basis), integer-cleared coefficients, state keys as natural numbers.
3. Export requests for the root: the `S₃` basis (956 vectors) and the triplet `q₊, q₀, q₋`
   (2,313 terms each) as sparse `QA` vectors, so that `S₃`, `P₄` stop being parameters of
   `latticeD`; the PCT map and the coordinates of `θ_g r_k` in the `r` basis.
4. Reduce `FLMInput.L0`, `FLMInput.Lm1` to finitely many kernel checks on generators plus the
   commutator formula (induction over the Fock monomials), leaving only the Borcherds identity.

### Status note, 4 October 2026 (S2 replay, items 4 and 3)

**Minimal generation replayed (all built, exit 0; axioms `propext`, `Classical.choice`,
`Quot.sound`).**  `S2Core`, `S2Rel00–43` (unchanged drafts), `S2MinGen` (one proof fixed:
`s2u_rel_mem`), `S2Link` (unchanged; `finrank_S2span`, `omegaV_mem_S2span`, `uV_mem_S2span`,
`S2span_le_U`, `minimalGeneration_latticeD`, `certDimensions_latticeD`,
`certFiniteClosure_latticeD_iff`, `proper_latticeD`).  The drafted `S2Pivots.lean` was **not**
usable: one file with all pivot checks hit `bad_alloc` at 4.0 GiB (job `120221-5200f3`), and a
quarter of it (states 90–119 plus per-`k` triangularity via `Vec4.coeff`) again reached 4 GiB.
Replaced by `S2Coeff` (coefficients read off by state comparison only, `coeffsAt`,
`Vec4.PivotAt/AbsentAt`, no rational sums in the kernel), `S2PivotsA–F` (states and grades,
≤ 31 vectors per file), `S2Tri00–32` (triangularity `s2tri_k`, packed to ≤ 2.5 s estimated kernel
time per file) and the assembly `S2Echelon` (same statements `s2basis_states`, `s2basis_length`,
`s2piv_valid`, `s2piv_diag`, `s2piv_low`; renamed so that the queue's memory history of the failed
`S2Pivots.lean` path does not apply).  `gen_s2.py` does not generate this layout yet.

Measured (sampled peak scope memory / kernel time): `S2Rel*` 0.55–2.0 GiB / 1.2–7.7 s per file
(heaviest `S2Rel29`: 2035 MiB, 7.7 s; `S2Rel24`: 1945 MiB, 7.4 s); `S2Tri*` 0.58–1.15 GiB /
1.1–2.9 s; `S2PivotsA–F` 0.40–0.55 GiB / 0.5–1.6 s; `S2Echelon` 0.51 GiB, `S2MinGen` 0.42 GiB,
`S2Link` 0.36 GiB.  **Memory rule of thumb:** the peak grows with the *total* kernel time of a file
(≈ 0.45 GiB + 0.2 GiB per second for the relation files, about half that slope for the
state-comparison checks), not with its largest declaration; keep files at ≤ 3–4 s of kernel time.

**Item 4 done: `FLMInput` reduces to the Borcherds identity** (`FLMGen`, `FLMChecks`,
`FLMReduce`, built).  `flmInput_of_borcherds : FLMBorcherds → FLMInput`,
`flmInput_iff_borcherds`, where `FLMBorcherds` is exactly the field `FLMInput.borcherds`.
Ingredients: `eq_top_of_genClosed` (the Fock model is generated from `𝟏` by the modes of the 24
fields `hᵢ(-1)𝟏`, `e^{±αᵢ}`; proved from the definitions: Heisenberg creation `modeC_hV`,
momentum shift `modeC_eV_lower`); `genList_checks` (kernel, 4.5 s, 1.4 GiB: weight one,
`ω_(0) b = b_(-2)𝟏`, `ω_(1) b = b` on the 24 fields); commutator formula, `mode_T`, `T_mode` of
the Borcherds algebra built from `FLMBorcherds` alone.

**Item 3: export scripts written, not run** (`lean/tools/lattice_export/export_s3.py`,
`export_p4.py`, `export_pct.py`; command lines and memory estimates in their docstrings).
`S₃` (956 rows, ≈ 220,000 terms, ≈ 40 MB JSON) will need splitting into many data files in Lean
(S2Data, ≈ 10,000 terms, took 1.2 GiB to elaborate).

### Status note, 4 October 2026, afternoon (PCT certificate, closure half of minimal generation)

**PCT (`θ_g S₂ = S₂`), built.**  `PCTCore` (the map of manuscript `eq:pct`, lines 1975–1989:
computable `pct4`/`sort4` and the conjugate-linear involution `pctV : V →+ V`, links
`pctV_toV4`, `pctV_pctV`), `PCTRel00–28` (121 kernel checks `sort4 (pct4 r_k) = ∑ cⱼ rⱼ` from
`pct.json`, generated by `tools/lattice_export/gen_pct.py`; probe `θ_g r₁₁₆`: 2.2 s, 0.9 GiB;
files 0.43–1.27 GiB, 1.8–4.5 s, 89 s in total), `PCTLink` (`pctV_mem_S2span`,
`pctV_mem_S2span_iff`, `certPCT_latticeD`, `pctV_vacV`, `pctV_omegaV`).  Not proved: that `θ_g`
commutes with all modes (`PCTModeCompatible`, stated; it is the explicit input `hθ` of `ProofMap.lattice_proof_map`, which proves `θ_g U = U` from it, `pctV_mem_U_latD`).

**Closure half, built.**  `S2Close00–254` (the 524 relations creating no basis vector, generated
by `gen_s2close.py`; 0.39–1.75 GiB, 348 s of kernel time in total; the heaviest single relations
reach 1.66–1.75 GiB / 6–7 s), `S2CloseMem` (membership of all 644 sources in `S2span`),
`S2ClosureOps` (`s2op_mem`), `S2Closure` (`S2Closed_S2span`, and
`S2span_eq_closureSpace : (latticeD …).S₂ = (latticeD …).closureSpace uV`; the Cartan zero modes
by the commutator formula, so this uses `FLMInput`).  The cost model of `gen_s2close.py`
(11/51/80 ms per term of `r_k`) overestimates by 2–5× for most relations.

Queue note: a monolithic `S2Closure.lean` (600-goal `interval_cases`) died with `bad_alloc` at
the 640 MiB floor reservation (job `135258-ed76e3`, exit 134, sampled 456 MiB); the runner does
not treat exit 134 as a breach, so it would not have retried with more memory.  Splitting the
tactic proof (`S2ClosureOps`) fixed it.

### Status note, 4 October 2026, 14:10 (triplet `P₄`; S₃ estimate)

* Triplet data built: `P4DataP0–3`, `P4DataZ0–3`, `P4DataM0–3` (each a quarter of one field,
  about 580 states, 2,300 rational rows, 27,000 literals): 7.9–8.9 s, 0.76–0.81 GiB each
  (`gen_p4.py`).  `P4Cartan` built: Cartan zero modes act diagonally (`modeC_cartan_toV4`), so
  the six Cartan controls reduce to checks on states.
* **Stopped:** the first state check `P4StatesP0` (Valid, grade 4, `H_L`/`H_R` eigenvalues of one
  quarter, rational `cartanEig`) took 20.7 s of kernel time and was escalated to 4096 MiB
  (peak 4085 MiB, job `140741-4ab143`).  Cause: rational arithmetic in `cartanEig`, repeated on
  all four `QA` components.  Planned fix (not run): integer eigenvalue forms (`cartanEig` of
  `hL`, `hR` as integer linear forms in the momentum, proved equal symbolically), states checked
  once, sub-chunks of about 600 rows (probe first).
* Heavy controls (not started): `E_L, F_L, E_R, F_R` zero modes and `L(1), L(2)` on 9,300-row
  vectors.  By the `𝔰𝔩₂` relations (commutator formula, `FLMInput`) the 12 non-Cartan
  identities reduce to six direct ones (`E_L q₊ = 0`, `F_L q₊ = 0`, `E_R q₊ = 0`, `F_R q₊ = q₀`,
  `F_R q₀ = q₋`, `F_R q₋ = 0`), and `L(2)P₄ ⊂ S₂` to `L(2) q₊ ∈ S₂` (`[L(2), F_R(0)] = 0`, `S₂`
  is `F_R`-stable).  Each needs input chunks with partial results `cur_(0) chunkᵢ` exported by
  the mode engine (root), since kernel memory grows about 0.2 GiB per second.  `L(1)P₄ ⊂ S₃`
  needs `S₃` as data.
* **S₃ estimate** (from `s3.json`: 956 rows, 220,376 terms, 766,312 nonzero rational components,
  about 8.7 million literals): in the `P4Data` format, about 320 data files of 27,000 literals
  (0.8 GiB, 8.5 s each), i.e. about 45 min of elaboration in the queue, before any check.

### Status note, 4 October 2026, 14:20 (triplet: Cartan controls done; direct controls stopped)

* Built: `P4Eig` (integer eigenvalue forms `eigZ hLZ`, `eigZ hRZ`, proved equal to `cartanEig`;
  `subsetSorted`), `P4StP0–3`, `P4StZ0–3`, `P4StM0–3` (each state of a chunk checked once:
  2.7–3.0 s, 1.08–1.12 GiB per file; probe of one 580-row component: 2.0 s, 0.91 GiB), `P4Defs`
  (`qpV`, `q0V`, `qmV`), `P4Link`: `triplet_grade_P4`, `latticeDP hF S₃ hS₃` (= `latticeD` with
  the actual triplet), and the six Cartan controls `hL_q_latticeDP`, `hR_qp_latticeDP`,
  `hR_q0_latticeDP`, `hR_qm_latticeDP` of `LowerCertificate`.
* **Stopped:** the mode probe `drafts/P4Probe.lean` (`E_L(0)`, `E_R(0)`, `ω_(3)` on 20 states of
  `q₊`, 80 rational rows) was escalated to 4096 MiB and killed in the first check (job
  `141900-b8bbec`, exit 143, sampled 4071 MiB).  Direct kernel replay of the twelve remaining
  current identities and of `L(2)` on the triplet is therefore out of reach with the present
  `Vec`/`Vec4` representation (vertex operators of roots on grade-four states with large
  `|(α, β)|`); it needs either a faster representation (integer-cleared coefficients, `QA`
  coefficients per state, memoized Schur polynomials) or option (b).  The export script for the
  partial results, `tools/lattice_export/export_p4_controls.py`, is written (not run).

### Status note, 4 October 2026, 14:45 (S₃ probe; `modeQ`; left-current controls done)

**S₃ slice probe** (`drafts/S3Probe.lean`: rows 0, 40, 80 of `s3.json`, 554 terms, 20,418
literals, `P4Data` encoding): checked in 7 s, peak 0.60 GiB.  With the `P4Data` measurements
(27,000 literals: 8.5 s, 0.77 GiB, olean 1.0 MB) the whole `S₃` (8,646,319 literals) needs about
320 data files, about 45 min of elaboration in the queue, and about 320 MB of oleans; the state
checks (as `P4St*`, about 3 s per 600 states) add about 370 files of 3 s.  Feasible in a
dedicated session, not as a side task.

**`modeQ` (new, `ModeQ.lean`, built)**: one `QA` coefficient per state, one `basisMode` per pair
of states, no merging; link theorems `toVQ_modeQ` (= `modeC`) and `toV4_toVec4Q`.  Benchmarks
(`drafts/ModeQProbe*.lean`, kernel time / peak):

| check | old `Vec4.mode` | `modeQ` |
|---|---|---|
| `E_L(0)`, 20 states of `q₊` | (part of the killed probe) | 24 ms |
| `E_R(0)`, 4 states | 170 ms, 0.37 GiB | 136 ms, 0.38 GiB |
| `ω_(3)` (`L(2)`), 4 states | 2.78 s, 1.02 GiB | 0.69 s, 0.54 GiB |
| the failed probe (`E_L`, `E_R`, `ω_(3)` on 20 states) | > 4 GiB, killed | 5.4 s, 1.63 GiB |

So the failed probe was dominated by `ω_(3)` (Heisenberg modes with two oscillators on
grade-four states), and `modeQ` gives about 4× there, 1.25× on root vertex operators.
Extrapolated to the remaining controls with `modeQ`: `E_R`/`F_R` about 55 ms per state, i.e.
about 130 s per control on 2,313 states (four controls: about 520 s, about 175 files of 3 s);
`L(2)q₊` about 220 ms per state, about 500 s (about 170 files).  Both need per-chunk partial
results as data (`export_p4_controls.py`, or `#eval`-generated and kernel-checked), and `L(2)`
also the coordinates of the record's `r2_*` rows in the `S₂` basis.  Option (a) is therefore
feasible but costs about 2–3 h of queue time; option (b) would remove that.

**Left-current controls, built.**  The triplet chunks are now cut at changes of momentum
(`gen_p4.py`; rebuilt `P4Data*`, `P4St*`, `P4Defs`, `P4Link`), so a single root vector acts
chunk by chunk without cancellation across chunks.  `P4EL*`, `P4FL*` (24 checks
`Vec4.mode (Vec4.ofVec e) 0 chunk = 0`; the three chunks with more than 640 states split into
component halves `…a`, `…b`): 2.2–4.9 s, 0.92–1.34 GiB per file.  `P4Left`: `eL_q_latticeDP`,
`fL_q_latticeDP`.  With `P4Link`, 12 of the 18 current identities are theorems about `latticeDP`
(`hL_q`, `eL_q`, `fL_q`, `hR_qp`, `hR_q0`, `hR_qm`); open: `eR_*`, `fR_*` (six), `L1_P₄`, `L2_P₄`,
`P₄_prov`.

### Summary for the decision on option (b) (4 October 2026, 15:00)

#### What kernel replay proves today

Everything below is a theorem about `latticeVOA hF` (namespace `HaagerupIzumi.C8.LatticeVOA`).
The only hypothesis is `hF : FLMInput`, and `flmInput_iff_borcherds` reduces it to the Borcherds
identity for `modeC` (FLM Thm 8.10.2).  Axioms are `propext`, `Classical.choice`, `Quot.sound`;
there is no `native_decide`.

| Node / record | Lean | Files | Kernel time (measured) |
|---|---|---|---|
| `L(0)`, `L(-1)` from Borcherds | `FLMReduce.flmInput_of_borcherds` | `FLMGen`, `FLMChecks`, `FLMReduce` | 4.5 s |
| `certDimensions` | `VOA.certDimensions_lattice`, `S2Link.certDimensions_latticeD` | (earlier) | — |
| minimal generation (24 → 120) | `finrank_S2span`, `omegaV_mem_S2span`, `uV_mem_S2span`, `S2span_le_U` | `S2Rel00–43`, `S2PivotsA–F`, `S2Tri00–32`, `S2Echelon` | 179 + 70 s |
| full `S₂` closure (524 more relations) | `S2Closure.S2span_eq_closureSpace` | `S2Close000–254`, `S2CloseMem`, `S2ClosureOps` | 353 s |
| PCT `θ_g S₂ = S₂` | `PCTLink.certPCT_latticeD`, `pctV_pctV` | `PCTRel00–28` | 89 s |
| triplet `P₄` in the data, 12/18 current identities | `P4Link.latticeDP`, `hL_q`, `hR_qp/q0/qm`, `P4Left.eL_q`, `fL_q` (`…_latticeDP`) | `P4Data*`, `P4St*`, `P4EL*`, `P4FL*` | 33 + 122 s |
| properness, conditional | `S2Link.proper_latticeD` (from the remaining certificates) | — | — |

About 500 queue jobs for about 15 min of kernel time: the queue wall time (about 2 h) is
dominated by per-job overhead (import, about 5 s) and by the file-size limit.

#### The cost model

* Kernel memory grows about 0.2 GiB per second of kernel evaluation in a file (plus about
  0.45 GiB imports), so every file must stay below about 3–4 s of kernel time (1.4 GiB).  A
  check that needs 100 s needs about 30 files and, when its result is not chunk-local,
  partial results as exported data.
* Data: about 27,000 literals per file (8.5 s, 0.8 GiB, 1 MB olean).
* Modes (kernel time per input state of the triplet, grade four): root vertex operators
  `E_L, F_L` about 1–2 ms (`Vec4.mode`, chunk-local, done); `E_R(0)` 55 ms (`modeQ`), 33–36 ms
  (`modeQR`, `modeQRF`); `ω_(3)` 700 ms (`Vec4.mode`), 170 ms (`modeQ`, `modeQR`), **30 ms**
  (`modeQRF`, `ModeHH.lean`: the inner level of the iterate recursion of `h_k(-1)h_l(-1)𝟏`
  replaced by the Heisenberg mode `h_l(m)`, with the link `toVQ_modeQRF = modeC`).
  Profiling (`drafts/ModeQProbeSplit.lean`, `ModeQRProbe.lean`, `ModeHHProbe*.lean`): for `E_R`
  the cost was mostly coefficient arithmetic (fixed by `modeQR`), for `ω_(3)` the nested
  Heisenberg loops of `basisModeAux` (fixed by `modeQRF`).  The failed probe (`E_L`, `E_R`,
  `ω_(3)` on 20 states; more than 4 GiB with `Vec4.mode`) now takes 1.35 s at 0.62 GiB.
  Memoized Schur coefficients would not help: `E_R`, `F_R` use simple roots (Schur polynomials
  of one variable) and `ω` none.  Natural-number state keys were not tried: after `modeQR`
  the final sorting is about a quarter of the `E_R` time and the rest is `vertexOp`.

#### What remains, with `modeQ`/`modeQR` (estimates in queue-hours)

| Item | Kernel time | Files | Queue |
|---|---|---|---|
| `E_R`, `F_R` controls (4 direct, 2 by `𝔰𝔩₂`; `modeQR`), partial images exported (`export_p4_controls.py`, spec `p4_chunks.py`) | about 320 s | about 110 checks + data | 1–1.5 h |
| `L(2)P₄ ⊂ S₂` (`ω_(3) q₊` with `modeQRF`; `q₀, q₋` by `[L(2), F_R(0)] = 0`), `r2_*` rows in the `S₂` basis | about 70 s | about 30 | 0.5 h |
| `S₃` as data (`gen_s3.py`: 320 data files, state checks, triangularity) | about 1,500 s + 45 min elaboration | about 1,000 | 3–4 h |
| `L(1)P₄ ⊂ S₃` (`ω_(2)` on the triplet with `modeQRF`, against `S₃`) | about 300 s | about 100 | 1 h (after `S₃`) |
| 3,970 lower relations (`K`, `S₂` products into `S₂`, `S₃`; products of two `S₂` vectors cost up to about 170 × 170 `basisMode` calls each) | 10⁴–10⁵ s | thousands | 10–50 h |
| Gate 4 (about 250 MB of targeted identities, or the manuscript's 644 saturation images in a 322-dimensional quotient) | out of reach | — | — |
| Gate 5 (24 channels at weight five) | not measured, at least as costly as the lower relations | — | — |

So option (a) (kernel only) can finish the triplet controls (about 2 h) and import `S₃` (about
4 h) in about one more working day of queue time, but the lower relations and Gates 4/5 are not
realistic without a change of method.

#### What option (b) would change

`native_decide` (`Lean.ofReduceBool`) evaluates the same computable definitions (`modeC` links
unchanged: `Vec4.mode`, `modeQ`, `modeQR` and all link theorems stay as they are) with Lean's
compiled code instead of the kernel's interpreter.  Expected: the speed of the Python engine or
better (the engine ran the record's triplet construction with all 18 controls in 12.8 s; the
same controls are about 500 s of kernel time with the fastest kernel evaluators `modeQR`,
`modeQRF` and the chunk-local `E_L`, `F_L`, split into about 170 files), no memory growth per
evaluation, no file-size limit, hence the lower relations and Gates 4/5 become a matter of minutes to hours of compute,
and every remaining record could be replayed in one or a few files.  The price is trust: the
proofs would depend on the axiom `Lean.ofReduceBool` (the Lean compiler, its runtime and the
`GMP`/`Nat` externs are trusted) in addition to the kernel; `#print axioms` would show it, and
it can be confined to named certificate lemmas (e.g. one file per record) so that the kernel-only
part (everything in the table above) stays separate.  A middle way is to use (b) only for Gate 4,
Gate 5 and the lower relations and keep (a) for the rest.

#### Right-current controls (4 October 2026, 15:15)

* `fR_qp` (`F_R(0) q₊ = q₀`) replayed with the exported partial images
  (`p4_controls/fR_qp.jsonl`, spec `p4_chunks.py`, generators `gen_p4ctl.py` and
  `gen_p4ctl_fRqp.py`): sub-chunk inputs `P4SubP0–1`, images `P4ImgFRP0–16`, per-sub-chunk checks
  `P4ChkFRP00–32` (`modeQRF`, about 5 s and 1.5 GiB each), links `P4SubLkP0–3` (split by
  component), image pieces `P4IpFRP*`, `P4IlFRP*`, pieces of `q₀` `P4EpFRP*`, `P4ElFRP0–3`, merge
  pieces `P4MgFRP0–11` (12 ranges of output states; probe: 3.3 s, 1.08 GiB), assembly `P4RFRP`.
  **Built, 15:30**: `fR_qpV : modeC 0 (toV fR) qpV = q0V` and `fR_qp_latticeDP` (the
  `LowerCertificate` field `fR_qp` for `latticeDP`).  The 33 per-sub-chunk checks took 0.04–8.0 s
  at 0.38–2.18 GiB (declared reservation 3072 MiB); the exported `q₀` is exactly `F_R(0) q₊`.
  The single merge check of all 33 images (`P4SumFRP`, job `150440-032c13`) had been escalated to
  4096 MiB and killed; merging by output-state ranges fixed it.
* **Nondegeneracy (15:50)**: `P4NonZero.lean` proves `qpV_ne_zero`, `q0V_ne_zero` and
  `qmV_ne_zero`, plus `qp/q0/qm_ne_zero_latticeDP` for the closure data.  Without these, the
  controls would hold trivially for a zero triplet.  For each vector, the proof takes the first
  state of data chunk 0, a pure exponential `e^β` that occurs in no other chunk.  It checks that
  the coefficient there, summed over the four chunks (`chunksCoeff`), equals the printed element
  `coeffP/Z/M` of `ℚ(√13, √-3)`, and that this element has a kernel-checked inverse.  Built in
  job `154828-3b9a0f`.  **Memory**: the job breached its 2048 MiB declaration and the queue
  requeued it at 4096 MiB; peak 2.80 GiB.  The cost is the three scans over all twelve data
  chunks (about 28,000 rows) in one file.  Split it into one file per vector before any rebuild.
* **`fR_q0` (`F_R(0) q₀ = q₋`), stopped at 15:46.** Built: `P4SubZ0–1`, `P4ImgFRZ0–16`,
  `P4IpFRZ0–14`, `P4EpFRZ0–5`, `P4SubLkZ*`, `P4IlFRZ0–5`, `P4ElFRZ0–3`, `P4MgFRZ0–11` and the
  checks `P4ChkFRZ00–13` (kernel 4.5–9.9 s).  `P4ChkFRZ13` peaked at 2.62 GiB (kernel 9.9 s,
  declared 3072 MiB), above the 2.5 GiB stop line.  Remaining: `P4ChkFRZ14–31` and `P4RFRZ`.
  Before resuming, halve the check sub-chunks of the remaining ranges (about 38 states).
* **Pending files** (generated by `gen_p4ctl2.py`, not built) are in
  `lean/tools/lattice_export/drafts/p4ctl/pending/` (202 files):
  * the rest of `fR_q0`;
  * `fR_qm`, all of it, including `P4SubM0–1` and `P4RFRM`;
  * `eR_qp`, all of it, including `P4RERP`.

  `drafts/p4ctl/P4RDerived.lean` is current; the other files directly in `drafts/p4ctl/` are the
  obsolete single-merge versions.  Build order: `python3 gen_p4ctl2.py <control> 12`.
  LowerCertificate count today: 13 of 18 current identities (`hL_q`, `eL_q`, `fL_q` for the three
  vectors, `hR_qp/q0/qm`, `fR_qp`).
* **Stale docstrings, deliberately not fixed.** Editing the source of a built module changes its
  olean, and Lake then rebuilds every dependent.
  * `S2Data`, `S2Core` and `P4Cartan` are imported by essentially all S2/PCT/P4 files.
  * `S2Link` and `P4Link` are imported by all triplet controls.

  Fix them together at the next deliberate full rebuild:
  * `S2Link.lean:28–30`: `P₄` is now exported (`latticeDP`, `P4Link.lean`).
  * `P4Link.lean:36–37`: `E_L`, `F_L` are in `P4Left`, `fR_qp` is in `P4RFRP`, nondegeneracy is in
    `P4NonZero`.
  * `S2Core.lean:13`, `S2Data.lean:12–13` and the headers of the 33 `S2Tri*.lean` cite
    `S2Pivots.lean`, which is now `S2PivotsA–F` / `S2Echelon`.
  * `P4Cartan.lean:20`: `P4States*` is now `P4St*`.
* **To do before importing records keyed to the saved `S₂` basis** (`L2_P₄`, `S₃`, lower
  closure): replay the equality of the saved basis (`r2_*` rows) with `S2span`.
* **Earlier state of this note** (written before the `fR_q0` run, kept for the method):
  `fR_q0` (`F_R(0) q₀ = q₋`), `fR_qm` (`F_R(0) q₋ = 0`), `eR_qp` (`E_R(0) q₊ = 0`), and
  `P4RDerived.lean` (`eR_q0`, `eR_qm` from the `𝔰𝔩₂` commutator).  To finish them: generalize
  `gen_p4ctl_fRqp.py` to a control argument (input field `Z`/`M`/`P`, expected `qm`/`0`/`0`;
  for the kills the merge pieces compare with `Vec4.zero`-pieces, i.e. `sum4 [...] = Vec4.zero`
  per range, and the expected-vector link is dropped), regenerate, and build in the order
  sub-chunk data and images (data, 0.6 GiB), sub-chunk links by component, per-sub-chunk checks,
  image pieces and links, merge pieces, assembly; then build `P4RDerived`.  The old single-merge
  files `P4Sum*.lean` and assemblies `P4R*.lean` in `drafts/p4ctl/` must not be used.  Queue:
  about 75 jobs (about 15 min) per control.

#### Right-current controls `fR_q0`, `fR_qm` built (4 October 2026, 16:20)

* **`fR_q0` (`F_R(0) q₀ = q₋`)**: the remaining checks `P4ChkFRZ14–31` and the assembly `P4RFRZ`
  are built (files moved unchanged from `drafts/p4ctl/pending/`, no re-chunking).  Before
  launching, each check's kernel time was predicted from the built ones by a linear fit in the
  sub-chunk's total code length and image size; the worst predicted peak was about 3.0 GiB, under
  the 3.3 GiB split line, so the 75-state sub-chunks were kept.  Measured: `P4ChkFRZ14–16` 12.2–13.6 s
  kernel at 2.59–2.68 GiB (declared 3584 MiB), `P4ChkFRZ17` 9.8 s at 2.11 GiB, `P4ChkFRZ18–31`
  3.1–6.0 s at 1.03–1.65 GiB.  `P4RFRZ` (0.53 GiB): `fR_q0V : modeC 0 (toV fR) q0V = qmV` and
  `fR_q0_latticeDP` (the `LowerCertificate` field `fR_q0`), axioms `propext`, `Classical.choice`,
  `Quot.sound`.
* **`fR_qm` (`F_R(0) q₋ = 0`)**: all of it is built: `P4SubM0–1`, `P4ImgFRM0–14`, `P4IpFRM0–13`,
  `P4ChkFRM00–32` (0.4–9.7 s, at most 2.24 GiB), `P4SubLkM00–33`, `P4SubLkM0–3`, `P4IlFRM0–5`,
  `P4MgFRM0–11` (kill: `sum4 [...] = Vec4.zero` per range), `P4RFRM`.  `P4RFRM` (0.56 GiB):
  `fR_qmV : modeC 0 (toV fR) qmV = 0` and `fR_qm_latticeDP`, same three axioms.
* **Generator fix (kill case)**: the generated kill assembly ended with
  `have hg : <all atoms, flat> = <grouped by range> := by abel; rw [hg, m0, …]`, which cannot
  match the goal (its left side is nested by images).  `P4RFRM` instead proves
  `hz : <grouped by range> = 0` by `rw [m0, …, m11]; all_goals simp`, then
  `refine Eq.trans ?_ hz; abel`.  `gen_p4ctl2.py` now generates this, and the pending
  `drafts/p4ctl/pending/P4RERP.lean` was patched the same way; it is still unbuilt and untested.
* LowerCertificate count: 15 of 18 (`hL_q`, `eL_q`, `fL_q` for the three vectors,
  `hR_qp/q0/qm`, `fR_qp`, `fR_q0`, `fR_qm`).  Still pending: `eR_qp` (all files are in
  `pending/`, about 75 jobs) and `P4RDerived` (`eR_q0`, `eR_qm`).

#### `eR_qp` and the derived `eR_q0`, `eR_qm` built (4 October 2026, 16:30)

* **`eR_qp` (`E_R(0) q₊ = 0`)**: built `P4ImgERP0–13`, `P4IpERP0–13`, `P4ChkERP00–32` (at most
  8.5 s and 2.14 GiB; `P4ChkERP13` 8.54 s at 2.12 GiB and `P4ChkERP16` 8.52 s at 2.14 GiB, both
  declared 3584 MiB), `P4IlERP0–5`, `P4MgERP0–11` and `P4RERP`.  The sub-chunk inputs and their
  links are shared with `fR_qp` (`P4SubP0–1`, `P4SubLkP0–3`).  `P4RERP` uses the patched kill
  ending (`hz`, `refine Eq.trans ?_ hz; abel`, see the 16:20 paragraph) and built on the first
  try (0.54 GiB).  It proves `eR_qpV : modeC 0 (toV eR) qpV = 0` and `eR_qp_latticeDP`.
* **`P4RDerived`** (from `drafts/p4ctl/P4RDerived.lean`; the only change is the rename of the
  commutator lemma to `bracket_zero_modeC`) built on the first try (0.37 GiB).  It proves
  `bracket_zero_modeC`, the commutator formula `[e_(0), f_(0)] = (e_(0) f)_(0)` on weight-one
  vectors.  This uses `FLMInput` through `latticeBVA`, the same argument as `cartan_mem` in
  `S2Closure.lean`.  From it, with `right_sl2` (`E_R(0) F_R = H_R`), the controls
  `fR_qpV`, `fR_q0V`, `eR_qpV` and `qpV_facts`/`q0V_facts` (`H_R`) give
  `eR_q0V : modeC 0 (toV eR) q0V = (2 : ℂ) • qpV` and `eR_qmV : modeC 0 (toV eR) qmV = (2 : ℂ) • q0V`.
  It also proves `eR_q0_latticeDP` and `eR_qm_latticeDP` in the `Properness/Setup.lean` field shapes.
* All axioms are `propext`, `Classical.choice`, `Quot.sound`.  LowerCertificate count: **18 of
  18 current identities** of the triplet for `latticeDP` (the closure-data and `L1_P₄`/`L2_P₄`
  fields are separate).  `drafts/p4ctl/pending/` is now empty.

#### Saved `S₂` basis = `S2span`, and `L2_P₄` built (4 October 2026, 16:50)

* **Saved basis.** The checkpoint rows `r2_000000–r2_000119` are `order2`/`rows2` of `s3.json`,
  the basis that `L2_P₄`, `S₃` and the lower closure are keyed to.  Both they and the replayed
  `s2r_k` are echelon at their least states.  Elimination over `ℚ(√13, √-3)` writes each basis in
  terms of the other with zero remainder:
  * 216 coefficients one way, 223 the other;
  * 61 rows coincide;
  * the transition is block-diagonal with at most 6 terms per row.

  This is generated by `gen_s2saved.py`, which reads `s3.json` itself.  Built:
  * `S2SvData0–5`: `s2sv_j : Vec4`, data, 0.4–0.6 GiB;
  * `S2SvIn0–4`: `s2sv_eq_j : s2sv_j = combo [(c, s2r_k), …]`;
  * `S2SvOut0–4`: `s2r_eq_sv_k : s2r_k = combo [(c, s2sv_j), …]`;
  * `S2Saved` (0.69 GiB), which proves
    * `s2saved` and `S2savedSpan`;
    * **`S2savedSpan_eq : S2savedSpan = S2span`**;
    * `s2saved_mem_S2span`;
    * `toV4_combo_saved_mem : (∀ p ∈ l, p.2 ∈ s2saved) → toV4 (combo l) ∈ S2span`, the import
      lemma for records keyed to `r2_*`.

  **Cost lesson:** the pilot model of about 1 ms per right-hand-side term underestimates `combo`
  checks by about 5×.  Measured: about 92 s of kernel time for the ten check files (0.4–14.4 s
  each, peaks 0.39–2.21 GiB).  `S2SvIn2` and `S2SvOut2` breached their declared 2048 MiB on the
  first attempt.  The runner requeued them automatically at 4096 MiB; they then peaked at 1.87
  and 2.21 GiB.  For such checks use about 5 ms per term and at most about 2,500 terms per file.
* **`[L(2), F_R(0)] = 0`** (`P4L2Red`): this file proves
  * `L2_fR_comm` from the commutator formula, `Lm1`, `L0`, `mode_T` and the kernel check
    `omega_two_fR : mode omega 2 fR = []`;
  * `L2_P4_latticeDP_of_qp`: the field follows from `ω_(3) q₊ ∈ S2span`, through `fR_qpV`,
    `fR_q0V` and `fR_mem`.
* **`L(2) q₊ = c · r2_000017`.** This is the record `p4.json` `virasoro_controls`.  `gen_l2qp.py`
  asserts that the exported total equals `c · r2_000017`.  Built:
  * `P4SubL0–1`: 90-state sub-chunks `p4sL_c_j` of `q₊`;
  * `P4ImgL2`: the images;
  * `P4SubLkL00–33`, `P4SubLkL0–3`: the links;
  * `P4ChkL200–27`: `modeQRF omega 3`, 1.4–11.7 s, 181 s in total, peaks up to 2.70 GiB, declared
    2560/3072/3584 MiB by code length;
  * `P4MgL2`: `sum4 images = combo [(c, s2sv_17)]`;
  * `P4RL2`, which proves
    * `L2_qpV`;
    * `L2_qp_mem : modeC 3 omegaV qpV ∈ S2span`;
    * **`L2_P4_latticeDP`**, the `LowerCertificate` field `L2_P₄`.

  A probe of sub-chunk 12 (`drafts/l2/L2Probe12.lean`, not in the tree) took 6.9 s at 1.95 GiB
  before launch.
* Every new file is built; axioms are `propext`, `Classical.choice`, `Quot.sound`.
* Open triplet fields: `L1_P₄` (needs `S₃` as data) and `P₄_prov`.

#### `KS₂1` (`K_(1) S₂ ⊆ K`) built with `modeQRF` (4 October 2026, 17:05)

* **Probe** (`drafts/ks21/KS21Probe.lean`, not in the tree): `r_61`, 72 terms, the heaviest
  vector of the stopped `Vec4.mode` probe.  Kernel times with `modeQRF`:
  * the `QVec`-to-`Vec4` link: 0.47 s;
  * `H_R`: 2.55 s (was 8.3 s with `Vec4.mode`), `H_L`: 2.2 s, `E_R`: 0.71 s, `E_L`: 0.10 s;
  * peak 1.59 GiB.

  This extrapolated to about 350 s for the 720 checks, so the full set was built.
* **Generator:** `gen_ks21q.py`, which replaces the stopped `gen_lower_ks21.py`.  Built:
  * `KsQData0–3`: `s2q_k : QVec`, data, 0.38–0.50 GiB;
  * `KsQLink0–6`: `s2q_link_k : (∀ q ∈ s2q_k, Valid q.1) ∧ nz4 (sort4 (toVec4Q s2q_k)) = s2r_k`, cheap;
  * `KsQChk00–94`: `ks21_<c>_<k> : kOK (nz4 (sort4 (toVec4Q (modeQRF c 1 s2q_k)))) = true` for all
    six currents and all 120 basis vectors.  Measured: 320 s of kernel time in total, at most
    2.4 s per check, peaks at most 1.41 GiB per file (declared 3072 MiB), no requeues;
  * `KS21` (0.53 GiB), which proves
    * `ks21_of_check`, the meaning of one check via `toVQ_modeQRF` and `toV4_mem_Kspan_of_kOK`;
    * `ks21_<c>_S2 : ∀ a ∈ S2span, modeC 1 (toV c) a ∈ Kspan`, by `span_le` along the basis;
    * **`KS21_Kspan : ∀ x ∈ Kspan, ∀ a ∈ S2span, modeC 1 x a ∈ Kspan`**, by `span_le` along
      the six currents for the flipped map;
    * **`KS21_latticeDP`**, the `LowerCertificate` field `KS₂1`.

  Axioms are `propext`, `Classical.choice`, `Quot.sound`.  Queue: about 6 minutes for 107 jobs.
* **Remaining heavy lower fields:** `S₂S₂1` and `S₂S₂2` (`120 × 120` products).
  * Same method: `modeQRF a_(n)` of `QVec` basis vectors, with `a` in the 120-dimensional `S₂`.
  * The modes of grade-two vectors cost more than those of currents (`ω_(3)` on grade four: about
    75 ms per state).
  * `S₂S₂2` lands in `K`, so it is decided by `kOK`.  `S₂S₂1` lands in `S₂` and needs a
    decomposition along the `S₂` echelon basis (pivots `s2piv`, as `kDec`).
  * Rough size: 14,400 pairs × about 30 terms × tens of ms, i.e. 10⁴ s or more each.  Needs a
    probe first.
