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
