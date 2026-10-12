# Companion documents for the c=8 draft

Both guides now refer to the current expanded manuscript,
`hi_cft_c8_proof.pdf`. Manuscript section, appendix, theorem, and page
references are imported from its LaTeX labels and link directly to the
corresponding PDF destinations. Keep all three PDFs in the same directory
for these links. The mathematical construction is now in Appendices A–L;
the physics material is in Sections 2–7. The earlier 55-page revision is
preserved in `c8_physics_20260927/baseline/`, and its numbering appears
only in the Lean guide's explicitly historical concordance.

- `hi_cft_c8_verification_guide.pdf` gives worked input checks, explicit
  field formulas, finite witnesses, and the distinction between checking
  coordinates and identifying those coordinates with actual VOA modes.
- `hi_cft_c8_lean_assessment.pdf` assesses every manuscript section and
  appendix. It records the exact existing Lean coverage, verified local
  Mathlib APIs, missing definitions/theorems, conversion difficulty, and
  staged completion criteria. Its physics supplement records two newly
  checked algebraic thermal-comparison lemmas with explicit premises.

Both `.tex` files load `c8_physics_20260927/manuscript_refs.tex`, which
uses `xr-hyper` to import `hi_cft_c8_proof.aux`. The updated presentation
fragments are `verification_finite_inputs.tex`, `lean_baseline_assessment.tex`,
and `lean_assessment.tex` in that directory. The verification guide also
uses the unchanged `c8_reviewability_20260927/structural_inputs.tex`.
The original reviewability fragments and certificates remain frozen.

After manuscript edits, **compile the manuscript first, then both guides**,
repeating each build until cross-references settle. The current release
also supplies the manuscript AUX for rebuilding only the companions.
Both use ordinary LaTeX packages and `pdflatex -no-shell-escape`; no
bibliography processor is needed. On this shared desktop, build serially
through `hi_cft_safe_run.py` with `--limit-mib 1536` and `timeout 120s`.
Run the reference audit after building:

```sh
python hi_cft_safe_run.py --limit-mib 512 -- timeout 120s python c8_physics_20260927/check_manuscript_refs.py
```

Its report checks the imported labels against the manuscript PDF's named
destinations and the links emitted by the companion PDFs. The current
`hi_cft_c8_physics_bundle.zip` includes all three PDFs, the companion
sources, the shared references, and their build dependencies. Its archive
verifier rebuilds all three documents in a fresh extraction.

## What the new evidence makes inspectable

| Input | New evidence | Scope of independent checking |
|---|---|---|
| Current conventions and defining vector | Integer Gram matrix, 72 singular brackets, three momentum/charge rows, gauge norm12 | Fresh arithmetic and coefficient extraction without the original mode engine |
| Positive stress identity | Four stress norms, eight overlaps, four rational equations; 337 plain coordinate rows | Actual Fock pairings and full projected vector identity; identifying the projections with Haar averages still uses the invariant-space input |
| Short generation | All120 raw/normalized rows, parent operations, pivot/elimination data, and ten targets in two bases | Rank, all elimination identities, explicit inputs and target expansions; raw mode-product recipes are a separate provenance obligation |
| Potts and PF13 membership | Exact33-word and42-word expressions, full source and target fields, readable coefficient table | Independent exact coordinate sums and grade/Cartan labels; no general VOA construction inferred |
| Gate4 | All12 projected residuals and21 normal column recipes, with a portable vector packet | Full exact saved-vector residuals; construction of the projected vectors, raising premises and saturation ranks remain separate |
| Gate5 | Seven zero brackets, one two-normal-word identity, two nonzero bottom scalars | Exact recombination of saved lower identities; the Jacobi argument is printed in the guide |
| Current80 irreducibility | Actual matrices, positive metric, unique seed, all80 cyclic rows and recipes | Finite matrix and cyclicity statements; identification of matrices with actual lattice zero modes is separate |

The structural field and spectral/top tables are exact transcriptions.
Their source maps distinguish a transcription, a new computation, and
a mathematical deduction. The large nonlinear parafermion identities
and complete grade-three/gate rank inputs have not all been recomputed
by a second lattice engine.

## Files to read first

- `c8_reviewability_20260927/grade2_fields.tsv`: all coefficients of eight
  low-grade fields, in the basis `1,s,t,st` with `s²=13`, `t²=-3`.
- `c8_reviewability_20260927/minimal_generation_witness.recipes.tsv` and
  `.target_coefficients.tsv`: the construction graph and target expansions.
- `c8_reviewability_20260927/membership_witnesses.coefficients.tsv`:
  coefficients and named source words for both membership equations.
- `c8_reviewability_20260927/finite_witnesses.json`: all12 Gate4 coefficient
  lists, normal-word recipes and the complete small Gate5 calculation.
- `c8_reviewability_20260927/current80_witness.json`: sparse metric,
  matrices and the full cyclic-basis certificate.

The JSON witnesses contain full coordinates; the TSV files are reader
views of those witnesses, not replacements for omitted terms.

## Replaying the small checks

All jobs must run serially. The permanent address, host-memory, RSS,
thread and affinity limits apply; the September15 exception is expired.
The reviewed estimates and observed results are in
`c8_reviewability_20260927/resource_review.md`.

From the repository root, the following commands use new output paths:

```sh
python hi_cft_safe_run.py --limit-mib 512 -- timeout 120s python c8_reviewability_20260927/check_readable_inputs.py --output-dir /tmp/c8-readable-review
python hi_cft_safe_run.py --limit-mib 1024 -- python c8_reviewability_20260927/export_minimal_generation.py --verify c8_reviewability_20260927/minimal_generation_witness.json --output /tmp/c8-minimal-generation-check.json
python hi_cft_safe_run.py --limit-mib 1024 -- python c8_reviewability_20260927/check_membership_coordinates.py c8_reviewability_20260927/membership_witnesses.json --output /tmp/c8-membership-check.json
python hi_cft_safe_run.py --limit-mib 1024 -- python c8_reviewability_20260927/check_gate4_packet.py --packet c8_reviewability_20260927/gate4_vectors.jsonl.gz --relations c8_reviewability_20260927/finite_witnesses.json --output /tmp/c8-gate4-check.json
python hi_cft_safe_run.py --limit-mib 1024 -- timeout 180s python c8_reviewability_20260927/check_current80_matrices.py c8_reviewability_20260927/current80_witness.json --output /tmp/c8-current80-check.json
```

Choose fresh names if those outputs already exist. The source-generating
exporters use the original exact lattice engine and are distinct from
the independent coordinate verifiers. The latter are deliberately small
enough to inspect against the formulas in the guide.

All five checks passed in this revision. The portable Gate4 packet
contains 33 vectors and 66,610 terms; its checker used about 35 MiB RSS
and 20 seconds. The independent current80 check verifies the positive
metric, 15 adjoint pairs, 30 invariant actions, the unique seed line,
and all 80 cyclic-basis steps. These are exact finite checks; their
reports state the remaining mode-identification obligations explicitly.

The historical reviewer archive `hi_cft_c8_reviewability_bundle.zip`
includes the original two companion PDFs and their TeX sources, all five
checkers and their data, the resource
launcher, and a SHA-256 manifest. After extracting it, change into its
top-level directory and run the same commands above. The five checks
need only Python's standard library and the supplied files. The archive
uses the supplied Linux resource launcher; it checks `/proc` memory and
cgroup limits before starting each job. Use ordinary Python, without `-O`,
so the independent checkers' assertions remain active. The archive
also includes the reference manuscript and the two existing CFT Lean
source files for reading; it does not bundle a Lean/Mathlib toolchain or
all historical mode-engine databases. Export scripts are supplied for
inspection; regenerating every witness uses the original repository.

## Physics revision and its formalization assessment

The new manuscript fragments and datasets live in
`c8_physics_20260927/`. The assessment identifies them by linked current
title, section or appendix, and page. Its concordance maps the archived
Sections 1–13 and Appendices A–C to current Section 1 and Appendices A–O.
The audit guide gives a shorter linked navigation table for finite inputs,
their mathematical consequences, and the new physical observables.

| New physics material | Evidence supplied | Lean work still required |
|---|---|---|
| Exact characters and spin-resolved spectra | Twelve rational character recurrences through grade24; complete diagonal and E8 spectra through Delta24; Virasoro-primary extraction and reconstruction | Sound recurrence/convolution checker, cutoff-completeness theorem, and connection to actual VOA trace functions and irreducible Virasoro modules |
| Controlled thermal observables | Outward-rounded intervals for Z, free energy, energy, entropy and heat capacity, with a proved modular tail estimate | Formal infinite-sum and moment bounds, convergence/modularity assumptions, and a sound interval evaluator |
| Currents and selected correlators | Exact current identities, rational correlator data, normalization and OPE checks in the explicitly named channels | Sound coefficient algebra, actual mode interpretation, locality/convergence, and the stated external-field interpretation |
| Low-weight primary couplings | Explicit primary bases, Gram data, direct seeds and Ward-identity completion with recorded probes | Completeness/rank interpretation, finite Ward determination theorem, normalization, and identification with actual mode products |
| Modular data, defects and Cardy boundaries | Exact cyclotomic S and fusion data, line eigenvalues, twisted sectors, annuli and boundary g factors | Concrete field embedding plus categorical/full-CFT theorems connecting finite tables to actual defects and boundaries |
| Selected chiral Haagerup symmetry | Canonical-extension forgetful data and tube multiplicity spaces, with the action convention specified | Center/forgetful and bimodule correspondences, invariant-space theorem, and distinction between one chiral factor and both factors |
| Bootstrap comparison | Source-specific plot variables, central-charge conventions and spectral points | Formal source correspondence; a numerical exclusion theorem would additionally need the original functional and certified positivity/error bounds |

The physics addition includes two checked real-number lemmas in
`lean/HaagerupIzumi/CFT/PhysicsBounds.lean`:
`modular_heavy_tail_comparison` derives the heavy-tail bound from the
supplied modular balance and contraction inequality;
`selfdual_tail_first_moment_comparison` divides the supplied first-moment
inequality by a positive cutoff. The guarded compile passed with1.549GiB
peak group RSS; `c8_physics_20260927/physics_lean.log` records only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
Neither lemma proves convergence, modular invariance, termwise
differentiation, the underlying spectral inequalities, or the decimal
interval implementation. The five previously checked CFT declarations
retain exactly the scopes recorded in the baseline assessment.
An exact Python result, a file hash, a TeX build, and a Lean proof have
different scopes. In particular the new physics data do not constitute a
formal proof of the CFT construction, its whole operator algebra, or an
exactly marginal deformation.

The spectrum files distinguish the diagonal U theory (2941 relevant
scalar components and scalar gap2/3) from the selected full E8 theory
(no relevant scalar and scalar gap2). For the E8 theory, the canonical
first chiral H3 action has1488 invariant scalar components at dimension2;
invariance under both independent H3 and H3-opposite factors instead
gives36. These different symmetry conventions are also distinguished in
the formalization assessment.

To regenerate the spectrum into a fresh directory, from the repository
root and with no other numerical job running:

```sh
python hi_cft_safe_run.py --limit-mib 512 -- python c8_physics_20260927/spectrum.py --order 24 --delta-cut 24 --outdir /tmp/c8-physics-spectrum-replay
```

The initial complete spectrum run took0.91seconds and26144KiB peak RSS.
The exporter refuses to overwrite an existing dataset output. Its saved
summary records the exact coefficient controls, source hashes and data
hashes; a final source revision must be paired with its own fresh report.
Only root ran the numerical jobs. The permanent resource constraints
apply unchanged, including the32GiB host reserve and two-thread limit.

The original reviewability ZIP remains the baseline finite-certificate
bundle unless explicitly regenerated. Its historical description above
does not imply that every new physics dataset has been added to that
archive. Use the separately named current physics release and its
manifest when reviewing the expanded manuscript.
