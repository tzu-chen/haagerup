# Central-charge-eight Haagerup manuscript

Substantially revised on 27 September 2026. The original 25-page draft and
review register are preserved in `c8_revision_20260927/baseline/`.

Read `hi_cft_c8_proof.pdf` (78 pages) for the current physics-first revision.
Physics Sections 2–7 occupy pages 7–28, followed by construction appendices.
The current audit and Lean guides use linked manuscript labels, with
current section, appendix, theorem, and page references. Keep their PDFs
beside the manuscript; see `hi_cft_c8_companions_README.md` for the build
order and reference checker.
The earlier 55-page
mathematical revision is preserved in `c8_physics_20260927/baseline/`;
its frozen audit archives retain that version. The construction develops the finite closure,
embedded-factor reconstruction, rationality, branching, fusion-ring,
character and analytic arguments into a research-paper presentation, with
numbered theorems, explicit construction inputs and primary references.
De Sole–Kac, Evans–Gannon and Carpi–Kawahigashi–Longo–Weiner supplied useful
models for proof density, normal-product conventions and analytic scope.

The physics release adds complete spectra with spin through dimension 24,
thermal intervals with tail bounds, the three-point tensor for all 113
weight-two chiral Virasoro primaries (18,365 nonzero entries), explicit
four-point functions, all 1,728 center fusion coefficients, defect spectra,
144 diagonal Cardy annuli and 36 U-preserving E8 annuli. It distinguishes
the diagonal theory from the selected holomorphic extension and compares
the latter with the original published Haagerup bootstrap plots.
See `c8_physics_20260927/README.md` for the data index, normalization,
replay commands and remaining bulk-sewing problem. The updated Lean
assessment covers every added physics section.

## Mathematical status

On the stated exact lattice and embedded-field inputs, the manuscript
proves strong rationality, strong unitarity, the complete gamma=0
Evans–Gannon character vector, and a completely rational conformal net
with unitary ribbon category Z(H3). It constructs the diagonal full net
CFT and a holomorphic net extension with boundary category H3.

The pairwise annulus comparison A1 is also proved. Choosing localized
annulus lifts before undoing one common diffeomorphism lift supplies the
exact module insertion identity, including domains and fractional sector
weights. Together with module exhaustion, this gives complete VOA
unitarity, the unitary ribbon identification of Rep(U), and a selected
holomorphic VOA extension isomorphic to V(E8) with boundary category H3.
The original embedded boundary category remains H2 or H3. The separately
constructed net extension is not identified with the E8 net.

An optional algebraic ribbon-identification proposition uses an additional,
explicit external computer-assisted classification assumption. It is not
used by the main character proof or the net theorem and does not establish
canonical VOA fusion positivity.

The exact structural inputs are collected in a labelled certificate rather
than hidden in general review language. Limited computational replays and
Lean proofs have precise scopes; they do not certify the whole manuscript.
See `hi_cft_c8_manuscript_review.md` for the disposition of the original
R1–R12 obligations and the individual 27 September audit notes for details.

## Sources and compilation

Keep these four files and the `c8_physics_20260927/` TeX/data/figure inputs together:

- `hi_cft_c8_proof.tex`: definitions, finite closure, main theorem statements,
  replay ledger and formalization scope.
- `hi_cft_c8_manuscript_structure.tex`: embedded factors, rationality,
  branching, rank exclusions, modular data and characters.
- `hi_cft_c8_manuscript_analytic.tex`: reconstruction, net realization,
  the pairwise annulus proof, positivity and extensions.
- `hi_cft_c8_bibliography.tex`: primary references.

From this repository, run serially:

```sh
python hi_cft_safe_run.py --limit-mib 1536 -- timeout 120s pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error hi_cft_c8_proof.tex
python hi_cft_safe_run.py --limit-mib 1536 -- timeout 120s pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error hi_cft_c8_proof.tex
```

A further pass may be needed after changes to the contents or pagination.
No bibliography processor or shell escape is required. The current
`hi_cft_c8_physics_bundle.zip` supplies sources, figures, data and replay
inputs. Earlier source ZIPs retain their frozen mathematical revisions.
The full historical certificates remain in the repository; they are not
required merely to compile the PDF.

`hi_cft_c8_revision_checks.zip` contains the new formalizations, replay
summaries, logs and audit notes. It is a review subset; full lattice
reproduction requires the historical repository inputs named in the ledger.

## Exact checks and formalization

The fresh checks are preserved under `c8_revision_20260927/`. They include
original provenance, minimal generation, grade-two PCT/OPE identities,
the exact 956-dimensional grade-three span, Gate4, charged span, Gate5,
all fourteen core tops, the order-thirteen spectral witnesses, four
81-dimensional mixed tops, the Potts field and PF13 membership/stress.
The supplemented final input ledger authenticates source dependencies
omitted from the old bundle while preserving the original frozen records.
It distinguishes semantic replay checks from file hashes.

The new Lean modules are:

- `lean/HaagerupIzumi/CFT/FiniteClosure.lean`: jointly nilpotent saturation,
  projected-residual recovery and the abstract Jacobi bottom witness.
- `lean/HaagerupIzumi/CFT/TopBound.lean`: the exact fourteen-variable linear
  certificate for the 17/10 bound.

Both pass under Lean 4.33.1 / Mathlib 4.33.1 without `sorry` or new axioms.
Their README states what is assumed and what is not formalized. They are
separate from the repository’s existing Evans–Gannon existence development.

## Resource and build records

All numerical work ran serially through the permanent resource guard,
with at most two threads and CPUs, address caps no greater than 6 GiB,
an 8 GiB process-group RSS watchdog, and at least 32 GiB host MemAvailable.
Lattice replays used caps no greater than 2 GiB. The expired September 15
exception was not used. The grade-three replay took about 493 seconds and
peaked at 0.190 GiB; the largest sampled Lean peak was 1.652 GiB.

The earlier 55-page document checks and artifact resolution are recorded in
`c8_revision_20260927/document_audit_complete.json`; the TeX log is
`hi_cft_c8_proof_build.log`. The installed TeX environment emits notices
about an array-package/kernel release mismatch and disabled shell escape.
The document uses no EPS graphics or external commands.

That frozen build has no undefined references, duplicate labels, missing glyphs,
or overfull/underfull boxes. Twelve representative pages were rendered and
visually inspected, covering the main results, finite closure, embedded
factors, top tables, A1, certificate ledger, formalization and references.
