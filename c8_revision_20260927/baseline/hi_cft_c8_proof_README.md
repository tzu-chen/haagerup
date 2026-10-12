# Central-charge-eight Haagerup proof manuscript

Prepared and compiled on 23 September 2026.

The compiled manuscript is `hi_cft_c8_proof.pdf` (25 A4 pages).

## Sources and compilation

Keep these three files in the same directory:

- `hi_cft_c8_proof.tex` — main source, explicit fields, finite closure and
  properness proof, comparison with arXiv:2512.08225, certificate ledger.
- `hi_cft_c8_manuscript_structure.tex` — regularity, branching, rank
  exclusions, modular data, and characters.
- `hi_cft_c8_manuscript_analytic.tex` — proposed analytic comparison,
  conditional complete unitarity, categorical identification, and full CFTs.

Compile with:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error hi_cft_c8_proof.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error hi_cft_c8_proof.tex
```

No bibliography processor, shell escape, or numerical computation is needed.
The source ZIP contains these three TeX files, this README, and the build log.
Referenced research certificates and companion proof notes remain in the
project directory; they are not needed to compile and are not included in
this small typesetting bundle.

## Reading the qualifications

Red **HIGH PRIORITY REVIEW** notes identify the analytic claims with the
largest remaining confidence concerns:

- A1: compatibility of the geometric annulus actions and bounded localized
  fields on reconstructed modules.
- A2: actual net branching and the twelve-sector count.
- A3: ordinaryness, irreducibility, and linear full faithfulness of reverse
  module reconstruction.

Amber **REVIEW** notes identify other substantial local deductions and
imported proof inputs: the finite-certificate boundary (F1), the all-weight
closure argument (F2), embedded regular factors (R1), the top bound and
finite-top actions (R2), rank-four exclusions (R3), and conductor-orbit
arguments (R4). The labels refer to this PDF; the separately prepared
editorial review register has its own numbering.

The manuscript makes downstream claims conditional where appropriate.
Compilation is not additional mathematical verification. In particular,
the full unitary Haagerup-CFT identification should not be read as an
unconditionally established theorem merely because the finite certificate
gates are complete.

## Build verification

Built using pdfTeX 1.40.29 (TeX Live 2026). The final build has no undefined
references, duplicate labels, overfull/underfull boxes, or missing-glyph
messages. Representative pages were rendered and visually inspected,
including the title, contents, theorem statement, analytic claim, and ledger.
All 40 distinct local artifact references in the TeX sources exist.

Two environment notices remain: the installed `array` package requests a
newer LaTeX kernel than the loaded format, and `epstopdf` reports that shell
escape is disabled. Compilation succeeds; this manuscript contains no EPS
graphics and does not require shell escape. The final build log is included
for transparency.

Compilation ran serially through `hi_cft_safe_run.py` with a 1536 MiB address
limit, two CPU/thread limit, the normal group-RSS/host-reserve checks, and a
120-second timeout. PDF rendering used a 1024 MiB address limit. No lattice
calculation was rerun, and no frozen research record was edited.
