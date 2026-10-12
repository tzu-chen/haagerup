Haagerup Symmetry and Conformal Field Theory
From Fusion Rules to Lattice Constructions and Continuum Tests

A textbook for beginning mathematics and physics PhD students.
Prepared during the requested six-hour writing period on October 5, 2026.

READING

Open haagerup_cft_textbook.pdf. The opening reading guide explains the
prerequisites, alternative reading routes, and the different construction
problems. A clickable list after the contents collects all worked examples.
The table of contents, cross-references, exercise solution links,
and index are clickable. Each exercise has a solution in Appendix B.

The five parts cover the categorical and CFT language; the explicit
central-charge-eight lattice construction; local fields, full theories,
defects and sewing; reduced theories and the physical Haagerup chain;
and arithmetic constructions including noncyclic and extended Haagerup.
The source guide is deliberately short. The exposition and worked examples
are meant to be read without following repository scripts.

SCIENTIFIC SCOPE

The central-charge-eight research construction is developed from explicitly
stated finite lattice inputs and structural/analytic theorems. This book does
not independently replay every large certificate. The physical Haagerup
chain's continuum limit remains unidentified in the completed record used
here. A chiral stress, a full sewn CFT, a fusion category, and a numerical
candidate are kept distinct throughout. Appendix C explains verification
scopes, including the separate all-odd coefficient formalization.

FILES

haagerup_cft_textbook.tex  Main document, with chapter and solution order.
preamble.tex             Notation, theorem environments, and layout.
chapters/                Main text and appendices.
solutions/               Solutions in book order, grouped by chapter.
figures/                 Native TikZ diagrams and the included vector Ising plot.
editorial/               Review notes, small-check records, and source drafts.
build.py                 Bounded document-only PDF builder for this Linux host.
audit_document.py        Source, reference, exercise, and Python syntax audit.
audit_pdf.py             PDF link destinations, solution anchors, and bookmarks.
check_examples.py        Small exact arithmetic checks, requiring the guard.
check_order_three.py     Exact order-three coefficient identities, same guard.
check_core_tops.py       Fourteen core tops and their rational trace certificate.
plot_ising_calibration.py Reproduces the included Ising plot, requiring the guard.
package.py               Source ZIP and SHA256 manifest generator.
record_sources.py        Read-only identities of selected research sources.
manifest.json            Hashes and counts for the packaged edition.

The source ZIP is self-contained for typesetting. It does not include the
large scientific repository, numerical checkpoints, or an installation of
the shared research launcher. The PDF is delivered separately and its hash
is recorded in manifest.json. Editorial records describe what was checked;
they are not a claim that all mathematical inputs were independently proved.
The dated editorial/scientific_source_snapshot.json identifies selected
research documents and completed records at the final source cutoff.
Current machine-policy, forwarding-shim, and central-guard hashes have their
own section; they do not replace hashes in historical execution records.
The recorder does not import, execute, or copy those research sources, and
refuses to overwrite a prior snapshot.

TYPESETTING

From this directory, on the supplied Linux research host:

    python3 audit_document.py
    python3 build.py --passes 3
    python3 audit_pdf.py
    python3 package.py

The builder uses pdfLaTeX and makeindex, disables shell escape, checks host
and cgroup headroom, and bounds each foreground typesetting process. It
records the TeX and included figure hashes and final PDF hash. It refuses a
final build if an input changed during compilation. Three passes settle contents,
cross-references, and index entries. Read build/haagerup_cft_textbook.log
for TeX diagnostics and build/build_record.json for the resource record.

The sources use standard TeX Live packages: Latin Modern, AMS mathematics,
mathtools, microtype, geometry, TikZ, booktabs, longtable, xurl, fancyhdr,
makeidx, hyperref, and bookmark. The PDF navigation audit additionally uses
qpdf. They can also be typeset in a conventional TeX
installation with pdfLaTeX and makeindex; the Linux-specific builder is
only an editorial convenience, not part of the mathematics.

SMALL MATHEMATICAL CHECKS

check_examples.py checks a finite set of displayed examples: the exact
Haagerup modular S-square and Verlinde arithmetic, two twisted character
vectors, descendant/null-state arithmetic, small Gram matrices, and selected
correlator coefficients. It uses the Python standard library and exact
rational/cyclotomic arithmetic. It does not verify the full CFT construction.

On this shared desktop, numerical work must follow the canonical policy at
/home/tzuchen/.codex/AGENTS.md. The recorded run used the central launcher:

    ~/.local/bin/research-safe-run --wait --limit-mib 256 --memory-mib 256 \
        --threads 1 -- timeout 90s python3 check_examples.py

Only that central launcher may admit research computations here. The
checker refuses to run without its guard environment. It is optional for
reading and typesetting the book. The existing result is recorded in
editorial/example_check_results.json with the checker and guard hashes.
The original checker and its first result are preserved together under
editorial/checker_history/. The current checker additionally refuses Python
optimization, which could otherwise disable its assertions; its recorded
result was refreshed after that change.

The order-three example has a complete hand proof of its cubic identities.
A second small checker independently verifies all indexed equations using
four-integer normal forms, without evaluating the special function:

    ~/.local/bin/research-safe-run --wait --limit-mib 128 --memory-mib 128 \
        --threads 1 -- timeout 30s python3 check_order_three.py

Its output is editorial/order_three_check_results.json. This verifies the
specified finite coefficient matrix, not categorical reconstruction or a CFT.

A third standard-library checker reconstructs the fourteen core-module
lowest spaces from the printed minimization formulas, retaining tied charges
and their multiplicities. It checks all trace columns, the finite cutoff,
and the coefficientwise nonnegative certificate for the universal 17/10 bound:

    ~/.local/bin/research-safe-run --wait --limit-mib 128 --memory-mib 128 \
        --threads 1 -- timeout 30s python3 check_core_tops.py

Its successful result is editorial/core_top_check_results.json. This checks
exact arithmetic conditional on the stated core realization and compatible-top
lemma; it does not verify the lattice embedding or reconstruct the VOA.

The included Ising figure is ready for typesetting. Its optional regeneration
uses Matplotlib and only the exact scalar formulas derived in the chapter;
it does not compute a spectrum. Its reviewed memory estimate includes imports,
font caches and rendering. The recorded command was:

    ~/.local/bin/research-safe-run --wait --limit-mib 1024 --memory-mib 512 \
        --threads 1 -- timeout 90s python3 plot_ising_calibration.py

Formulas, plotted values, script and asset hashes, and execution measurements
are in editorial/ising_calibration_plot_provenance.json and the accompanying
plot review. Matplotlib is unnecessary when using the supplied figure.

REUSE

Edit a chapter or its solution file, run the text audit, and rebuild the
PDF before packaging. Old aggregate solution drafts are preserved under
editorial/source_drafts/; the active files are in solutions/. Keep scientific
source changes and new research certificates separate from editorial fixes.
