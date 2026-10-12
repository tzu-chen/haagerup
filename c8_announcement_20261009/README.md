# Short c = 8 identification announcement

`haagerup_c8_announcement.tex` is a standalone proof-sketch announcement
prepared on 9 October 2026. The compiled PDF is **11 pages**, including references.
`references.tex` is its only local input.
The author name follows the existing letter; no affiliation, public
repository URL, or release date for the companion works has been invented.

The note retains the explicit lattice generators and gauge, the recursive
closure criterion, positive-stress rationality, the universal top bound,
branching and fusion-ring exclusions, the analytic unitarity step, and the
twelve-sector identification. It distinguishes the diagonal theory from
the selected holomorphic extension and the latter from the original
lattice embedding. It states that the mathematical exposition, numerical
and exact-arithmetic certificate repository, and physics exposition are
in preparation.

## Source and review scope

The mathematical sources are the current `../hi_cft_c8_proof.tex`,
`../hi_cft_c8_manuscript_structure.tex`, and
`../hi_cft_c8_manuscript_analytic.tex`, checked against the corresponding
chapters of `../haagerup_cft_textbook/`. The earlier five-page physics
letter informed the scope and notation. Original manuscripts and
scientific certificates were not modified.

The stated realization inherits the finite exact construction inputs of
those sources. This writing task did not rerun the lattice engine,
numerical certificates, or Lean development. Independent reading reviews
checked the compressed argument and restored the pointed rank-six
exclusion, balanced near-group exclusion, second-moment hypothesis, and
concrete annulus-net comparison. These reviews are not an independent
verification of the complete construction. Selected primary references
were checked against their original papers.

## Build

From this directory, run twice:

```sh
~/.local/bin/research-safe-run --wait --limit-mib 1536 --memory-mib 1024 -- timeout 90s pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error haagerup_c8_announcement.tex
```

Only standard LaTeX packages are required; there are no external figures,
BibTeX step, or shell-escape dependencies. The source archive is intended
for typesetting, not for reproducing the scientific certificates. On this
host the canonical policy is `/home/tzuchen/.codex/AGENTS.md` and builds
use the installed central guard; no local launcher is supplied.

The actual typesetting path loads this small source and ordinary TeX
packages, without invoking scientific scripts or large data stores.
Estimated peak resident use was below 128 MiB for pdfLaTeX and 256 MiB
for the additional Tectonic check, including fonts and temporary output.
The earlier resource-limited checks used a 1536 MiB address cap, a 1024 MiB
kernel cgroup memory limit, no swap, one CPU, a 120-second timeout,
and a 32 GiB host-availability watchdog. Observed sampled peaks were
33 MiB for pdfLaTeX and 187 MiB for Tectonic; host MemAvailable stayed
above 48.9 GiB. Build measurements are in `build_record.json` and
`tectonic_build_record.json`; those records describe the earlier revision.

The initial build was blocked by another project's exclusive research
lock. The user subsequently explicitly authorized temporarily bypassing
that lock to fix and check the document. That temporary exception was
used only for typesetting and PDF inspection, including the wording-fix
and final-cleanup rebuilds, with bounded CPU and memory use;
no numerical research job or certificate replay was run. No locks were
modified or acquired outside the central guard, and no permanent policy
or launcher changes were made. The normal build command above continues
to use the central guard.

The current guard SHA-256 is
`09b9986966402a73bba8e078884a50b5762c4980485ea295e8cca2e02fc8ae63`.
No historical launcher or certificate provenance was rewritten.

## Validation status

Fixed the Pond-reported `Command \Vec already defined` error. `amsmath`
already defines `\Vec` as an accent, so the conflicting declaration was
removed and its one category-notation use was replaced by
`\mathrm{Vec}_{\ZZ/3}`. The mathematical content is unchanged.

The subsequent wording audit was applied: grading restrictions are explicit,
the core-extension argument is restricted to supported invertible constituents
of the zero-complementary-energy subalgebra, the representation inequalities
refer to the full U-top, and the extension categories explicitly mean all
right modules over the algebra in Rep(U). The Sugawara statement, abstract
current-algebra terminology, and introductory generalization were corrected.
The `monolith-authorship` package declaration was removed; no matching style
file was present in this project. The PDF metadata title now matches the title.

Two pdfLaTeX passes succeeded for the wording-fix revision, producing eleven pages.
That final log has no undefined references/citations, missing glyphs, or
overfull boxes. Two harmless underfull-box notices remain in the bibliography;
pdfLaTeX also reports that shell escape is disabled, as intended. That revision's
source hashes and measurements are in `wording_build_record.json`, with
logs `wording_build_pass_1.log` and `wording_build_pass_2.log`. This rebuild
used a 1536 MiB address cap, a 1024 MiB kernel cgroup memory limit, no swap,
one CPU, a 120-second timeout per pass, and a 32 GiB host-availability
watchdog. Sampled process-group RSS stayed below 33 MiB, and host
MemAvailable stayed above 49.4 GiB. Rendered pages 9, 10, and 11 were
inspected, including the sector table, final discussion, and references.

The earlier revision also passed Tectonic 0.15.0 (cached resources only,
untrusted mode) and broader page inspection. That historical check does not
describe the current revised source; its record is preserved separately.

Static checks found 39 unique labels, 30 cited bibliography entries,
no unresolved references or citations, no unused bibliography entries,
and no unexpected control characters.

## Final submission cleanup

The final check includes the author's latest prose edits. Two commented-out
lines were removed and a missing sentence-ending period was restored in the
introduction. Both TeX sources and the extracted PDF text were checked for
prompts, TODOs, placeholders, editorial notes, hidden comments, local paths,
and merge artifacts. No unintended residue remains. The acknowledgements,
AI-use disclosure, and companion-work announcement are intentional.

Two fresh pdfLaTeX passes succeeded, producing eleven pages with no unresolved
references or citations, missing glyphs, or overfull boxes. The same two
harmless bibliography underfull-box notices remain. That revision's source hashes,
PDF hash, build limits, and measurements are in `final_build_record.json`;
the logs are `final_build_pass_1.log` and `final_build_pass_2.log`. The final
build used the same limits as the wording-fix rebuild. Sampled process-group
RSS remained below 23 MiB, and host MemAvailable stayed above 49.5 GiB.

The refreshed submission ZIP contains only `haagerup_c8_announcement.tex`
and `references.tex`, verified byte-for-byte against the current files.
This local README and all build logs and records are excluded from the ZIP.
All document build jobs completed; none remains waiting or running.

## Closing paragraph revision

After the author moved the detailed-proof statement into the introduction,
a two-sentence closing paragraph was added before the acknowledgements.
It connects the construction to the realized character vector and Haagerup
defects, then points to studying their action on operators and correlation
functions. The moved introductory sentence now uses the present tense.
Two pdfLaTeX passes succeeded; the PDF remains eleven pages, with no
unresolved references or citations, missing glyphs, or overfull boxes.
That revision's hashes and build measurements are in `closing_build_record.json`;
the earlier build records remain unchanged. The two-file source ZIP was
refreshed and verified against the current sources.

The Section 2 gauge constants were subsequently renamed from tilde-c to
the indexed constants lambda_0 through lambda_7, including both the gauge
and PCT products. Two pdfLaTeX passes succeeded, still producing eleven
pages with no unresolved references or citations, missing glyphs, or
overfull boxes. That revision's hashes and build measurements are in
`notation_build_record.json`; the two-file source ZIP matches this revision.

The two current formulas now use matching fixed-size RHS parentheses and
side subscripts on the sums to give the rows similar heights. The rebuilt
page 2 was visually checked. Two pdfLaTeX passes succeeded, retaining eleven
pages without unresolved references or citations, missing glyphs, or
overfull boxes. Current hashes and measurements are in
`current_layout_build_record.json`; the two-file source ZIP was refreshed.
