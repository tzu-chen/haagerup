# Expanded c=8 verification draft — 29 September 2026

Read **[haagerup_c8_expanded.pdf](haagerup_c8_expanded.pdf)**: **341 pages**.
This is a separate expansion of the current 78-page `hi_cft_c8_proof.pdf`,
with the verification and Lean companions incorporated. Original manuscript,
scripts, and result files were not edited.

The purpose is to put the recorded equations, coefficients, coordinates,
normalizations, and verification boundaries on the page. This edition does
not claim a new research computation or an independent proof of the CFT.

## Reading map

The PDF has a linked contents list and bookmarks. Its original appendices
retain letters; supplementary appendices use S numbers. References in the
incorporated companions now lead to this same PDF.

| Material | Start page |
|---|---:|
| Orientation and quick verification map | 2 |
| Preserved main manuscript | 11 |
| Original construction and mathematical appendices | 35 |
| Integrated small-input verification guide | 83 |
| Expanded finite construction, field tables and membership recipes | 102 |
| Additional commutants, residual tensors, top data and analytic records | 140 |
| Additional interactions, fusion, defects and boundaries | 172 |
| Complete characters and spectra | 219 |
| Thermal intervals and tail certificates | 261 |
| Complete small-field coordinate atlas | 263 |
| Complete finite top witness atlas | 278 |
| Integrated formalization assessment | 320 |
| Source concordance and version decisions | 335 |
| References | 338 |

## What was incorporated

- All 303 terms of the charged highest fields and retained neutral stress;
  the 120 accepted generation recipes; all 75 Potts/parafermion membership
  coefficients; grade-three charge data; and detailed Gate 4/5 records.
- Residual Griess products, conformal axes, core-top characters and energy
  traces, ambient coset and charge-six lattice arguments, and the analytic
  dependency and replay maps. Supplementary archived arguments retain their
  own hypotheses and review scope.
- All 113 primary-component indices and norms, 318 phase-sensitive reduced
  coupling representatives with an explicit reconstruction formula, and all
  169 ordered multiplet support rows. Together these describe the completed
  18,365-entry nonzero coupling tensor, including its zero maps.
- All 198 saved global-block rows, surviving Gaussian terms, selected light
  lattice blocks, rational-point correlator values, center fusion products,
  twisted-sector matrices, Cardy annuli and extension boundary data.
- All 25 grades of twelve U characters and the E8 character, full scalar
  spectra and all 2,907 signed-spin rows through dimension 24 (opposite signs
  folded without losing their individual multiplicities), and 60 outward-
  rounded thermal observable intervals with tail bounds.
- All 771 distinct small stress/spin-three coordinate terms, all 126 joint
  spectral-vector terms, the eighty-current ambient/complement bases, and
  all 404 cyclic recipes for the eighty-current and four mixed 81-dimensional
  tops, including their complete mixed-sector bases and metrics.

Large outputs are represented compactly only where the text gives the
recovery rule. The full historical SQLite stores and high-weight vector
databases are not reproduced wholesale.

The review also made two important conventions explicit: the left-lowering
norm factor `8640^(2p)`, and the conversions from the raw Potts/PF13 coordinate
vectors to the canonical spin-three generators. The older 96-field coupling
export is not substituted for the completed 113-field release.

## Files and validation

- `haagerup_c8_expanded.tex`: main source, with the original manuscript body
  incorporated and figures redirected to local `assets/`.
- `finite_details.tex`, `structure_details.tex`, `physics_details.tex`:
  authored expansions; `physics_tables/` contains their generated tables.
- `spectral_details.tex`, `coordinate_details.tex`, `top_details.tex`:
  complete transcribed data appendices.
- `verification_guide.tex`, `lean_scope.tex`: incorporated companions.
- `base/`: unchanged copies of the original TeX inputs.
- `document_audit.json`: source/dependency/reference/build checks.
- `finite_final_review.md`, `physics_final_review.md`: independent static
  and transcription reviews, including the normalization correction.
- `build_record.json`: limits and sampled resource use for the final build.

The final document has 310 labels and 50 bibliography entries. Checks found
no unresolved references/citations, duplicate labels, missing glyphs, or
overfull boxes. The original 17 copied TeX inputs and 42 recorded input
hashes match the repository. The remaining underfull-box notices concern
loose line spacing in narrow cells; TeX also reports the pre-existing local
array/kernel release mismatch and disabled shell escape. Representative
pages were rendered for visual review.

These checks validate the document and its transcriptions. They do not
replay the lattice engine, prove finite ranks again, or verify external
VOA/category/analytic theorems. The optional transvectant comparison script
is supplied but was **not run**; no passing result for it is claimed.

## Build

From this directory:

```sh
python build_pdf.py --passes 3
```

This fixed-purpose Linux typesetting runner accepts no research command.
It disables shell escape and bounds each TeX pass to 1.5 GiB address space,
1 GiB group RSS, two CPUs/threads, 120 seconds, and at least 32 GiB host
MemAvailable. The numerical shared lock is left to numerical workloads.
Final passes used about 38 MiB sampled peak RSS and about two seconds each.
The expired September 15 exception is not used.

The source ZIP is self-contained for typesetting; it needs the standard
LaTeX packages used by the original draft. It does not need the research
JSON/SQLite stores merely to compile. Regenerating table fragments with
`assemble_draft.py`, `build_top_atlas.py`, or the physics table producer
requires the original repository data. Running `audit_document.py` also
requires the original repository to check archived input hashes.
