# Physics data for the central-charge-eight Haagerup draft

Read [the manuscript](../hi_cft_c8_proof.pdf) for derivations, assumptions,
and physical interpretation. The 78-page manuscript places the physics
in Sections 2–7 (pages 7–28); the detailed
construction is retained in appendices. The earlier 55-page mathematical
version is preserved in `baseline/`. Old certificate archives have not been
silently updated to refer to the new manuscript.

Both current companions, the [audit guide](../hi_cft_c8_verification_guide.pdf)
and [Lean assessment](../hi_cft_c8_lean_assessment.pdf), now import the
manuscript's own labels for linked section, appendix, theorem, and page
references. Keep the PDFs together. Rebuild the manuscript before either
guide after source changes; `check_manuscript_refs.py` checks the emitted
links against the current manuscript destinations. The current physics
ZIP includes all three documents and their build dependencies.

## Two different full theories

All quoted central charges mean **c_L = c_R = 8**.

| Observable | Diagonal U theory | Selected full E8 extension |
|---|---:|---:|
| Currents in each chirality | 6 | 248 |
| First nonidentity Virasoro-primary dimension | 2/3 | 1 |
| First nonidentity scalar dimension | 2/3 | 2 |
| Relevant scalar components | 2,941 | 0 |
| Dimension-two scalar components | 19,558 | 61,504 |
| Invariant scalar gap | 2 | 2 |
| Invariant dimension-two scalar components | 36 under all center lines | 1,488 under the first chiral H3 factor; 36 under both factors |

The diagonal theory has the twelve Verlinde lines of the Haagerup **center**.
The selected E8 extension carries the specified six-object H3 action.
Its identity and charged tube-sector scalar gaps both give **(8,2)** in
Figures 2 and 3 of Albert–Honda–Kaidi–Zheng. Inspection of the original
plots places both points below the numerical bounds. The ordinary E8
scalar spectrum lies at the familiar (8,2) kink of Collier–Lin–Yin.
The unrestricted diagonal spectrum instead gives (8,2/3).

## Data index

| Files | Contents and scope |
|---|---|
| `data/characters.json`, `.tsv` | All twelve characters through grade 24, actual ground weights, state and Virasoro-primary multiplicities; independent E8 character control. |
| `data/fundamental_matrix.json` | Full rational exponent/characteristic matrices, recurrence, and computed fundamental-matrix coefficients. |
| `data/diagonal_sector_spectrum.tsv` | 3,410 sector/left-grade/right-grade rows, complete for total dimension ≤24. |
| `data/diagonal_spectrum.tsv`, `e8_spectrum.tsv`, `scalars.tsv` | Spin-resolved totals and scalar subsectors for the two full theories. The diagonal table has 2,582 dimension/spin rows. |
| `data/thermal.json`, `.tsv` | Partition function, free energy, mean energy, heat capacity and entropy at five aspect ratios, with outward-rounded intervals and modular tail certificates. |
| `full_weight_two/low_weight_basis.json` | All 113 actual weight-two chiral Virasoro primaries, sparse lattice vectors, lowering labels, charges and exact norms. |
| `full_weight_two/low_weight_products.jsonl` | 1,137 directly evaluated highest-first mode products. |
| `full_weight_two/low_weight_couplings.json`, `.tsv` | 3,512 charge-compatible seed projections, 1,639 nonzero. |
| `full_weight_two/complete_primary_couplings.tsv` | Full 113³ tensor: 18,365 nonzero entries; every omitted triple is exactly zero. Numerators, norm products and squared absolute coefficients are exact. |
| `full_weight_two/complete_primary_couplings.json` | Ward-completion derivation, 51,076 raising/lowering checks, 12,769 primary symmetry checks, 33 extra direct lattice probes, hashes and selected examples. |
| `full_weight_two/stress_couplings.tsv` | 32 exact stress Ward couplings for the eight original highest fields and four commuting stresses. |
| `correlators.json`, `.terms.tsv`, `.global_blocks.tsv`, `.samples.tsv` | Six orderings of the generator four-point function, Potts and PF13 spin-three four-point functions, current/stress examples, six global-block families through weight 32, nine selected fractional lattice-intertwiner blocks, and six lightest-block three-point magnitudes. |
| `defect_data.json`, `modular_S.tsv`, `defect_sectors.tsv` | Exact positive modular data, twists, dimensions, labels and Cardy overlaps. |
| `fusion.tsv`, `line_eigenvalues.tsv`, `twisted_gaps.tsv` | All 1,728 center fusion coefficients, 144 line eigenvalues and twelve twisted partition-function recipes/gaps. |
| `Cardy_annuli.tsv` | All 144 annuli between the diagonal theory's twelve Cardy boundaries. |
| `H3_forgetful.tsv`, `H3_fusion.tsv`, `E8_H3_tube_sectors.tsv`, `E8_H3_twisted.tsv` | Exact forgetful multiplicities, six-object fusion ring and selected E8 Haagerup sectors. |
| `E8_U_preserving_annuli.tsv`, `E8_U_preserving_boundaries.tsv` | All 36 annuli between the six U-preserving E8 boundaries; boundary overlaps are 1 or (3+√13)/2. |
| `crosslink_checks.json` | Independent arithmetic links the complete coupling tensor to the Gaussian four-point function (primary projection 11/3), stress Ward values, character count and defect-sector conventions. |
| `thermal_input_check.json` | Independent rational Machin-series certificate for the 100-digit enclosure of π supplied to the interval calculation. |
| `figures/` | Vector PDF/SVG figures, including attributed original-bootstrap panels with our model points. Plotting decimals are not exact algebraic inputs. |

## How to read a coupling

The raw basis is `v_m_p_q = F_L^p F_R^q v_m_0_0`, with no factorial
division. The basis file supplies every vector, so a basis label is an
actual field, not a sector name. Its unit version is `v_hat = v/sqrt(N)`
with positive square root and the transported lattice Hermitian norm N.

Each coupling row means

`C_ij^k = <v_k, (v_i)_1 v_j> / sqrt(N_i N_j N_k)`.

The first slot is antilinear. The numerator retains its complex phase.
Algebraic arrays are in the ordered basis **[1,s,t,st]**, where s=√13>0
and t=i√3; conjugation fixes s and reverses t. The four entries are exact
rational strings. The norm product uses the same encoding. Omitted
rows in the complete table mean zero; they do not mean uncomputed.

The eight original multiplets have dimensions (1,5), (1,9), (1,9),
(1,13), (2,2), (2,6), (2,8), (2,14). The additional multiplets are
(1,5), (3,3), and three stress-difference singlets. The manuscript gives
their explicit formulas. For example the first stress-difference
singlet has normalized self-coupling squared **23104/9243**.

The defining generator and its conjugate are basis indices 68 and 95,
up to a harmless unit phase. Summing their nine nonzero primary
projections gives **11/3**. Adding the total-stress contribution 1 gives
the independent Gaussian four-point global weight-two coefficient **14/3**.

## Other conventions that matter

- Dimension is h+hbar; spin is h−hbar. Scalar means spin zero, not merely
  integer spin. A degeneracy counts components, not extended sectors.
- The d3 ground weight is **15/13**. Its twist exponent 2/13 is not its
  lowest weight. Using the twist as the weight gives a wrong scalar gap.
- The EG-to-AHKZ map is d1,…,d6 → μ5,μ2,μ1,μ3,μ6,μ4. Both conventions
  appear in the literature; the exported map matches the actual twists.
- The defect field uses twelve rational coefficients of 1,ζ13,…,ζ13^11,
  with Φ13(ζ13)=0 and ζ13=exp(2πi/13). Decimal columns are for display.
- A noninvertible line fixes a state when its eigenvalue equals its
  vacuum value (the line's quantum dimension), not generally one.
- The H3 bootstrap multiplicity spaces omit the finite tube-irrep
  factors. In particular the physical untwisted π2 block has two copies.
- Dimension-two scalar counts do not assert that every such perturbation
  is exactly marginal. The manuscript identifies abelian current
  deformation subfamilies and states the remaining symmetry question.

## Reproduce without overwriting the release

Run from the repository or extracted bundle root. Use a fresh directory
for each command that writes data. All computations remain serial and
use the permanent desktop resource guard. These are bounded examples:

```sh
mkdir -p /tmp/c8-physics-replay
~/.local/bin/research-safe-run --limit-mib 512 -- timeout 300s python c8_physics_20260927/spectrum.py --order 24 --delta-cut 24 --outdir /tmp/c8-physics-replay/spectrum
~/.local/bin/research-safe-run --limit-mib 1024 -- timeout 920s python c8_physics_20260927/full_weight_two.py --output-dir /tmp/c8-physics-replay/primaries
~/.local/bin/research-safe-run --limit-mib 1024 -- timeout 300s python c8_physics_20260927/complete_weight_two.py --data-dir /tmp/c8-physics-replay/primaries
~/.local/bin/research-safe-run --limit-mib 1024 -- timeout 130s python c8_physics_20260927/correlators.py --output /tmp/c8-physics-replay/correlators.json
~/.local/bin/research-safe-run --limit-mib 1024 -- timeout 300s python c8_physics_20260927/defects.py --output-dir /tmp/c8-physics-replay/defects
~/.local/bin/research-safe-run --limit-mib 512 -- timeout 30s python c8_physics_20260927/check_physics_crosslinks.py
~/.local/bin/research-safe-run --limit-mib 512 -- timeout 30s python c8_physics_20260927/check_thermal_inputs.py
```

The arithmetic producers use the Python standard library. Plotting uses
Matplotlib. The bootstrap-overlay source states its separate PDF/TeX
requirements and the primary source URL; the full third-party paper is
excluded from the bundle. The distributed panels retain attribution.
Source hashes and output hashes authenticate files, while the algebraic
checks test their stated mathematical content. These are different tasks.

## What is still missing

These data are conditional on the construction and character identification
documented in the manuscript. The weight-two tensor is a **chiral
vacuum-module** tensor. It is not the nonvacuum bulk OPE tensor of the
diagonal theory. In particular, normalized bulk three-point coefficients
and sewn four-point functions for the nine Δ=2/3 scalar components remain
uncomputed. The selected fractional lattice blocks are partial chiral
input to that problem. General junction correlators, full nonvacuum
crossing data, RG endpoints and a transported Haagerup symmetry along
exactly marginal deformations also remain open calculations.

See the updated 17-page [Lean assessment](../hi_cft_c8_lean_assessment.pdf) for a
section-by-section account of missing definitions, dependency difficulty
and realistic formalization stages. Two new Lean lemmas prove the algebraic
thermal-tail rearrangement and positive-cutoff division, with analytic
premises explicit. Exact Python checks are not Lean proofs.

The current release audit reports a clean TeX build, authenticated producer
inputs/outputs, and a fresh-tree replay of all six physics producers: 31
payload files agree byte for byte and four structured records agree after
excluding run metadata. See `release_audit.json`, `release_replay.json`,
and `resource_review.md`. The full historical construction and bootstrap
SDP are outside this replay's scope.
