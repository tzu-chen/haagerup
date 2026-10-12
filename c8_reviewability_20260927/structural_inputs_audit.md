# Structural-input reviewability supplement

The structure agent wrote `structural_inputs.tex`, four readable transcription
tables, two bounded exporters, and two independent standard-library verifiers.
The root agent runs all arithmetic jobs under the permanent resource policy.
The structure agent performed only reading, algebra, editing and direct JSON-to-TSV
transcription; it did not launch research computations or builds.

## What is exposed

- The complete compact Potts stress and weight-three field, with worked central
  charge and PCT checks. The root's independent readable-input checker also
  compared both complete formulas with their saved 27- and 92-term fields.
- All three PF13 singular first rows, including the seven-term weight-six
  polynomial and the weight-seven simple pole obtained algebraically. Sources:
  `hi_cft_20260923_proof_pf13_upper_poles.py`, `..._nonlinear.py`,
  `..._truncation.json`, and `..._simple_pole_algebra.json`. Coefficients retain
  canonical mode, derivative, and normal-order conventions.
- Six complete 21-term joint spectral witnesses and their residual equations.
  `core_spectral_witnesses.tsv` is a direct transcription of the old exact
  record, not a new mode calculation. The compact PF13 lowest-weight arithmetic
  singles out the two inverse simple currents.
- The elementary unique-Cartan-eigenline plus cyclicity irreducibility proof,
  with explicit initial current actions for both the 80- and 81-dimensional
  cases. All four 81-top seed and pivot recipes are transcribed into readable TSV.

The positive-stress overlap table is in the root's guide section
`hr:positive-stress-check`, to avoid duplicate tables. Its independent exact
check uses saved actual fields and a Fock pairing formula, not the original
mode engine. Haar averaging still uses the certified identification of the
four-dimensional current-invariant subspace in S2.

## New exact membership witnesses

`export_membership_witnesses.py` repeats the original finite span construction
while tracking exact expressions in raw generated words. The root's guarded
run produced `membership_witnesses.json` and its coefficient TSV:

| Target | Target terms | Nonzero source coefficients | Rank at discovery |
|---|---:|---:|---:|
| Potts w_P | 92 | 33 | 41 |
| PF13 w | 342 | 42 | 58 |

The export contains all 120 S2 parent vectors, all 58 retained grade-three
source vectors and their recipes. It used 154 zero-weight products, retained
43,462 sparse terms including elimination data, and finished in 157.54 seconds
at 84,292 KiB peak RSS. Frozen research records were not overwritten.

`check_membership_coordinates.py` imports no research engine and independently
verified both coordinate sums plus grade/Cartan labels on 21,772 decoded rows.
Its passing result is `membership_coordinate_check.json`, peak 52,788 KiB.
Duplicate basis rows, duplicate expression entries and duplicate JSON keys
fail closed. This verifies the explicit linear identities, not the assertion
that each supplied source vector is the mode product named by its recipe.

## New eighty-current witness

`export_current80_witness.py` exports an 86-state ambient basis, its positive
Hermitian Gram matrix, six current vectors, an 80-row complement basis, all
30 original/adjoint matrices, and 80 cyclic rows with complete recipes. The
root's guarded run passed in 1.25 seconds at 36,996 KiB peak RSS. The actual
matrix count is 3,486 nonzero entries, and the seed has basis index 76 and
Cartan weight (0,10). Its pure momentum is (1,1,1,1,1,0,0,0).

`check_current80_matrices.py` is the separate standard-library checker. It
reconstructs and proves positivity of the Gram matrix, verifies explicit
current formulas, orthogonality and independence of the complement, all
adjoint/invariance assertions, the exact Cartan matrices and unique seed,
and all cyclic recipes and pivots. The root's run passed, as recorded in
`current80_matrix_checks.json`, at 25,336 KiB process RSS. Its exact positive
LDL diagonal is [2,3/2,4/3,5/4,6/5,1/2,2,3/2]. Neither its matrix checks nor the
membership coordinate sums formalize the ambient VOA or independently
reconstruct every named mode product.

## Exact provenance of the four TSV views

1. `structural_fields.tsv`: concatenate the following arrays, in this order,
   with field labels `p`, `w_P`, `z`, `w` respectively:
   `hi_cft_20260923_proof_potts_exact.json` → `potts_stress`,
   same file → `weight_three_primary`,
   `hi_cft_20260923_proof_pf13_exact.json` → `stress`,
   same file → `primary`.
   Each array element supplies `momentum`, `oscillators`, and the four strings
   in `coefficient`. Integer lists are comma-joined; an empty list gives an
   empty TSV cell. There are 27+92+64+342 = 525 data rows.
2. `core_spectral_witnesses.tsv`:
   `hi_cft_20260923_next_structure_core_extension.json` → each element `b`
   of `blocks`, then each `e` of `b.joint_eigenspaces` for which
   `e.PF13_weight == "12/13"`, then each `v` of `e.vectors`, then each row
   of `v.vector`. The leading TSV column is `b.Cartan_weight`; the remaining
   columns are that row's `momentum`, `oscillators`, and `coefficient` strings.
   Source order is preserved. Six vectors × 21 terms give 126 data rows.
3. `top81_seeds_and_first_steps.tsv`:
   `hi_cft_20260923_next_81top_all.json` → each `sec` of `sectors`, then
   rows `i=0,1` of `sec.rows`. Each stored `[j,c]` gives one TSV row with
   `sec.glue_sign`, `sec.sector_sign`, `i`, `j`, comma-joined `sec.roots[j]`,
   the four coefficient strings `c`, and `json.dumps(sec.recipes[i],sort_keys=True)`.
4. `top81_pivots.tsv`: same four `sec` records, all `i=0,...,80`.
   The pivot column is `sec.rows[i][0][0]`, the first (smallest) basis index
   in that stored sparse row. The remaining columns are
   `sec.recipes[i].weight` (comma-joined), `input` (JSON with sorted keys),
   `reductions` (JSON), and `scale` (JSON). No pivot computation, elimination,
   rescaling or arithmetic was performed during transcription.

All TSV files use the Python CSV writer with a tab delimiter, so JSON-bearing
cells may have doubled quote characters in the physical text. Reading them
with a CSV/TSV parser recovers the exact JSON strings described above.

## Remaining substantial boundary

The saved nonlinear parafermion product a_0 b reports 25,045 nonzero basis
terms and the weight-six relation involves 28,342 terms. Short OPE formulas
make these inputs mathematically explicit, but the corresponding actual
vector equalities still require exact mode-product verification. The mode
provenance of the newly exported small witnesses is likewise distinct from
their independently verified finite linear algebra. No passage from matching
central charge and one coupling to a parafermion isomorphism is asserted;
the manuscript uses the full rows and its separate reconstruction theorem.
