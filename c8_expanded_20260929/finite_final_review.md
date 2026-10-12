# Independent final finite-document review

Reviewed 2026-09-29. Scope: `finite_details.tex`, `coordinate_details.tex`, `top_details.tex`, their typesetting producers, and the corresponding saved exact/numerical inputs. This was a static mathematical/transcription review. No vertex-mode calculation, matrix product, eigensolver, rank recomputation, external theorem verification, research-script import, PDF rendering, or numerical job was run. Small standard-library document parsing and rational coefficient comparisons were used.

## Finding corrected during review

The initial coordinate atlas incorrectly labelled the 342-term TSV field `w` as the normalized parafermion generator `a_PF13`. The actual TSV export maps this field to `pf['primary']`, which is the unnormalized `w`; the structural companion defines `a = sigma*w`, with `sigma^2 = -(7+3st)/9223500`.

Reported this to root immediately. Root corrected both `assemble_draft.py` and the regenerated `coordinate_details.tex`. I checked the correction: the atlas now labels `w_PF13`, explicitly gives the normalization, distinguishes `w_5 w = (-86086+36894st)1` from `a_5 a = 8/15`, and states that the printed coefficients do not include sigma. The source coefficients were not altered. This also restores agreement with the complete membership tables, whose parafermion target is the unnormalized primary.

## Independent transcription comparisons that passed

The comparisons parse the *printed TeX expressions* into rational coordinates in `(1,s,t,st)` rather than merely trusting the typesetting helper. They compare momenta/oscillators and coefficients, not just row counts.

- All **303** finite highest-field/neutral-stress coordinate terms match the current repaired `hi_cft_20260923_c8_exact_fields.json`.
- All **771** distinct root coordinate-atlas terms match `grade2_fields.tsv` plus the nonduplicated part of `structural_fields.tsv`. The repeated `p,z` rows agree exactly across the two exports.
- All **126** terms of the six joint spectral witnesses match `core_spectral_witnesses.tsv`.
- All **75** complete structural membership coefficients and their actual source-word labels match the coefficient TSV (33 Potts, 42 parafermion).
- All **404** printed cyclic recipes (80 current-complement recipes and four sets of 81 mixed-top recipes) match the saved operator indices, parent indices, normalization scales, ordered reductions, and reduction coefficients. Seed rows have empty reductions and scale one as assumed by the compact rendering.
- All **80** complement-row coordinate expansions match the explicit current80 witness.
- All **324** mixed-sector root tuples and metric entries match their sector-specific records. The displayed integer tuples are exactly three times the stored rational momenta; they are not mistakenly treated as the momenta themselves.
- All **130** Gate 4 added-request pairs have the correct left index, exact right-row name, input/output Cartan weights, and subsequent Direct/Singlet coverage.
- The complete **120** structural-membership basis definitions have the stated relationship to the other indices: first 23 vectors equal the corresponding *raw* short-generation vectors, index 23 is `e`, and the remaining 96 have the correct charged-field index/lowering-power/range conventions.

The TeX files' braces and relevant environment pairs balance. The root build, not this audit, supplies PDF compilation/page-layout verification.

## Version and interpretation checks

- The top-atlas transcription hashes and byte counts match the current three input files. The original mixed81 record's exact-field-source hash matches the current repaired exact field JSON, excluding an unnoticed old-versus-repaired field mixup.
- The numerical discovery tables are explicitly historical floating diagnostics. Modular rank and exact field-rank conclusions are distinguished. The interpretation of the saved low-grade `exact_OPE_closure` flag is restricted to its actual tested modes/pairs.
- Lower-closure target rows named `current_basis_*` are correctly distinguished from canonical currents. Their printed conversion is `(-H_L,E_L,-F_L,-(H_R+5H_L)/2,E_R,-F_R/5)`.
- Top-atlas operator names use canonical currents `K0,...,K5 = H_L,E_L,F_L,H_R,E_R,F_R`, followed by `field0,...,field7 = a0,...,a7` and `field8 = e`. The 30 interleaved operator/adjoint indices agree across records; the text does not assert equal matrices between different sectors. Current modes are zero, weight-two modes are one. Current80's saved adjoint components have one term each, consistent with the wording.
- The mixed81 source contains matrix hashes/nonzero counts, not the full action matrices. The atlas correctly calls these matrix metadata and retains the actual lattice-mode identification as a separate obligation.
- The twenty-one projected normal columns are not presented as an exhaustive basis of N4. The 6007 selected normal words plus a triplet are not used to claim an independently exact dimension 6010. The distinction between U4=W4 and the later character coefficient 6010 remains explicit.
- Conditional old Jacobi/status records, request-only lists, completed direct identities, and final authenticated gates are kept distinct.

## Review conclusion and limits

No remaining substantive transcription or version-mixing error was found in the reviewed files after the parafermion normalization correction. These checks establish consistency between the new presentation and the saved records; they do not independently establish that saved vectors/matrices equal their named VOA mode products, prove the finite strong-generation theorem, or verify the full construction and analytic transport arguments.

## Reviewed source snapshots

- `finite_details.tex`: 98542 bytes; SHA-256 `96f6da93b9e0d7397bc6a65558748d1028c1e025711cc3fdcd9ad9370c8765ca`.
- `coordinate_details.tex`: 53200 bytes; SHA-256 `4a35e0afc0df255a57138115f85f7d51bfeb04278f0b17eb559c820826b78f65`.
- `top_details.tex`: 237684 bytes; SHA-256 `5f8104cfd709f2c8f2dd31c3d4161f6591555fd90ca5b5eddd4c041809905312`.
- `assemble_draft.py`: 19230 bytes; SHA-256 `d182a65979b67627c750529ccd8587b6c578062b9de4aeded74cde3390e08336`.
- `build_top_atlas.py`: 8663 bytes; SHA-256 `b36187e707acb917645f23cb7857e4f06327afbd1884a04d525664b591c5e238`.
