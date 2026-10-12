# Finite-lattice expansion source notes

`finite_details.tex` was assembled on 2026-09-29 as a documentation expansion of the current c=8 draft. No numerical research job, imported research script, lattice-mode replay, eigensolver, or database mutation was run for this task. JSON/TSV reads, exact rational formatting, support-count transcriptions, and ordinary text comparisons were used. Root owns the integrated LaTeX build.

All section/equation labels begin `expfinite:`. The only external cross-reference is `expdata:coordinates`, supplied by the root's added data atlas. The file uses the existing `artifact` macro, standard math environments, booktabs, and longtable.

## Main contents

- Complete 303-term coordinates for all eight charged highest fields and the retained neutral stress: `hi_cft_20260923_c8_exact_fields.json`. Coefficients are read from the nested exact rational arrays, flattened in order `1,s,t,st`, and combined over a common denominator. Historical decimal recognition fields are not used.
- The entire 120-row accepted short-generation graph, with raw recipes, Cartan weights, and raw/normalized support sizes; every normalized target-coordinate expansion for all ten targets: `c8_reviewability_20260927/minimal_generation_witness.json`.
- Exact grade-three build history and complete Cartan census: `hi_cft_20260923_c8_grade3_exact_v2.json`. Quotient multiplicities and the 15-type current decomposition come from `hi_cft_20260923_c8two_structure_saturation.json`; the normal multiplicities are differences. Nonnegative representatives have explicitly stated sign-orbit multiplicities.
- All nine saturation deficits, all 130 additional Gate 4 requests, all twelve raising-premise requests, every one of the 21 normal-column recipes, and all twelve projected target support sizes.
- Actual triplet recipe, projector denominators and support sizes: `hi_cft_20260923_next_structure_p4_controls.json`.
- Breakdown of all 3970 lower-control tasks and conversion of its normalized current-coordinate rows to the canonical currents: task producer and `hi_cft_20260923_next_structure_lower_closure.json`.
- All 28 accepted charged-span seeds: `hi_cft_20260923_c8two_structure_charged_span.json`, with explanation of how the independent verifier reconstructs them from exact lower relations.
- All 75 nonzero structural membership coefficients (33 Potts, 42 parafermion), including every source word: `c8_reviewability_20260927/membership_witnesses.coefficients.tsv` and the JSON witness.
- Historical numerical ambient highest multiplicities, grade-three action residuals, 16 Griess-axis charges, and all 49 eigenvalue/positive-mode norm pairs. These are explicitly labelled numerical diagnostics, not exact inputs.

## Important distinctions preserved

1. `hi_cft_20260923_c8_exact_fields.json` retains its original reconstruction-conjecture scope text. The later exact certificates check the repaired entries. Two stress oscillator coefficients were repaired; the expansion prints the before/after expressions and uses the corrected current file.
2. The minimal-generation `v_i` are raw vectors, `r_i` their pivot-normalized remainders. The membership export has a different `b_i` basis. A direct comparison of saved coordinate lists confirmed `b_i=v_i` for `0<=i<=22`; `b_23=e`, whereas minimal `v_23=r_23=u`. The remaining 96 membership vectors are explicitly indexed unnormalized lowering descendants. Neither index set is silently equated to the checkpoint `r2_...` basis.
3. `current_basis_0,...,current_basis_5` in the lower-control target-coordinate data are `-H_L,E_L,-F_L,-(H_R+5H_L)/2,E_R,-F_R/5`. The left current in a task remains the canonical indexed current.
4. The 130 requested Gate 4 pairs consist of 118 later direct relations and twelve later singlet recoveries. The twelve extra raising-premise requests form a different list and have output weight `(0,2)`.
5. Positive full rank at the good prime is only used against the independently exact dimension 322. No characteristic-zero upper bound for the full N4 is inferred from the chosen normal columns.
6. The saved 6007 selected normal words plus a triplet do not independently establish `dim U4=6010`. Finite strong generation establishes `U4=W4`; the coefficient 6010 has a later character-theoretic dependency.
7. The old `c8two_jacobi_checked.json` is conditional; its false prerequisite flags precede the final fully authenticated Gate 5 record. Unfinished/refused direct grade-five attempts are not treated as final proof inputs.
8. The original 640-file bundle omitted short-generation and independent grade-three records. The 20260927 supplementary authentication closes that source-ledger omission; hashes still are not mathematical equality/rank proofs.
9. The portable Gate 4 residual checker checks saved vectors, not mode provenance/projector reconstruction. The structural membership coordinate checker similarly checks saved coordinate sums, not mode recipes by itself.
10. The parafermion membership target is the unnormalized saved primary `w`, not the later normalized `a=sigma*w`.

## Source files inspected for interpretation

The exact low-grade engine and checker; numerical lattice and OPE producers; minimal-generation exporter; membership exporter; exact lower-closure producer; saturation and charged-span producers; projected normal-column providers; current main draft finite sections; finite and structural reviewability companions; finite-audit, direct-audit and certificate-audit notes; and final finite theorem synthesis. No historical theorem statement was upgraded merely because an old note uses unconditional wording.

## Static checks

All generated environments and braces were checked for balance; all labels are unique and use the requested prefix. The final source has 27 longtables, including both complete membership tables and both discovery-spectrum tables. LaTeX page count and overflow checks are delegated to the root's integrated build. Every printed added-request row and seed recipe is a direct transcription rather than an inferred new mode identity.

## Read-only review of the root top atlas

Reviewed `build_top_atlas.py`/`top_details.tex` against the current80 exporter, its matrix-check scope, the mixed81 producer, and the structural companion. Field/current index ordering and mode naming match: canonical K0..5, charged field0..7, neutral field8. Each of the saved current80 adjoint components has one term. The81 sector matrices are only bound by metadata in the source JSON; the atlas accurately says so. Suggested an explicit reminder that local complement/cyclic indices differ from the finite-generation and membership indices. No mathematical replay was run.
