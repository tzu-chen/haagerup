# Verification-guide manuscript-anchor audit: archived before-update state

**Status:** This report records the guide **before root's reference updates**.
All source line numbers, descriptions of existing text, and local-reference
inventories below are historical snapshots, not claims of remaining defects
in the updated guide. Root subsequently replaced the stale manuscript
references with stable links. The current guide includes the copied fragment
`c8_physics_20260927/verification_finite_inputs.tex` in place of the original
`c8_reviewability_20260927/finite_inputs.tex` audited here. Root also resolved
the local u-reference issue using the guide-local label
`hr:three-term-vector`. The old ledger, formalization, and compilation
sections were **appendices A, B, and C**, respectively, in the initial
55-page manuscript; their corrected mapping is given below.

Audit date: 27 September 2026. Read-only review of
`hi_cft_c8_verification_guide.tex`, its two included fragments
`c8_reviewability_20260927/finite_inputs.tex` and
`c8_reviewability_20260927/structural_inputs.tex`, against the current
`hi_cft_c8_proof.aux` and the manuscript's three mathematical source files.
No guide or manuscript source was changed by this audit, and no build or
numerical job was run. The manuscript auxiliary file inspected ended with
`\gdef \@abspage@last{78}`. The guide auxiliary file then described a
20-page guide; its equation numbering is independent of the manuscript's.

## Complete inventory of literal external numbers before root's updates

There were exactly **two literal manuscript section ranges** in the expanded
guide and one stale page-count description. There were **no literal external
proposition, theorem, lemma, corollary, certificate, or equation numbers**
elsewhere in the three guide sources. The named mathematical results and
formulas can nevertheless receive the stable links listed below.

| Guide source and location | Existing text | Current destination | Recommended replacement |
|---|---|---|---|
| `hi_cft_c8_verification_guide.tex:36–38` | “the 55-page revision of 27 September 2026. Section and proposition numbers prefixed by ‘manuscript’ refer to that version” | Current manuscript has 78 pages; construction/proof sections are now appendices A–O | Remove the fixed page count. State that links labelled “manuscript” resolve against the accompanying manuscript. If needed, give an anchored entry point: `manuscript Appendix~\msref{sec:construction}, p.~\mspageref{sec:construction}`. |
| `hi_cft_c8_verification_guide.tex:55` | `manuscript Sections~3--12` | Appendices B–K: finite closure through the chosen full theory/extension | `manuscript Appendices~\msref{sec:finite}--\msref{sec:analytic-full-theory}`. Current endpoints B, p.31 and K, p.69. |
| `c8_reviewability_20260927/finite_inputs.tex:4–5` | `Sections 2--6 of the manuscript` | Appendices A–E: lattice construction through properness | `Appendices~\msref{sec:construction}--\msref{sec:properness} of the manuscript`. Current endpoints A, p.28 and E, p.38. |

The ranges above preserve the intended mathematical scope. They should
**not** become references to the new physics Sections 2–6 or 3–12.
“Gate 4”, “Gate 5”, and “Gates 4–5” are names of construction gates;
their digits should not change when the manuscript is reorganized.

## Complete old-section to current-label map

This expands both stale ranges and provides the nearby continuation
sections needed by the final reproduction discussion. The old section
numbers refer to the mathematical manuscript organization before the
physics material was placed before its appendices. The initial 55-page
manuscript ended with appendices A–C, rather than numbered sections 14–16.

| Old section | Current appendix and first page | Stable label | Current title |
|---|---|---|---|
| 2 | A, 28 | `sec:construction` | The explicit lattice construction |
| 3 | B, 31 | `sec:finite` | Finite closure and the all-weight criterion |
| 4 | C, 34 | `sec:gate4` | Gate 4: exact seeds, raising, and singlet recovery |
| 5 | D, 36 | `sec:gate5` | Gate 5 from Jacobi identities |
| 6 | E, 38 | `sec:properness` | From the finite gates to properness |
| 7 | F, 39 | `sec:regularity` | Regularity from a positive conformal-vector identity |
| 8 | G, 44 | `sec:branching` | Branching and the boundary fusion ring |
| 9 | H, 58 | `sec:characters` | The complete character vector |
| 10 | I, 59 | `sec:analytic-unitarity` | From vacuum unitarity to complete unitarity |
| 11 | J, 67 | `sec:analytic-category` | Unitary categorical identifications |
| 12 | K, 69 | `sec:analytic-full-theory` | Full net theory and a chosen E8 VOA extension |
| 13 | L, 71 | `sec:comparison` | Relation to the proposed Haagerup theories |
| Appendix A | M, 71 | `sec:ledger` | Certificate ledger and reproducibility |
| Appendix B | N, 74 | `sec:formalization` | Limited formalization |
| Appendix C | O, 75 | `sec:compilation` | Compilation and review scope |

The guide can use `\msnameref{...}` for the titles above. Page numbers in
this report are audit snapshots; put `\mspageref{...}`, not literal page
numbers, into the guide.

## Named results and formulas: exact external destinations

The following were **unnumbered prose references or repeated
formulas in the audited guide**, not additional stale numeric citations. These
destinations are available if root wants a fully navigable guide.

### Guide overview, lattice calculation, and stress calculation

| Guide reference/content | Stable manuscript label(s) | Current printed number and page | Notes |
|---|---|---|---|
| Main properness conclusion | `prop:mainproper` | Proposition 1.1, p.5 | Properness is construction-input-dependent. |
| Initial graded pieces | `cor:initial-grades` | Corollary 1.2, p.5 | Distinct from the initial-space certificate below. |
| Main conformal-net realization | `thm:main-net` | Theorem 1.3, p.5 | Appropriate overview link for the net conclusion. |
| Main VOA realization and extension | `claim:main` | Theorem 1.4, p.6 | Label retains `claim:` although the environment is a theorem. |
| Definition of U | `eq:U` | (1), p.5 | Not the guide's equation (1). |
| Cocycle | `eq:cocycle` | (79), p.28 | Same signs used in the guide. |
| Exponential lattice product | `eq:lattice-product` | (80), p.29 | Guide's coefficient extraction. |
| Left and right current triples | `eq:leftcurrents`, `eq:rightcurrents` | (81), (82), p.29 | Two separate labels. |
| Affine levels 1 and 39 | `lem:levels` | Lemma A.1, p.29 | The guide works out these checks explicitly. |
| Three-term defining vector u | `eq:u` | (83), p.29 | Its guide occurrence is currently an unnumbered formula in subsection 2.1. |
| Transported PCT | `eq:pct` | (84), p.30 | Appropriate link for transported conjugation and positive form. |
| Ambient and Sugawara stresses | `eq:ambient-stress`, `eq:sugawara` | (85), (86), p.30 | The four-axis check uses these conventions. |
| Actual S2 and S3 construction | `cert:initial` | Certificate A.2, p.30 | The finite-generation queue verifies part of this input. |
| Two retained coset stresses | `eq:two-coset-stresses` | (87), p.31 | Manuscript's e and f. |
| Positive averaged-stress identity | `eq:positive-stress` | (104), p.39 | The guide's explicit four-column check proves the projected vector identity; the Haar-average interpretation retains its stated invariant-space input. |
| Finite positive sum replacing averages | `eq:finite-positive-stress` | (105), p.40 | A proved convexity consequence, not another coefficient certificate. |
| Strong rationality from positive stresses | `thm:positive-stress-rationality` | Theorem F.8, p.44 | Suitable link for the overview's “regularity” conclusion. |

### Included finite-input fragment

| Guide reference/content | Stable manuscript label(s) | Current printed number and page | Notes |
|---|---|---|---|
| Short generating set and resulting saved spaces | `eq:U`, `cert:initial` | (1), p.5; Certificate A.2, p.30 | Do not identify inclusion S2 subset U2 with equality before the all-weight proof. |
| Differential normal span | `def:normal-span` | Definition B.1, p.31 | Applies to the named normal words. |
| “filtered Wick” at fragment lines 470–471 | `lem:filtered-wick` | Lemma B.2, p.31 | Its displayed formula has separate label `eq:wick`, (88), p.32. |
| “recursive zero-product argument” at lines 470–471 | `thm:recursive` | Theorem B.3, p.32 | `eq:recursive-jacobi` is (89), p.32. |
| Scope of finite controls | `rem:finite-scope` | Remark B.4, p.33 | Appropriate distinction between actual identities and the general theorem. |
| N4,W4 and N5 | `eq:normal4`, `eq:normal5` | (90), (91), p.33 | The guide has no numbered external reference here. |
| Current projector degree bounds | `lem:current-bounds` | Lemma B.5, p.33 | Applies to the finite projector polynomial. |
| Lower identities and actual triplet | `cert:lower` | Certificate B.6, p.34 | Separate finite input. |
| Gate 4 inclusion | `eq:gate4` | (92), p.34 | Gate name remains “4”. |
| Gate 5 inclusion | `eq:gate5` | (93), p.34 | Gate name remains “5”. |
| Raising saturation argument | `lem:raising` | Lemma C.1, p.34 | Guide's finite rank argument. |
| Recovery of the singlet from its projection | `lem:singlet` | Lemma C.2, p.34 | Distinct from merely checking a projected residual. |
| Projector polynomial | `eq:projector` | (94), p.34 | Guide's explicit polynomial specializes this formula. |
| Positive-mode bootstrap | `lem:bootstrap` | Lemma C.3, p.35 | Section anchor `sec:bootstrap` gives C.1, p.35. |
| Three groups of positive-mode controls | `eq:positive-S3`, `eq:positive-W4`, `eq:positive-N5` | (95)–(97), p.35 | Use individual labels if adding an equation range. |
| Gate 5 normal-space controls | `lem:normal-controls`, `eq:normal-lemmas` | Lemma D.1 and (101), p.36 | The lemma and its equation have different labels. |
| Iterate identity | `eq:iterate` | (102), p.36 | Formal identity used in the finite Jacobi reduction. |
| Jacobi reduction | `lem:jacobi`, `eq:jacobi-reduction` | Lemma D.2 and (103), p.37 | The guide's small scalar bracket is local equation (4), not manuscript (103). |
| Charged and neutral scalar witnesses | `sec:gate5` | Appendix D, p.36 | The manuscript's charged/neutral subsections have no separate stable labels; do not invent a theorem number for a witness. |
| Properness after Gates 4 and 5 | `sec:properness` | Appendix E, p.38 | Result also summarized by `prop:mainproper`. |
| “source ledger” near fragment end | `sec:ledger` | Appendix M, p.71 | Fresh replay subsection M.1 currently has no own label. |

### Included structural-input fragment

| Guide reference/content | Stable manuscript label(s) | Current printed number and page | Notes |
|---|---|---|---|
| “manuscript's embedded structural-data certificate”, line 7 | `cert:structural-inputs` | Certificate F.1, p.39 | Former Certificate 7.1 if restoring that old reference; link to the certificate, not all of Appendix F. |
| Potts, parafermion, core, finite tops | `cert:structural-inputs` | Certificate F.1, p.39 | These are its four numbered items. |
| “manuscript's finite reconstruction proposition”, line 236 | `prop:pf13-finite-reconstruction` | Proposition F.2, p.40 | Former Proposition 7.2 if restoring that old reference. |
| PF13 iterate used by reconstruction | `eq:pf13-b-iterate` | (106), p.41 | This is not any of the guide's explicit PF13 equations (7)–(11). |
| Orthogonal energy bound underlying regularity | `lem:positive-c2` | Lemma F.3, p.42 | For an optional link from the large-check boundary. |
| Compatible highest-space argument | `lem:compatible-top` | Lemma F.4, p.42 | Distinguishes intrinsic and ambient grading. |
| Vacuum projectivity | `lem:vacuum-projective` | Lemma F.6, p.43 | Optional exact theorem link for the overview. |
| Positive-stress regularity conclusion | `thm:positive-stress-rationality` | Theorem F.8, p.44 | Use here for “regularity” at structural lines 543–544. |
| Core and six spectral witnesses | `sec:branching` plus `cert:structural-inputs` | Appendix G, p.44; Certificate F.1, p.39 | The core discussion is in G.1 but that subsection has no separate label. The guide's explicit spectral table has only a guide-local label. |
| Universal h<2 top bound, line 543 | `eq:sharp-top-bound` | (111), p.46 | This displays the stronger h≤17/10<2 bound. Its derivation starts in G.1. |
| Actual B branching | `eq:B-branching` | (112), p.46 | Consequence of top bound and current/top evidence. |
| Rank alternative from holomorphic extension | `eq:H-branching-fork` | (113), p.47 | Separate from B branching. |
| All-weight irreducibility from finite tops | `sec:branching`, `eq:sharp-top-bound`, `thm:positive-stress-rationality` | G, (111), F.8 | There is no standalone manuscript theorem labelled “finite cyclicity”; the guide provides the elementary finite-dimensional proof directly. |
| Unmixed lattice restrictions | `cor:unmixed-lattice-restrictions` | Corollary H.2, p.59 | Do not substitute this for the guide's four **mixed** 81-dimensional tops. |
| Complete character exhaustion/uniqueness | `lem:haagerup-character-unique`, `sec:characters` | Lemma H.1, p.58; Appendix H | Optional overview links. |
| Complete unitarity, overview and final paragraph | `thm:analytic-complete-unitarity` | Theorem I.8, p.67 | End of the analytic proof, not an input to finite cyclicity. |
| Unitary Haagerup-center identification | `thm:analytic-category` | Theorem J.2, p.68 | Optional overview link. |
| Chosen E8 extension | `thm:analytic-e8-extension` | Theorem K.3, p.69 | End of the intended old Sections 3–12 range. |
| Limited Lean formalization | `sec:formalization` | Appendix N, p.74 | The final guide paragraph also links to a separate Lean-assessment PDF. |

## Existing local references: keep them local

Every existing `\ref` or `\eqref` in the expanded guide is internal.
None should be converted to `\msref`, `\mspageref`, or `\msnameref`.
The following inventory lists every referenced local label, including
all occurrence locations. Their current numbers come from
`hi_cft_c8_verification_guide.aux`.

| Local label | Current local number | Source occurrences using it |
|---|---|---|
| `eq:reader-row-recipe` | (1) | `finite_inputs.tex:345` |
| `eq:reader-projected-residual` | (2) | `finite_inputs.tex:222,258` |
| `eq:reader-small-bracket` | (4) | `finite_inputs.tex:359,376` |
| `hr:membership-words` | subsection 5.4 | `structural_inputs.tex:120` |
| `hr:positive-stress-check` | section 3 | `structural_inputs.tex:308` |
| `hr:pf-last-pole` | (10) | `structural_inputs.tex:213,230` |
| `hr:pf-ab` | (8) | `structural_inputs.tex:215` |
| `hr:pf-derived-pole` | (11) | `structural_inputs.tex:229` |
| `hr:pf-decoupling` | (9) | `structural_inputs.tex:234` |
| `hr:core-eigenvalues` | (12) | `structural_inputs.tex:372` |
| `hr:cyclic-recipes` | (13) | `structural_inputs.tex:515` |
| `hr:potts-field`, `hr:potts-primary` | (5)–(6) | `structural_inputs.tex:559` |

Other defined but currently unreferenced guide labels are
`sec:reader-finite`, `eq:reader-seven-zeros`, `hr:structural-inputs`, and
`hr:pf-selfrow`. They also belong to the guide namespace.

One additional local prose reference was misleading and has been resolved:
`finite_inputs.tex:64` calls u “the displayed three-vertex field in the
preceding section”. The immediately preceding guide section is the
positive-stress calculation, whereas u appears in guide subsection 2.1.
Best fix: add a guide-local label to “The three-term vector without a
mode engine” and use `\ref` to that subsection. Alternatively replace
“in the preceding section” with “in the lattice calculation above”. It
does not require an external manuscript reference. Root implemented this
fix with the guide-local label `hr:three-term-vector` in the updated guide
and its copied finite-input fragment.

## Linking conventions and limitations

Use the current environment type before `\msref`: for example
`manuscript Proposition~\msref{prop:pf13-finite-reconstruction}` and
`manuscript Certificate~\msref{cert:structural-inputs}`. Their old numeric
values should not be retained anywhere in source. For an equation,
wrap `\msref` in parentheses if the macro returns the raw number:
`manuscript equation~(\msref{eq:positive-stress})`.

No stable labels presently identify the manuscript's G.1 subsection,
individual six spectral witnesses, 80-current cyclicity paragraph,
individual 81-dimensional tops, charged/neutral Gate-5 subsections, or
fresh-replay subsection M.1. A containing appendix/certificate is an
honest destination; an invented lemma/equation anchor is not. The guide
already supplies finer local labels for its spectral and row-recipe
equations, so those should be used when the reader is being directed
to the actual human-readable witness rather than to the manuscript's
proof context.
