# Review register for the c=8 manuscript

Revised 27 September 2026. This supersedes the editorial register of
23 September, preserved in `c8_revision_20260927/baseline/`.
It records mathematical deductions, fresh computational checks, and
remaining assumptions separately. Internal agent review is not external
expert validation.

## Main result and its boundary

The revised main statement has two parts. On the explicit finite lattice
and embedded structural inputs, the manuscript proves strong rationality,
strong unitarity, the complete twelve-component gamma=0 character vector,
and a conformal net with unitary ribbon category Z(H3). It constructs the
diagonal full net theory and a selected holomorphic net extension with
boundary category H3. The latter net is not asserted to be the E8 net.

Complete VOA unitarity, the unitary ribbon identification of Rep(U), and
the selected H3 holomorphic VOA extension retain the geometric annulus
comparison A1. The draft identifies the actual original boundary category
only up to H2 or H3. Matching modular matrices does not settle that choice.
The optional algebraic classification route has its own expressly stated
external computer-assisted completeness assumption and does not prove
positivity of the VOA’s canonical fusion forms.

## Disposition of the original review points

| Original ID | Revised disposition | Evidence and remaining boundary |
|---|---|---|
| R1: the explicit generated algebra | Conventions and provenance expanded; exact checks replayed | The lattice Gram matrix, cocycle, currents, transported PCT, three-term field, and extension of the positive gauge to E8 are printed. Minimal generation now explicitly binds the 120-vector presentation to the short generating set. This record was missing from the old 640-file ledger and is included in the supplemented ledger. |
| R2: all-weight normal closure | Proof supplied | Filtered Wick reduction and lexicographic induction are printed in full, with actual zero-product provenance as a hypothesis. Lean checks selected linear consequences, not this VOA theorem. |
| R3: Gate4 saturation/singlet repair | Proof and fresh verifier replay | Projector bounds follow from lattice energy; nilpotence follows from bounded Cartan weights. The 12 integer-cleared projected identities, exact raising premises, and positive rank witness support all 2,898 required inputs. This is not 2,898 separate ambient-vector replays. |
| R4: Gate5 Jacobi reduction | Proof reordered and expanded; fresh verifier replay | The current/Virasoro bootstrap now precedes its use. Full formal normal spaces and both charged/neutral reductions are explained. The 24 channels follow from Jacobi and exact bottom witnesses, not 24 reconstructed grade-five products. |
| R5: positive stresses and rationality | Complete deductions printed | The C2 argument works inside finite ambient grades; lowest-space trace positivity avoids simultaneous diagonalization and does not assume module unitarity. Vacuum projectivity and the finite braided r-category lemma invoke Etingof–Penneys with hypotheses checked. Embedded regular factors remain exact construction inputs. |
| R6: top bound, branching, rank exclusions | Substantially expanded | The actual order 13 core,14-top table, nonnegative 17/10 certificate, integer-graded branching, both rank alternatives, induction/indicator formulas, conductor 40 equality case, and harmonic-theta normalizations are supplied. Independent Fraction arithmetic and Lean verify the bounded algebraic part of the top estimate. A Lie-theoretic fixed-rank obstruction replaces the old Aut(B/U)=1 computation. |
| R7: actual net branching and sector count (A2) | Proved deduction | The proof uses the actual smeared-field subnet, common-core projections, local irreducibility, finite index and an independent boundary-category count. A mere abstract isomorphism between two net constructions is used only to transfer complete rationality. CKLW automorphism and subnet reconstruction supply the sign-involution bridge. |
| R8: reverse reconstruction (A3) | Proved deduction | The bounded-energy weak-module extension in HT Remark 9.8 is used before finite energy multiplicities are known. Regularity, orthogonal projection and graph closure prove ordinaryness/irreducibility. Linear * full faithfulness is distinguished from tensor equivalence. |
| R9: geometric annulus comparison (A1) | Remains open, narrowed | Density and continuation consequences are proved once specific geometric annuli and their central lifts match. The match itself is an explicit unproved hypothesis. This is the remaining analytic premise for canonical fusion positivity and complete VOA unitarity. |
| R10: C* all-module category/classification | Net route proved; VOA route conditional on A1 | The net boundary category is already C*. Unitary HI(Z3) classification and Morita equivalence identify its center. On the VOA route, Gui’s positivity/Q-system results still need A1. Local modules Vec and all modules H2/H3 are kept distinct. |
| R11: full character vector | Uniqueness proof supplied | The exact two possible principal parts, dim U1 = 6 + 13 gamma, finite modular image and absence of invariant constants establish the full vector. The first four vacuum coefficients also have an independent finite-construction proof. Four unmixed lattice restrictions now follow without extra top-action computations. |
| R12: selected H3 extension and defects | Net version proved; VOA version conditional on A1 | Transport of the canonical H3 algebra gives a holomorphic local net extension and 36 bimodule simples. The VOA extension uses canonical fusion positivity, unitary extension theorems and the c = 8 holomorphic VOA classification. It need not be the original embedded H/U. |

The PDF’s local R1/R2 labels name the embedded-field and finite-top
certificate boundaries; they are separate from this historical R1–R12
numbering.

## Additional repair: parafermion identification

The finite reconstruction proposition now gives an acyclic route from
checked first OPE rows to all generator OPEs. Its uniqueness argument uses
the diagonal subalgebra in the product of two simple vertex algebras and
its unique maximal proper graded ideal. It does not assume freeness of
normal words or silently invoke a universal algebra at a singular
parameter. Exact membership, PCT, translation and polynomial identities
remain the declared computational premises.

## Verification and limitations

Fresh exact outputs and logs live in `c8_revision_20260927/`; frozen source
records are unchanged. The original provenance replay, minimal generation,
grade-two PCT/OPE tests, exact grade-three span, final Gate4, independent
charged-span check, Gate5 and fourteen-top arithmetic have passed.
The exact grade-three replay took 493 seconds and peaked at 0.190 GiB RSS.

`lean/HaagerupIzumi/CFT/FiniteClosure.lean` and `TopBound.lean` both compile
without `sorry` or added axioms. Their printed axiom reports contain only
Lean’s standard propositional extensionality, choice and quotient soundness.
The maximum sampled RSS for these checks was 1.652 GiB.

All numerical work was serial, with the permanent guard, at most two
compute threads/CPUs, hard address limits no greater than 6 GiB, an 8 GiB group
RSS watchdog and at least 32 GiB host MemAvailable. Lattice jobs used at most
2 GiB address limits. The expired September 15 exception was not used.

The checks do not constitute a second implementation of the entire lattice
engine, a complete Lean VOA formalization, or a proof of A1. The final PDF
and source archive are accompanied by the build log and precise scoped
replay ledger. Further exact structural replay coverage is listed there.


Final structural replays also passed: all six order-thirteen spectral
witnesses, all four 81-dimensional mixed tops, the Potts primary’s
membership, and the PF13 candidate’s exact membership/PCT line and
positive stress coefficients. The last replay took about 181 seconds
and peaked at 0.117 GiB. These do not claim a fresh recomputation of
all parafermion polynomial OPE and decoupling records.

The final 54-page PDF has 43 primary bibliography entries. It builds
without unresolved references, duplicate labels, missing glyphs or
box warnings; nine representative pages were visually inspected.
