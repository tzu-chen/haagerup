# Review register for the c=8 manuscript

23 September 2026. This is an editorial and logical-dependency review of the
existing proof records. It does not rerun a certificate, independently reprove
the external theorems, or alter a frozen research artifact. No numerical job
was launched. A statement marked for review below is an identified proof
obligation or confidence boundary, not a discovered counterexample.

Primary records read:

- `hi_cft_20260923_c8two_final_theorem.md`;
- `hi_cft_20260923_c8two_certificate_audit.md`;
- `hi_cft_20260923_next_structure_recursive_strong_certificate.md`;
- the rationality, vacuum-projectivity, final-dependency-audit, and reverse
  module-bridge notes linked by those records;
- the headers/provenance portions of the completed Gate4 and Gate5 JSON files.

The final status paragraph of the certificate audit supersedes its retained
historical statements that Gate4 or properness was still open. The typeset
manuscript should present the final argument directly. Historical attempts
need not be reproduced as current uncertainty.

## How to mark the manuscript

Use separate labels for three materially different kinds of dependency:

1. **Exact certificate:** an ambient-vector identity, an exact representation
   identity, or a positive rank witness together with an independently exact
   upper dimension. Its residual arithmetic and source provenance are the
   checkable finite input.
2. **Author deduction — review point:** a new algebraic or analytic argument
   that transports those inputs to a stronger conclusion. A successful
   program does not check this implication.
3. **External theorem:** an explicitly cited classification or extension
   theorem used with its stated hypotheses. Not rerunning a published
   classification is not itself a mathematical gap.

The most prominent review markings should appear on the annulus compatibility
argument and the passage from net sectors to ordinary VOA modules. The
recursive strong-generation lemma also merits a visible review marking:
it is the all-weight implication that makes the finite computations relevant
to properness. Avoid highlighting every exact identity as equally uncertain.

## Specific review points and affected conclusions

| ID | Claim to mark | What actually supplies it | Precise reviewer task | Conclusions affected |
|---|---|---|---|---|
| R1 | The concrete defining field and all additional generators are actual vectors of the same generated VOA U, with compatible lattice cocycle, gauge, and PCT conventions. | Exact field/construction records and normal-word provenance, rather than the proposed character. | Follow one fully specified convention from the lattice basis through the field coefficients, current actions, and normal recipes; verify that the displayed formula for u agrees with the authenticated field file. | The theorem concerns this explicit U; all subsequent model-specific conclusions use that identification. |
| R2 | The finite gates imply differential normal-span closure in all weights. | The recursive strong-generation lemma, a new algebraic deduction. | Check the lexicographic induction on total generator weight and left weight, including nested Wick terms and normal remainders. The crucial hypothesis is actual zero-product provenance for P3 and P4, not merely their weights or dimensions. Verify that the larger spaces used as generators meet the lemma's hypotheses. | Strong generation, U1=K, and properness. Strong rationality has a separate route and should not be made dependent on this step. |
| R3 | The remaining Gate4 inputs follow from raising saturation and the joint-singlet repair. | Exact seed identities, exact raising equations, a rank witness in the known 322-dimensional quotient, and a finite-dimensional sl2 representation argument. | Check well-definedness of f_a on S3/N3, stability of its kernel under both raising operators, current stability of full W4, and the bounds in the FE projector. Explain why a weight-zero class killed by both raisings is a singlet. | The complete Gate4 inclusion and then R2/properness. |
| R4 | Jacobi yields every charged and neutral Gate5 channel. | Exact lower relations, two nonzero triplet coefficients, eight quotient-zero pairs, the charged-span certificate, plus algebra. | Verify S2_0 N4 and (N3)_0 S3 are contained in N5 using the full formal normal spaces and translation reduction; check the neutral charged-bracket argument separately. The weight test applies to the original bottom input. Raising the resulting zero is the valid step; repeating the weight test on raised inputs is not. | Complete Gate5, then R2/properness. |
| R5 | Positive stresses give projective vacuum and, with the finite-category lemma, strong rationality. | Exact positive-stress input and an author deduction using Etingof–Penneys. | Verify regularity of every component subalgebra before U rationality is used; ensure the lowest/generalized weight-zero spaces are invariant under each stress zero mode. Trace positivity needs each operator's diagonalizability and nonnegative spectrum, not a positive form on arbitrary U-modules. Verify the finite abelian/right-exact/Grothendieck–Verdier hypotheses and the moderate-growth estimate. | Strong rationality; all subsequent branching, modular, and extension arguments. |
| R6 | Properness plus the top bound forces the actual restrictions B=U+X and H=U+X+2Y and twelve algebraic simple modules. | Finite top-action certificates, the universal bound 17/10, and the separately written rank/indicator/center arguments. | State why every possible later top in the integer-graded restrictions is excluded and why the finite top action is irreducible. Preserve the spherical hypotheses in rank exclusions; do not replace them by classification statements that require complete unitarity. | Algebraic branching, modular data, character theorem, and the later sector-count argument. |
| R7 | The actual net restriction has the same simple summands and multiplicities as the VOA restriction, and the independent net-side count is twelve. | Reconstructed-field compatibility, invariant projection arguments, and a repetition of the positive spherical rank-six reasoning on the actual net inclusion. | Supply the common-core and closure argument that identifies the relevant endomorphism algebras. Check the transfer of Aut(B/U)=1 from finite-energy reconstruction and the untwisted Z3 input. Merely matching a character or a finite-dimensional branching space would not establish this. | Net sector exhaustion, strong unitarity, and the character interpretation of the diagonal full net theory. |
| R8 | Every simple net sector reconstructs an ordinary irreducible unitary U-module and the comparison is fully faithful as a linear functor. | Henriques–Tener reconstruction plus the separate regularity/orthogonal-projection deduction. | Check that the projection onto an algebraic simple summand preserves the stated common core, commutes with closures/adjoints, and hence is a net intertwiner. Verify why irreducibility removes the potentially infinite energy multiplicities of the weak-module extension. Distinguish linear full faithfulness from a tensor equivalence. | Counting twelve sectors exhausts the twelve VOA simples, yielding strong unitarity. |
| R9 | Every reconstructed module satisfies Tener's precise bounded-localized vertex-operator condition. | The manuscript's new comparison of geometric annulus systems, domain construction, gluing, and analytic continuation. This is not a finite certificate. | Match the annulus actions on arbitrary modules, including central scalars and path/lift choices; prove density of the inverse-finite-energy domains; verify bounded gluing and equality first on incoming/outgoing open sets. For continuation, justify that each component of the insertion domain meets such an open set and that the finite-energy matrix coefficients have the claimed finite Laurent form. Check the common-lift cancellation explicitly. | Positivity of canonical fusion forms, complete unitarity, the subsequent C*-classification route, and the claimed unitary VOA extension. This is the highest-priority analytic review point. |
| R10 | The all-module category of the actual holomorphic extension is C*, and Izumi's classification applies. | Complete unitarity, Gui's Q-system/module results, the one-sided to bimodule construction, and the untwisted pointed subcategory. | Check tensor closure and the * structure in the passage to the all-module category; write out both obstruction vanishings. The local-module category is Vec and is not the category to classify. | The chosen route to Rep(U) equivalent to Z(H3) as a unitary ribbon category. Modular data/characters were established earlier and do not by themselves give this equivalence. |
| R11 | The complete twelve-component character vector equals the gamma=0 Evans–Gannon vector. | The modular/pole uniqueness argument, beyond the displayed initial coefficients. | Identify the full exponent/pole bounds, the coefficient relation dim U1=6+13 gamma, the finite-image modular representation, and the absence of invariant constants. State why cancellation eliminates every remaining holomorphic difference. | The full character formula and exact diagonal partition function, rather than only the first few vacuum coefficients. |
| R12 | Transport of the canonical H3 Lagrangian algebra produces a unitary holomorphic c=8 extension isomorphic to V(E8). | The ribbon equivalence, extension theorems, positivity/integral grading, and the c=8 holomorphic classification. | Check the hypotheses for connectedness, twist, positive nonvacuum lowest weights, rationality and C2-cofiniteness of the finite extension. Keep separate the existence of this chosen extension and the identity of the original embedded extension. | The specifically H3 extension and its U-preserving algebra-bimodule defect category. |

R2–R4 have explicit finite algebraic arguments in the source records; this
review found no reason to replace those arguments by an unproved
"low-weight closure implies all-weight closure" assertion. R9 contains the
largest analytical transport step. Highlighting it should identify the
exact bridge being asserted, rather than vaguely questioning unitarity.

## What the finite checks do and do not establish

The final Gate4 proof is a mixture of exact vector identities and an
algebraic saturation argument. It should not be described as 2,898 separate
ambient-vector calculations. The records list 2,145 original exact
identities, 118 further direct identities, twelve further ordinary raised
identities, twenty-four exact raising premises, and twelve exact projected
identities. The rank and singlet arguments supply the coverage of all
2,898 required inputs.

Likewise, the final Gate5 certificate proves all twenty-four independent
channels through the audited Jacobi reduction. It should not be described
as twenty-four direct reconstructed grade-five residuals. The small
checker authenticates the required finite data for that argument; the
argument itself needs to be printed.

A nonzero minor modulo a good split prime is an exact positive lower-rank
witness in characteristic zero, provided the rational coefficients are
defined at that prime and the selected field embedding is authenticated.
Here the known exact quotient dimension 322 supplies the upper bound.
This is a valid use of finite fields. It does not authorize treating a
rank found among selected grade-four normal columns as an upper bound
for the full grade-four normal space.

The proof only needs positive normal-space memberships, so an exact
identity in any subset of legitimate normal columns is sufficient.
The facts that the saved grade-four normal list is not proved exhaustive
and that the three extra weight-four vectors are not proved minimal
are therefore scope limits, not obstructions to the stated properness
proof. In particular, no minimality claim for P4 should be added.

Hashes, source graphs, and frozen replay records protect provenance;
they do not by themselves prove correctness of the implementation.
A checkable presentation should say which identities are recomputed by
the final verifier and which existing exact certificates it authenticates
as inputs. No fresh end-to-end replay was performed for this typesetting
review. Do not describe this manuscript preparation as an additional
independent computational verification.

## Suggested dependency summary beside the main theorem

The following text gives a concise, accurate review boundary:

> The finite lattice identities are accompanied by source-bound exact
> certificates. Their passage to properness uses the recursive
> strong-generation and current-representation arguments printed below.
> Strong rationality, sector exhaustion, and complete unitarity additionally
> use the stated algebraic and analytic deductions. The annulus comparison
> supplying bounded localized module fields is a separate analytic proof
> step, not a consequence of the certificate status. The final ribbon
> identification and holomorphic extension use the cited classification and
> extension theorems.

This is more informative than a blanket claim that the theorem is uncertain
because it is unreviewed, or a blanket claim that all of it is certified by
the computer. Lack of proof-assistant formalization should be reported as
the proof format, not treated as a missing mathematical hypothesis.

## Explicit limits that belong in the typeset theorem or following remark

- The original embedded extension H/U is identified only up to the two
  possibilities H2 and H3 at the all-module-category level. The separately
  chosen canonical H3 algebra proves the existence of an H3 extension;
  it does not resolve that original embedding's label.
- The argument does not construct or identify the natural braided tensor
  functor between all VOA modules and net sectors. Linear full faithfulness
  and sector exhaustion have the explicitly stated uses above.
- The algebra-bimodule defects preserve U. They need not commute with the
  enlarged E8 chiral algebra; the local chiral H'-module category is Vec.
- No uniqueness theorem for all c=8 CFTs, no continuum-limit statement for
  the lattice chain, and no c=2 tensor-factor decomposition is established.
- The diagonal full-theory assertion specifies c_L=c_R=8. It should not
  be phrased as a statement that their sum is 8.

## Local typesetting tools checked, without installation or compilation

`kpsewhich`, `pdftoppm`, and `pdfinfo` are installed under `/usr/bin`.
The installed TeX tree contains `microtype.sty` and `xurl.sty`.
`kpsewhich tcolorbox.sty` and `kpsewhich mdframed.sty` returned no path.
The author can use ordinary LaTeX color/rule/minipage constructs for review
boxes without introducing either missing package.

Only read-only shell inspection and this new Markdown file were used.
The expired research-window memory exception was not used; no calculation
or TeX compilation was launched by this reviewer.
