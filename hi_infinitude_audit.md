# Audit of the claimed infinitude proof

Audited on September 7, 2026. The operative claim is Section 111 of
`haagerup_izumi_class_field_stark_notes.md`, beginning at line 17205, together
with its dependencies in Sections 34, 52, 53, 93–95, and 110. The older
`haagerup_izumi_notes.tex` and PDF predate this final argument.

**Verdict: I think the argument is correct for the theorem actually stated.**
I found no fatal gap in the dependency chain. It establishes complex spherical
and, by algebraic conjugation, pseudo-unitary cyclic Haagerup–Izumi fusion
categories for every odd `n >= 3` with `2^m = -1 (mod n)` for some `m`.
In particular it establishes infinitely many distinct ranks using `n = 2^m+1`.
It does not establish unitarity, categorification at every odd order, or the
stronger proposed class-field/Stark identifications.

The review combined direct examination of the proofs with three independent
reviews of the analytic, arithmetic, and combinatorial/reconstruction steps.
The conclusion rests on the written arguments, not extrapolation from the
computations below. This is a mathematical audit, not formal verification.

## Principal checks

| Step | Audit result |
| --- | --- |
| Section 93: exact Fourier transform and all Q | The cosecant contour has additional poles `h-jB`. They are explicitly retained and cancel against the continued separating-contour residues. The remaining integer residue cancels the exceptional diagonal sample. The gamma normalization and convergence conditions agree with the cited two-gamma integral. Reflection then gives the spectral inverse and all quadratic equations. |
| Section 93.4 and Section 53: algebraicity | No Stark algebraicity is assumed. One real quadratic column and inverse norms give rational critical equations with a negative-definite Hessian. The analytic point is an isolated simple algebraic point. The draft shortens this step: existence and uniqueness of the entire prescribed convex chamber are unnecessary once the analytic solution is in hand. |
| Sections 94–95: exact Frobenius | The minimum-valuation argument makes every phase a unit above 2. The convolution Jacobian reduces to a permutation matrix. The contraction estimate also proves uniqueness against ramified extensions, which is needed to identify the analytic number-field point with the unramified lift. Equality of residue tuples therefore gives the literal characteristic-zero automorphism `W_a -> W_{2a}`. |
| Sections 110.3–110.4: product transforms | The two sampling intervals, all extra poles, and the exceptional integer samples are accounted for. When `h=l`, the noninteger double poles require full residues and the coincident integer sample requires its product correction. Neither can be discarded. |
| Section 110.5: continuous Euler identity | The two-gamma transform gives the convolution symmetry. The permutation/translation symmetry is valid. Their six-step composition has a common nonsingular convergence neighborhood; its exponential factors cancel. Continued contour values are used after specialization. |
| Section 111.1: four-term contour relation | The integrand difference is an exact sine/Laurent identity. In the exhibited initial domain, shifting the primitive's contour by `B` crosses no pole and horizontal boundaries decay. The final specialization has no opposite-pole pinch. The case `h=l` follows without dividing by a vanishing sine. |
| Sections 111.2–111.3: Fourier completion | The coefficients have the required signs and exponential factors. The excluded frequencies form one cyclic interval of length `g-1`. Permutations give `g-1` distinct zeros from smaller first indices. Polynomial interpolation therefore eliminates the excluded block, including at composite orders. |
| Sections 34 and 111.4: collisions and normal form | Collision reductions remain valid at negative dimension when conjugation notation is replaced by algebraic inverse norms. The signed normal-form argument handles repeated entries: repeated rows already prevent the strict-column-maximum situation used in the contradiction. |
| Sections 52 and 111.5: reconstruction | The displayed cubic-to-quartic residual identity supplies the missing quartic reconstruction equations. The cited reconstruction theorem permits the negative dimension embedding. Conjugation to positive categorical dimensions proves pseudo-unitarity, with no inference of Hermitian positivity. |

The external analytic input was checked against
[Belousov–Sarkissian–Spiridonov, equations (2.17)–(2.18)](https://arxiv.org/html/2412.07562v2#S2.E17).
The local lifting input is the standard finite étale correspondence for
henselian rings, as in [Stacks Project, Tag 04GK](https://stacks.math.columbia.edu/tag/04GK).
The categorical hypotheses and allowed dimension signs were checked directly
in [Evans–Gannon, Theorem 2 and equations (4.7)–(4.10)](https://arxiv.org/pdf/1506.03546).

## Replayed and additional calculations

- `python hi_infinitude_fourier_checks.py --orders 3 5 9 17 --digits 40`:
  the formal Laurent primitive identity vanishes; 572 off-solution residual
  factors, 202,368 descending permutations through order 35, and 95,496
  cross-free normal forms through order 17 pass. Numerical coefficient
  checks at orders 3, 5, 9, 17 also pass; the largest reported coefficient
  discrepancy is about `1.78e-38`. These coefficient tests sample
  `h=n-1-g` and `l in {1,h}`; they do not exhaust all ordered triples.
  See `hi_infinitude_audit_fourier_results.txt`.
- `python hi_cubic_quartic.py`: every tested quartic residual decomposition
  passes exactly on rational matrices away from the solution scheme at
  orders 3, 5, and 7, both with and without fixed axes. See
  `hi_infinitude_audit_quartic_results.txt`.
- `python hi_infinitude_double_pole_check.py`: the genuine double-pole
  residue agrees to about `1.08e-32` relative error. The corrected finite
  product quadrature at 80 nodes differs by about `6.58e-12`. This is
  numerical quadrature, not an interval certificate. See
  `hi_infinitude_audit_double_pole_results.txt`.
- `python hi_infinitude_direct_audit.py`: the new checker evaluates phases
  from the positive-strip double-sine integral and sums Q and C directly,
  without the Fourier formula, cubic orbit reduction, or Frobenius action.
  All Q pass at 3, 5, 9, 17, 33, 65. All C pass at 3, 5, 9, 17 (81, 625,
  6,561, and 83,521 quadruples); 1,222 and 1,414 selected C pass at 33 and
  65. Working precision is 80–102 decimal digits, with guard digits for
  cancellation in the negative-dimension matrices. See
  `hi_infinitude_direct_audit_results.txt`. The initial run without these
  guard digits exhausted its absolute-error tolerance at order 65; the
  higher-precision run resolves that numerical precision issue.

## Draft

`hi_infinitude_draft.tex` contains the standalone proof draft, with the
normalizations, residue bookkeeping, algebraicity, exact Frobenius,
Fourier induction, and reconstruction included. Its bibliography identifies
the external inputs. It deliberately separates pseudo-unitarity from
unitarity and makes the algebraic meaning of inverse norms explicit.

The source is a single file and compiles to `hi_infinitude_draft.pdf`
(16 pages). The final two-pass pdfLaTeX build has no warnings, unresolved
references, or overfull/underfull boxes. The title page, contour-identity
page, and final reconstruction/bibliography page were visually inspected.
The original research notes and their pre-existing TeX/PDF were not edited.

Compile from this directory with:

```sh
pdflatex -interaction=nonstopmode -halt-on-error hi_infinitude_draft.tex
pdflatex -interaction=nonstopmode -halt-on-error hi_infinitude_draft.tex
```
