# Rationality from projective vacuum and the Etingof–Penneys theorem

23 September 2026. This independent categorical argument completes
rationality of the constructed U, using the preceding C2-cofiniteness
certificate and the positive-stress identity. It does not decide U=B
versus U proper, and it does not identify its module category.
No numerical job was launched; the permanent resource limits apply.

**Theorem.** The constructed simple unitary conformal VOA U is strongly
rational.

The crucial newer input is
[Etingof–Penneys, arXiv:2412.17681v3, Theorem 1.1](https://arxiv.org/html/2412.17681v3).
The inspected v3 has arXiv header 27 July 2026 and body date 24 August
2026. Its hypotheses do not include semisimplicity or exactness of
tensoring. For an indecomposable object X in a Cauchy-complete linear
braided category with finite-dimensional Hom spaces and End(1)=C,
it proves rigidity if (i) 1 is a direct summand of Y tensor X for some Y,
and (ii) dim End(X tensor-power n)<n! for some n.

## Categorical lemma

Let C be a finite complex linear abelian braided monoidal category
with simple unit 1, tensor product right exact in each variable, and
Grothendieck–Verdier duality whose dualizing object is 1. If 1 is
projective, then C is semisimple and rigid.

First, all objects have the moderate growth required by
Etingof–Penneys. Choose an equivalence of finite abelian categories
C equivalent to finite-dimensional left A-modules for a finite-dimensional
algebra A, and let P correspond to the regular A-module. Write d(Z)
for the ordinary vector-space dimension of the A-module corresponding
to Z. Every Z is a quotient of P direct-sum d(Z) times. For fixed X,
right exactness gives a quotient

\[
 (P\otimes X)^{\oplus d(Z)}\twoheadrightarrow Z\otimes X.
\]

Consequently, with C_X=max(1,d(P tensor X)),

\[
 d(Z\otimes X)\leq C_X d(Z),\qquad
 d(X^{\otimes n})\leq d(\mathbf1)C_X^n.
\]

Since the chosen equivalence is faithful and complex linear,

\[
 \dim\operatorname{End}_{\mathcal C}(X^{\otimes n})
 \leq d(\mathbf1)^2 C_X^{2n}<n!
\]

for sufficiently large n. This proof uses only right exactness, which
is available before rigidity; it does not assume tensor-exactness or
that tensoring preserves projective objects.

Next, for every nonzero indecomposable X, Grothendieck–Verdier duality
provides a nonzero evaluation DX tensor X -> 1, corresponding to the
identity of DX under its representing property. Simplicity of 1 makes
this evaluation an epimorphism. Projectivity of 1 makes it split.
Thus X is non-negligible in the exact sense used by Etingof–Penneys.
Their Theorem 1.1 proves that X is rigid. Finite abelian categories are
idempotent complete and have finite direct sums and Krull–Schmidt
decompositions. Therefore every object of C is rigid.

Once rigidity has been obtained, tensoring is exact. For any X, its
dual X* gives

\[
 \operatorname{Hom}(X,-)
   \cong\operatorname{Hom}(\mathbf1,-\otimes X^*).
\]

The right side is exact because the unit is projective and tensoring
with X* is exact. Hence every object is projective and C is semisimple.
This completes the categorical lemma.

## Verification for the actual U

U is CFT type, simple, self-contragredient and C2-cofinite, by the
unitary construction and the certified positive-stress argument. Its
category C of grading-restricted generalized modules is finite abelian
and braided. Tensoring is right exact, and contragredients provide
Grothendieck–Verdier duality with dualizing object U'=U. These standard
VOA category facts, including the hypotheses under which they apply,
are reviewed in
[McRae, Sections 2.3 and 3](https://arxiv.org/html/2108.01898).
For right exactness see the explicit use of HLZ3 Proposition 4.26 in
the proof of McRae's Theorem 3.8. Simplicity gives End_C(U)=C.

The note `hi_cft_20260923_next_structure_vacuum_projective.md` proves
projectivity of U directly. Its two essential steps are:

1. On any simple U-module's finite lowest space, regular subalgebras
   in the positive stress identity have diagonalizable stress zero
   modes with nonnegative spectra. Taking traces implies that every
   simple U-module has nonnegative lowest weight.
2. For an epimorphism E->U, finite length then excludes negative
   generalized weights in E. The generalized weight-zero space lies
   in the highest spaces of all these regular subalgebras. Its L(0)
   trace is zero, so positivity of the coefficients forces every
   component stress zero mode to vanish. Each component has only its
   vacuum sector at weight zero. Their translation operators therefore
   vanish there, and the stress identity forces L_U(-1)=0 on that
   space. Any lift of the vacuum gives a vacuum-like vector and hence
   a section U->E.

All categorical-lemma hypotheses are now met. The module category is
semisimple, hence U is rational; together with the existing properties,
it is strongly rational. The argument does not infer semisimplicity
from unitarity of selected modules or from finite branching of B.

## Relation to the preceding audit

The projective-vacuum note correctly observes that the older route
through Miyamoto semi-rigidity or McRae's ordinary-character S-transform
requires an additional hypothesis. Etingof–Penneys supplies that missing
rigidity implication here, using the explicit moderate-growth argument
above. There is no assumption that all irreducible U-modules already
occur in lattice-sector restrictions, and no categorical dimension of
B is assumed.

The known alternative U=B remains compatible with strong rationality.
Properness, complete branching and the Haagerup braided-category
identification still need their own proofs.
