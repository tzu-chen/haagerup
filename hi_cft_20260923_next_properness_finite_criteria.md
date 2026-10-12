# Properness after rationality: finite criteria and a truncation obstruction

23 September 2026. Analytical and source review only; no numerical job was
launched. U is taken to be the actual strongly rational conformal subVOA
already constructed in B. The new bound puts every simple summand of B at
an integer lowest weight between 0 and 5.

**No properness proof is obtained here.** Two precise sufficient certificate
formats are available: the complete level-five Zhu action, or a closed finite
strong-generator presentation. The original generators' compressed mode
matrices do not automatically supply either certificate.

## 1. A sharper finite endomorphism target: the single grade B5

Write the finite semisimple restriction as

    B = direct_sum_i M_i tensor C^(m_i),

where the M_i are inequivalent simple U-modules, with lowest weights h_i in
{0,1,2,3,4,5}. Each summand has a nonzero absolute grade-five slice. For a
unitary module at a positive weight lambda,

    ||L(-1)v||^2 = 2 lambda ||v||^2 + ||L(1)v||^2,

so translation is injective there. This propagates a positive-weight top
to grade five. The h=0 module is U, and U1 contains six currents, so U5 is
nonzero as well.

Let A5(U) denote the usual Dong–Li–Mason fifth Zhu algebra (subscript 5,
not Huang's superscript construction). Rationality makes it semisimple.
Its nonzero simple modules are the relative-grade slices M_i(r), 0<=r<=5;
the pair (i,r) distinguishes them. These assertions follow from
[Dong–Li–Mason, Proposition 3.4 and Theorems 4.9–4.10](https://arxiv.org/html/q-alg/9612010).

Since B5 contains exactly M_i(5-h_i) with multiplicity m_i, restriction gives
an algebra isomorphism

    End_U(B)  -->  End_A5(U)(B5).

Indeed, both sides are the same direct sum of matrix algebras End(C^(m_i)).
This proves surjectivity here, beyond the earlier injective restriction to
B0 through B5. The argument uses the full A5(U) action on an actual module.

Consequently properness has the finite equivalent criterion

    U != B  iff  dim End_A5(U)(B5) > 1.

The vacuum U occurs with multiplicity one, because B0 is one dimensional.
If no other summand occurs, B=U; otherwise the commutant has a nontrivial
projection. Any A5(U)-linear endomorphism of B5 has a unique U-linear
extension to B. In particular a nontrivial idempotent is a properness
certificate once its commutation with the **complete** A5(U) image is proved.

The missing computational gate is substantial. A5(U) acts by o(a) for every
homogeneous a in U, not just the original seven/eight generating fields or
the currently certified finite spans. Its image is finite dimensional, so a
finite spanning list exists; its existence does not identify that list or
bound the weights needed to produce it. Closure of a guessed list under
ordinary matrix multiplication is not a proof that it contains every o(a).

One useful asymmetric conclusion does survive a truncated calculation. If
the commutant of a tested subset of genuine U zero modes on B5 is already
only the scalar matrices, then the complete commutant is scalar and U=B.
Finding a larger commutant only supplies candidates for extension.

## 2. Why the more general finite-matrix reconstruction theorem is not a shortcut

[Huang's A^N(U) construction, Sections 2, 4 and 5](https://arxiv.org/html/2009.00262)
uses a filtration Omega_n defined by all U-fields. It yields finite
associative algebras under C2-cofiniteness and useful reconstruction
statements, but the introduction explicitly cautions that its module
categories are not equivalent on morphisms. It does not replace its
algebra action by compressed modes of a weak generating set.

Also distinguish the two cutoffs. The universal simple-weight difference
bound furnished by 0<=h<=938/169 is covered by the integer N=6. The cutoff
5 is specific to the integral spectrum of B. Neither bound alone proves
that a generator word can be rewritten without intermediate grades above
the cutoff.

## 3. An explicit high-excursion obstruction, even with semisimplicity

For any N>=1, take a finite-dimensional Hilbert space with orthonormal basis

    v0;  v1,w1;  v2,w2; ...; vN,wN;  z.

Their grades are respectively 0,1,2,...,N,N+1. Let H be the grading operator.
Let the degree-one operator A raise along each chain and join them at z:

    A vi = v(i+1)      for 0<=i<N,
    A wi = w(i+1)      for 1<=i<N,
    A vN = A wN = z,   A z = 0.

Include A*, the Hilbert adjoint, among the generators. On the truncation
through grade N, projection P onto span(v0,...,vN) commutes with every
compressed generator H, A and A*. It fixes v0 and kills w1.

The full representation is nevertheless irreducible. The vector v0 is
cyclic: powers of A give its chain and z, and A*z=vN+wN then gives the
second chain by subtraction and lowering. Since H has a one-dimensional
grade-zero eigenspace, any reducing decomposition puts v0 in one summand;
cyclicity forces that summand to be the whole space. The generated complex
*-algebra is therefore a full matrix algebra. It is semisimple and has
only one simple representation, whose lowest grade is zero.

The invisible obstruction is explicit:

    (A*)^(N+1) A^N w1 = v0.

It travels through grade N+1. Hence P cannot extend to a commuting full
projection. This works for arbitrarily large N, although the only simple
top remains at zero and the full space is generated by its lowest grade.

This is an associative graded *-algebra example, not a VOA example. Its role
is to show exactly why semisimplicity, bounded tops, adjoints, and generation
from bounded grades do not by themselves justify the proposed finite
projection extension. A VOA-specific rewriting or presentation theorem
must supply the missing implication. The separate Ashihara Griess-algebra
counterexample already rules out using Griess closure as such a theorem.

## 4. A finite strong-presentation certificate that would prove properness

Find a finite homogeneous set S of explicitly certified U-fields satisfying:

1. S contains the original VOA generators (or explicitly generates them).
2. Its weight-one part spans exactly the six retained currents K1.
3. For every a,b in S and every n>=0 with possible nonzero output, give an
   exact identity expressing a_n b as a differential normally ordered
   polynomial in S and the vacuum.

If H is the largest generator weight, these are finitely many equations,
and every output has weight at most 2H-1. The fields already live inside B,
so the actual identities inherit Jacobi and locality there. The
noncommutative Wick formula and the iterate identities then make the span
of all normally ordered S-words and their derivatives a vertex subalgebra.
It contains the original generators and is contained in U, hence equals U.
Thus S strongly generates U, and positive weights force U1=span(S1)=K1.
Since dim B1=86, this proves U!=B.

This is the standard nonlinear-OPE reconstruction mechanism, with null
relations retained; see [De Sole–Kac](https://arxiv.org/html/math-ph/0312042)
and the discussion of degenerate nonlinear conformal algebras in
[Linshaw, Section 3](https://arxiv.org/html/1710.02275). It requires actual
normal-polynomial identities, not membership in a finite span that was
itself obtained using unrestricted positive modes.

This distinguishes the proof gate from the current S4 calculation. The
new exact S4 producer computes a finite generated span and tests lowering;
it does not test all singular OPEs of a proposed finite strong generating
set. For example, a candidate S of maximum weight three requires singular
OPE checks through weight five, including the weight-five simple poles of
weight-three pairs. If those checks fail, their normal-span complements
are new strong-generator candidates. C2-cofiniteness guarantees some finite
strong generating set exists, but provides no current explicit H.

The practical refinement is to organize S and its OPE pairs into finite
K representations and certify highest-weight tensor channels, then use
exact current equivariance. That can reduce the number of equations; it
does not remove any tensor channel or replace the normal-span condition.
