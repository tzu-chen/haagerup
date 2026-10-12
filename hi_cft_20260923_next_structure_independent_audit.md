# Independent audit: top bound, vacuum projectivity, and rationality

23 September 2026. This is a source and algebra audit. No numerical or
exact-arithmetic job was launched. The permanent resource limits remain in
force. The existing computational certificates are inputs; this note does
not independently reimplement their lattice-mode calculations.

**Audit outcome:** the top-weight bound and the vacuum-projectivity argument
pass. The Etingof–Penneys theorem supplies a further categorical step: together
with the established positive-stress identity and C2-cofiniteness, it proves
strong rationality of the constructed U. Properness and the Haagerup category
remain separate questions.

## 1. Different conformal vectors do not invalidate the top-space restriction

Let A be one of the regular subalgebras in the positive stress identity,
including T when the sharpened identity is used. Its internal conformal
grading agrees with its inherited U-grading. Thus, for homogeneous a in A,
the modes defining Omega_A(M) are exactly the ambient lowering modes.
They annihilate the lowest U-space E. Moreover e_1 has ambient degree zero,
so it preserves E. Regularity decomposes the restricted weak A-module into
ordinary simple A-modules; their Omega spaces are their actual lowest spaces.
Consequently the spectrum of e_1 on E consists of actual lowest A-weights.

No claim that omega_A equals omega_U on all of M is needed. No invariant
positive form on M or simultaneous diagonalization of different e_1 is used.
The finite-dimensional trace argument is valid.

## 2. The core table and charge estimate pass independent algebraic checks

In the orthogonal a0,H coordinates, dual-lattice integrality is precisely
s,m integral with s=m modulo 2. Translation by a0 changes s by 2, and
translation by t changes (s,m) by (3,39). The extension momentum r changes
them by (1,13). Thus the lattice cosets and order-three extension orbits used
in the note have the stated sizes.

Use the bilinear convention b(J,X)=h(JX)-h(J)-h(X) modulo 1. The lattice
contribution is 2m/3 and the Potts contribution is a/3. Locality therefore
requires a=m modulo 3, compatibly with the extension shift. Reversing the
monodromy convention reverses both signs and gives the same condition.

I checked all fourteen entries of the displayed T table using the actual
weights, including the alternate representatives j-13. The maximum is
14/13. Every H-charge m on a T top therefore satisfies m^2<=168 and hence
|m|<=12. This controls every finite-dimensional right-sl2 constituent of E:
its highest label is an H eigenvalue, so it is at most 12. The Sugawara
eigenvalue bound is consequently 42/41.

The current normalization also gives
average(H(-1)^2/156)=(41/117) omega_A1,39.
Subtracting this averaged core stress from the original identity leaves
the positive coefficients 1804/4563, 19/6, and 25/26. The final sum is

    (1638 + 616 + 3211 + 4725)/1521 = 10190/1521 < 7.

The uniqueness argument for a weight-zero simple module passes as well.
Once every component stress vanishes on its top, each component translation
vanishes there. Their positive linear combination is L_U(-1). If L(-1)v=0,
the relation L(-1)a_n v=-n a_(n-1)v and lower truncation imply a_n v=0 for
all n>=0. Thus v is vacuum-like and a -> a_(-1)v gives the required map
from U. This supplies the detail behind the translation step in the note.

## 3. Vacuum projectivity: the generalized weight-zero argument is sound

Consider a surjection pi:E->U in the grading-restricted generalized category.
This category has finite length. Since every simple constituent has
nonnegative lowest weight, E has no negative generalized conformal weights.
Let F=E_[0]. It is finite dimensional, and pi(F) contains the vacuum.

For every regular A in the positive stress decomposition, F is contained in
Omega_A(E). Each e_1 preserves F, is diagonalizable there, and has nonnegative
real eigenvalues. L_U(0) on F may initially be nilpotent; nonetheless its
trace is zero. Therefore

    0 = Tr_F L_U(0) = sum_i c_i Tr_F(e_i,1),   c_i>0

forces every e_i,1 to vanish. The unique zero-weight simple A-module is its
vacuum module, so e_i,0 F=0 as well. The stress identity gives L_U(-1)F=0.
Choose v in F with pi(v)=1. Its vacuum-like module map U->E splits pi.
Every epimorphism onto U therefore splits: U is projective. This argument
does not assume L_U(0) was semisimple on F before taking the trace.

The category inputs are standard for C2-cofinite CFT-type VOAs: finite
abelian category, braided tensor products, and right exactness of tensoring.
Self-contragredience makes contragredient duality an r-category structure.
Precise references are collected in [McRae, Sections 2.2–3](https://arxiv.org/html/2108.01898),
which cites Huang for finiteness and HLZ3, Proposition 4.26, for right
exactness.

## 4. Why positivity alone does not settle nonzero generalized weights

The analogous diagonalizability assertion at positive weight would be false.
Set

    P+ = [[0,1, 1], [0,0,0], [0, 1,1]],
    P- = [[0,1,-1], [0,0,0], [0,-1,1]],
    Q  = diag(1,1,0).

These three matrices are idempotent. Each is diagonalizable with spectrum
contained in {0,1}, but

    P+ + P- + 2Q = 2I + 2E_12.

This sum commutes with all three matrices and is not diagonalizable.
Thus a positive central sum of individually diagonalizable operators with
nonnegative spectra can have a nonzero nilpotent part. The trace-zero
argument above avoids this problem; it must not be generalized silently.

## 5. Etingof–Penneys closes the remaining rigidity step

The audited source is [Etingof–Penneys, Theorem 1.1](https://arxiv.org/html/2412.17681).
The currently served version is arXiv v3, 27 July 2026, with manuscript date
24 August 2026. Its assumptions are Cauchy completeness, C-linearity,
braiding, finite-dimensional morphism spaces, and End(1)=C. An indecomposable
object is non-negligible when 1 is a direct summand of Y tensor X for some Y.
If also dim End(X^tensor n)<n! for some n, the theorem makes X rigid.
**Semisimplicity and prior tensor exactness are not hypotheses.**

Here is an independent proof of the required growth estimate. Choose a
projective generator P of the finite abelian category and set
d(M)=dim Hom(P,M). The evaluation map P^direct-sum-d(M)->M is surjective.
For fixed X, right exactness of F=X tensor - and exactness of Hom(P,-) give

    d(FM) <= d(FP) d(M).

Hence d(X^tensor n)<=d(1) d(FP)^n. Faithfulness of Hom(P,-) implies
dim End(M)<=d(M)^2. These bounds are exponential, so the required strict
factorial inequality eventually holds. No rigidity was used in this estimate.

For each nonzero indecomposable X, r-category duality gives a nonzero
evaluation DX tensor X -> 1. The unit is simple, so this map is an
epimorphism; the already proved projectivity of 1 makes it split. Thus X
is non-negligible. All hypotheses of Theorem 1.1 are now verified, so all
indecomposables are rigid. Finite direct sums give rigidity of the category.

Finally, in a rigid abelian tensor category, tensoring is exact and tensoring
a projective object with a rigid object preserves projectivity. Therefore
every object 1 tensor X is projective and every short exact sequence splits.
The category is semisimple, giving rationality of U. The familiar last step
is also stated as [McRae, Lemma 3.6](https://archive.ymsc.tsinghua.edu.cn/pacm_download/610/12057-Finite_Index_SS_Revised.pdf).

Together with the previously certified simplicity, CFT type, unitarity
(hence self-contragredience), and C2-cofiniteness, this yields strong
rationality. It does not use descent along finite branching, assume all
modules unitary, or assume ordinary-character S-transformation closure.
The earlier route through that S-transformation criterion is unnecessary
once this separate rigidity argument is supplied.
