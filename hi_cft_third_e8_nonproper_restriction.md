# What the nonproper commutant restriction does and does not imply

This note records what follows from the restricted channel alone.
Its polynomial and index observations remain valid. The subsequent
[rank-two restriction lemma](hi_cft_third_e8_rank_two_restriction.md)
uses the additional finite rational current-frame decomposition to
prove that a nontrivial residual restriction is proper. Thus the
channel-level ambiguity here is no longer an open loophole in that
stronger setting. No general claim that extremality survives arbitrary
restriction is made.

Let the ambient proper two-element Haagerup operation on B be x, and
let H be fixed pointwise. Put
\[
 D=\operatorname{Com}(H,B),\quad D_0=\operatorname{Com}(H,W),\quad
 I=1+d^2=(13+3\sqrt{13})/2.
\]
Assume the compatible unitary-net/normal-expectation setup. Bimodularity
makes D invariant. The restricted map, again denoted x, obeys
\[
 x^2=d^{-2}\operatorname{id}+(1-d^{-2})x,\qquad
 E={\operatorname{id}+d^2x\over1+d^2}.
\]
Here E is the vacuum-preserving conditional expectation D→D0. In
particular its positivity gives the Pimsner–Popa estimate
\[
 J=[D:D_0]\le I.                                  \tag{1}
\]
This is an upper bound, not an equality statement.

## Exact canonical-hypergroup decomposition

For a finite-index conformal subnet, Bischoff constructs its canonical
proper hypergroup. Its vacuum expectation is the Haar combination, and
the D0-bimodular stochastic maps form the simplex spanned by the
canonical extreme operations. See
[Bischoff, Theorem1.3 and Proposition4.10](https://arxiv.org/pdf/1608.00253).
These statements concern conformal nets with the hypotheses in that
paper; formal VOA polynomial identities alone are not a substitute.

Write its operations as \(\phi_0=\operatorname{id},\phi_1,\ldots,\phi_r\),
with positive weights \(w_0=1,w_1,\ldots,w_r\), and
\(J=\sum_jw_j\). Then \(E=J^{-1}\sum_jw_j\phi_j\), so the restricted
ambient operation has the **unique** decomposition
\[
 x={I-J\over J(I-1)}\operatorname{id}
   +\sum_{j>0}{Iw_j\over J(I-1)}\phi_j.            \tag{2}
\]
The coefficients sum to one and are nonnegative precisely when \(J\le I\).

Consequences:

- If \(1<J<I\), the identity and every nonidentity canonical operation
  occur with positive coefficient. The restriction is not extreme.
- If \(J=I\), the identity coefficient vanishes. The restriction is
  extreme only when there is one nonidentity canonical operation.
  Equality of indices alone does not prove properness.
- Conversely, starting from any compatible finite-index inclusion with
  \(J\le I\), equation (2) defines a stochastic map with the same
  quadratic relation and the same fixed subnet. Thus that relation
  imposes no rank-two canonical-hypergroup conclusion.
- The case \(J=1\) gives x=id and is another nonfaithful restriction.

This sharpens the earlier convex finite-group counterexample: the
obstruction is not limited to ordinary orbifolds.

## What could force properness

If B were exactly a tensor product H⊗D, a map fixing H pointwise would
be \(\operatorname{id}_H\otimes x_D\). A nontrivial convex decomposition
of x_D would then lift to B, contradicting ambient extremality.
Thus properness would follow in that exact tensor-product setting.

The relevant E8 hosts are finite conformal extensions of an affine and
lattice frame times D. They contain charged intertwining fields beyond
that tensor product. A stochastic map of D need not extend across
those fields, and a convex decomposition need not lift. No proof of
such lifting has been established for hosts379 or600.

There is a related sufficient *index* condition: an appropriate
nondegenerate commuting square, including density of the linear span
WD in B and the compatible expectation, would identify the induced
standard modules and give J=I. The weaker fact that W and D generate B
as an algebra is not that condition. Even the stronger index equality
still needs the rank-two/extremality step identified above.

An eventual closure should therefore establish at least one concrete
additional fact: a CP-extension theorem across the actual affine
branching, a two-summand canonical endomorphism for D0⊂D, or an explicit
restriction-index and canonical-rank calculation. None is supplied by
the ambient polynomial or the existing low-grade character alone.

## Current impact on the E8 catalogue

The ordinary-fixed-subalgebra obstructions for hosts379 and600 remain
valid because they use rational branching and the ambient irrational
index directly. The proper-action fusion obstructions also remain
valid with their explicit premise. Their union leaves the possible
nongroup, nonproper restrictions described by (1)–(2).

The c=1-host exclusions and the rational-axis Griess obstruction do not
need properness and are unaffected by this issue. The determinant575
construction and its parity/weight-three deductions do use properness;
they should not be carried over to an arbitrary restriction.
