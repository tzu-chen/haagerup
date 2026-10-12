# A necessary rational screening direction for the Miura branch

This is an analytical restriction on a unitary finite-index subVOA of a
binary lattice VOA. It is not an identification of the H3 chain. It closes
the generic orientation part of the remaining Miura branch in the
[determinant-575 low-weight argument](hi_cft_third_e8_host0_lowweight.md).
The rational screening case is handled in the separate proof by the uniform
agent. No numerical calculation is used here.

## Statement

Let L be a positive-definite even rank-two lattice with no norm-two or
norm-four vectors. Suppose its determinant has rational squareclass different
from 1 and 3. Let U be a unitary full-conformal subVOA of V_L such that

\[
 U_1=0,\qquad U_2=\mathbb C\omega,
 \qquad W_3(c=2)\subset U.
\]

The displayed W3 is the pure harmonic Miura algebra in the two Heisenberg
currents. It determines a root system of type A2 with root lengths squared
two. If U is strongly rational and has finite index in V_L, then at least
one of these A2 roots belongs to the rational plane L tensor Q.

The finite-index rational hypothesis is used only in the final character
comparison. The argument does not assume that U retains either individual
Heisenberg current or any individual c=1 stress tensor.

## 1. Generic Fock modules cannot mix with degenerate Fock modules

Write F_p for the two-boson Fock module of real momentum p. Call p generic
when (p,alpha) is not an integer for every A2 root alpha. At zero background
charge, the Fock determinant gives irreducibility of F_p as a W3 module;
its character is

\[
 \operatorname{ch}F_p(q)
   =q^{(p,p)/2-1/12}/\prod_{n\ge1}(1-q^n)^2.
\]

Here and below the common vacuum monomial may be omitted when comparing
ratios. The determinant statement and unitary complete reducibility are
[Bouwknegt--McCarthy--Pilch, Corollary 2.28 and Theorem 2.31(i), pp27--28](https://arxiv.org/pdf/hep-th/9509119).
The explicit integral-weight decomposition in Theorem 2.31(ii) is not
being extrapolated to arbitrary real momenta.

If q is nongeneric, select an A2 root alpha for which (q,alpha)=m is an
integer. Along this root the c=1 Fock representation decomposes as

\[
 F_{m/\sqrt2}^{(1)}
  =\bigoplus_{j\ge |m|,\ j\equiv m\ (2)}
       L(1,j^2/4).
\]

The c=1 irreducible character is
\(q^{j^2/4}(1-q^{j+1})/\prod(1-q^n)\). These are the N=2 case of the
commensurate-exponent character and Fock decomposition in
[Frenkel--Kac--Radul--Wang, Proposition 2.1, (2.5), and Sections 5--6](https://arxiv.org/pdf/hep-th/9405121).
Their specialized grading differs from physical L0 by a constant on a
fixed total-charge module; it changes only the leading monomial, not the
relative character or the factor 1-q^(j+1).

The Miura W3 lies in the product of this root Virasoro algebra and the
perpendicular Heisenberg algebra. This is the one-screening inclusion:
W3 is in the kernel of the root screening, whose zero-charge root factor
is L(1,0). Thus F_q is a direct sum of W3-invariant spaces

\[
 L(1,j^2/4)\otimes F_{q_\perp}^{(1)}.
\]

Every displayed summand has character, up to its leading monomial,
\((1-q^{j+1})/\prod(1-q^n)^2\). It cannot contain a generic simple F_p:
an injection would imply a coefficientwise character inequality, whereas
the ratio of this character to that of F_p tends to zero as q tends to
one from below. Any map into the algebraic direct sum has a nonzero
projection into at least one summand. Therefore a generic F_p never
occurs inside a nongeneric F_q.

This comparison does not require irreducibility of the displayed tensor
summands. That stronger fact is used only in the separate rational-root
proof.

## 2. A generic isotypic block regenerates a forbidden quadratic

For generic momenta, the W3 highest weights are the degree-two and
degree-three Weyl invariants. Thus two generic Fock restrictions are
isomorphic precisely when their momenta are in the same A2 Weyl orbit.
The lattice decomposition is semisimple over the unitary W3 algebra.
By Section 1, its generic isotypic blocks contain only these Fock modules,
with no additional copies hidden among nongeneric momenta.

A Weyl orbit meets L in at most two nonzero points. Indeed, among any
three distinct orbit points two differ by a 120-degree rotation. If p
and its rotation both lie in L, their rank-two Gram determinant is
3(p,p)^2/4, forcing determinant squareclass 3. If there are two orbit
points, they have equal norms. They cannot be orthogonal: that would
force determinant squareclass 1.

Consequently a nonzero generic U submodule contains a lowest vector

\[
 v=\sum_{p\in\mathcal O\cap L}c_p e^p,
\]

with at most two nonzero coefficients and with nonorthogonal momenta in
the two-point case. The weight-two coefficient in its OPE with its
unitary conjugate has quadratic-current projection

\[
 \frac12\sum_p |c_p|^2 p(-1)^2\mathbf1.
\]

There is no charged weight-two state because L has no norm-two or
norm-four vectors. Derivative-current terms have a different oscillator
degree and cannot cancel the traceless quadratic projection. A positive
sum of one rank-one tensor, or two nonorthogonal equal-length rank-one
tensors, is not a multiple of the rank-two metric. Its traceless part
therefore contradicts U2=C omega. No generic isotypic component can
occur in U.

## 3. Without a rational screening direction, too few charges remain

It follows that every nonzero charge in U lies in

\[
 \bigcup_{\alpha\in\Delta_+}L_\alpha,
 \qquad L_\alpha=\{p\in L:(p,\alpha)\in\mathbb Z\}.
\]

If L_alpha has rank two, its integer pairings with a full-rank sublattice
place alpha in its dual rational plane, which is L tensor Q. Therefore
if no A2 root is rational, each L_alpha has rank at most one.

Overcount U by the full oscillator Fock modules on this finite union.
For q=exp(-t), its numerator is at most a finite sum of rank-one theta
series, of order O(t^(-1/2)); the rank-two theta numerator of V_L has
order t^(-1). The common two-boson oscillator denominator cancels, giving

\[
 0\le \operatorname{ch}U(e^{-t})/
          \operatorname{ch}V_L(e^{-t})=O(\sqrt t)\longrightarrow0.
\]

A finite rational unitary extension has a positive finite quantum
dimension, and hence a positive character ratio in this limit. This
contradiction proves the stated necessary rational root.

## Scope and independent audit

The generic-versus-degenerate character separation was independently
checked by the uniform agent. The root agent independently checked the
FKRW character formula and its grading convention. The remaining
rational-root case has a stronger one-screening irreducibility argument;
it must be combined with this note before excluding the determinant-575
candidate. Neither statement is a classification of all rank-two lattice
subalgebras or of all possible E8 Haagerup actions.
