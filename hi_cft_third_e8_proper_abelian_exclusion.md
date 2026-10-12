# No proper all-current residual action for the abelian E8 host

## Result and exact scope

Under the stated unitary finite-index Haagerup E8 setup, the restricted
rank-two action on the all-current commutant of the six-dimensional
abelian weight-one host **cannot be proper**.

More explicitly, there is no configuration satisfying all of:

1. E=V_E8, B=E^alpha=V_E6 tensor V_A2, W contained in B, with
   [E:B]=3 and [B:W]=I=(13+3 sqrt(13))/2;
2. W1 is six-dimensional and abelian, and the fixed character starts
   1+6z+120z²+956z³;
3. the compatible unitary rational VOA/conformal-net realization and
   vacuum-preserving finite-index expectation used throughout the E8
   current-host argument;
4. the rank-two hypergroup action restricted to
   D_B=Com(W1,B) is proper.

No odd-determinant assumption, lattice-minimum assumption, or choice of
a short cocharacter in the complementary plane is needed. The subsequent
[rank-two restriction lemma](hi_cft_third_e8_rank_two_restriction.md)
derives condition4 from the proper ambient inclusion and the actual
rational current-frame commutant, unless the residual inclusion is
trivial. The trivial case is already excluded by the ordinary-fixed
dimension-field argument. Thus the combined result excludes this
abelian host even when restricted properness is not initially assumed.
The original proper-action proof below is preserved as a separate step.
This does not prove that the physical chain arises from an E8 coset or
determine its central charge.

The conclusion combines independently audited lattice, module-character
and OPE arguments. No new numerical job was run for this synthesis.

## 1. Properness forces saturation and a pointed extension

The [proper host0 capacity theorem](hi_cft_third_e8_host0_proper_constraints.md)
supplies primitive orthogonal lattices

\[
 K=E8\cap\mathfrak z,\qquad
 L=E8\cap\mathfrak z^\perp,\qquad
 \det K=\det L=q,
\]

where z is the six-current plane. It proves

\[
 V_K\subset W,\qquad K\text{ rootless},\qquad
 D_B=V_{L_B},\quad [L:L_B]=3.
\tag{1}
\]

Writing D0=Com(V_K,W), it also proves that

\[
 T=V_K\otimes D_0\subset W
\]

is a local simple-current extension with support group P of order q.
The distinction between Com(V_K,W) and Com(W1,W) causes no issue here:
inside E8 both commutants lie in the orthogonal lattice V_L, which
commutes with the whole V_K.

The categorical input is the independently audited
[pointed near-group factorization](hi_cft_third_pointed_neargroup_factorization.md),
including the actual central lifts. This is where properness enters.

## 2. The mod-three form is hyperbolic, and L_B has only norms divisible by six

The [mod-three lemma](hi_cft_third_e8_mod3_obstruction.md) gives

\[
 q\equiv2\pmod3.
\tag{2}
\]

Here is its additional norm consequence, with the main steps recalled.
In a Cartan of B containing z, represent alpha by h/3 with h²=6.
The A2-factor choice h=u+2v for simple roots u,v gives such a
representative directly. Alpha fixing V_K makes P_K(h)/3 an element
of K*. Since K is primitive and E8 is unimodular, E8 projects
surjectively onto K*. Choose x with this projection and put h'=h-3x.
Then h' lies in L, represents the same alpha, and (h')²=0 modulo3.

The nontrivial alpha action on V_L means h' modulo3 is a nonradical
isotropic vector in L/3L. A degenerate binary symmetric form over F3
has no such vector. Thus the form is nondegenerate hyperbolic, with
determinant2 modulo3, proving (2).

For a nonzero isotropic vector in this binary space,

\[
 (\overline{h'})^\perp=\mathbb F_3\,\overline{h'}.
\]

But L_B consists exactly of y in L with (h',y)=0 modulo3. Every
reduction of such a y is therefore isotropic. Hence

\[
 y^2\equiv0\pmod3,\qquad
 y^2\in6\mathbb Z\quad(y\in L_B).
\tag{3}
\]

The second statement uses evenness. Positive definiteness now makes
the minimum of L_B at least six automatically. Norm-two and norm-four
loopholes are absent under (1).

## 3. The aggregate nonvacuum character is even, including even-order cases

The projection of P onto the V_K module labels has trivial kernel.
Otherwise a nonidentity extension summand would have form
V_K tensor M for a nonvacuum simple D0 module M. Its vectors
1 tensor M commute with V_K and would lie in
Com(V_K,W)=D0, contradicting the irreducibility of D0's vacuum module.
A duplicate vacuum is also prohibited by connectedness. Since both
P and the discriminant group K*/K have order q, this projection is
in fact bijective.

Consider a nonidentity extension summand.

- If it is not self-contragredient, it pairs with a distinct dual
  summand. Their graded characters agree by the nondegenerate
  contragredient pairing.
- If it is self-contragredient, its nonzero V_K label is an order-two
  coset lambda+K. Every momentum in that coset pairs with its
  distinct negative. Zero momentum cannot occur in a nonzero coset.
  Thus its theta series, and its entire oscillator-dressed
  character, has even coefficients at every conformal grade.

Convolution with the D0 character preserves evenness. Fractional
individual conformal weights do not alter this integer-multiplicity
statement; the full local extension has integral weights. Therefore
all nonvacuum contributions to the character of W are even, for
every q, without an odd-order assumption.

For a rootless rank-six K, with N4,N6 its norm-four/six vector counts,

\[
 \dim(V_K)_2=27+N_4\equiv1\pmod2,\qquad
 \dim(V_K)_3=98+6N_4+N_6\equiv0\pmod2.
\]

Both shell counts are even. With D01=0 and the fixed W character,
we obtain

\[
 \dim D_{0,2}\text{ odd},\qquad
 \dim D_{0,3}\text{ even}.
\tag{4}
\]

## 4. The low-weight algebra forces a forbidden Heisenberg extension

By (3), the weight-two part of D_B has only derivative currents and
quadratic oscillators. Since D01=0, applying L1 removes the derivative
currents from D02. The latter is a unital Jordan subalgebra of the
three-dimensional real symmetric quadratic algebra. Its dimension
is1,2, or3.

Equation(4) leaves1 or3. Dimension3 contains a rational pair of
rank-one stresses and is excluded by the
[rational-axis full-index theorem](hi_cft_third_e8_griess_constraint.md).
Thus

\[
 D_{0,2}=\mathbb C\omega.
\tag{5}
\]

Equation(2) shows that the determinant squareclass is neither1 nor3:
integer squares are0 or1 modulo3, while three times a square is0.
At lattice minimum six, the norm-six shell then has at most two
nonorthogonal opposite pairs. Three pairs would be a hexagonal shell
and force squareclass3; orthogonal pairs would force squareclass1.

A Hermitian weight-three primary cannot contain any of these lattice
vertices. Their self-OPE gives a positive sum of at most two
nonorthogonal rank-one tensors, with nonzero traceless quadratic
part. The oscillator primaries have rotation types0 and plus/minus3,
so have zero matrix elements against a type2 traceless quadratic.
They cannot cancel that vertex contribution, which contradicts (5).

There remain three real oscillator primaries: one antisymmetric
bilinear and a harmonic cubic doublet. With (4), D0 contains one
or three genuine weight-three primaries.

- All three generate H²^C3, excluded by the finite-orbifold Fock
  argument in this determinant squareclass.
- A single mixed antisymmetric/harmonic primary is excluded by
  the exact cubic collinearity identity -96 a³b. The Hermitian
  phase a=i t is explicitly included.
- A pure antisymmetric primary generates H²^SO(2), excluded by
  the audited neutral-bilinear/compact-Galois argument.
- A pure harmonic primary generates Miura W3 at c=2. Generic
  orientations have only rank-one surviving charge support after
  the positive-quadratic test. A rational screening orientation
  has exact one-screening irreducible characters; every
  transverse isotypic block has a fixed nonzero relative-stress
  expectation. It too leaves only rank-one charge support.

All alternatives contradict finite-index strong rationality or (5).
The detailed proofs, precise primary sources, and independent audits
are in the
[low-weight calculation](hi_cft_third_e8_host0_lowweight.md),
[generic Miura proof](hi_cft_third_e8_miura_orientation.md),
[rational Miura proof](hi_cft_third_miura_rational_screening.md), and
[SO(2) proof](hi_cft_third_heisenberg_SO2_obstruction.md).
The OPE identity additionally passed the root agent's guarded exact
oscillator checker. Thus no configuration satisfying the initial
four hypotheses exists.

## What remains unresolved

An ambient proper Haagerup action can restrict to a nonextreme
stochastic operation on the commutant. The quadratic rank-two relation
alone does not restore properness; the
[nonproper restriction note](hi_cft_third_e8_nonproper_restriction.md)
gives the precise canonical-hypergroup decomposition and remaining gap.

The theorem therefore rules out the proposed proper residual
realization, not the entire E8 fixed-algebra program. In particular,
it must not be rephrased as an unconditional exclusion of c=2 or of
the Haagerup-chain continuum theory.
