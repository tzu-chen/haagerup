# Odd-determinant proper abelian hosts require hexagonal squareclass

This intermediate theorem has been strengthened by the
[complete proper abelian exclusion](hi_cft_third_e8_proper_abelian_exclusion.md),
which removes the oddness and minimum assumptions. The argument below
is preserved because it gives the independent low-weight component of
that final proof.

## Precise necessary condition

Assume the unitary finite-index E8 fixed-algebra setup of the
[proper host0 capacity theorem](hi_cft_third_e8_host0_proper_constraints.md):

- E=V_E8, W contained in B=E^alpha, with indices [E:B]=3 and
  [B:W]=I=(13+3 sqrt(13))/2;
- W1 is six-dimensional and abelian, and its fixed character begins
  1+6z+120z²+956z³;
- the rank-two restricted quotient on the commutant is proper, with the
  stated compatible unitary expectation and rational VOA/net bridge;
- q=det(K)=det(L_E) is odd;
- the actual B commutant D_B=V_(L_B) has no norm-two or norm-four lattice
  vectors, equivalently its lattice minimum is at least six.

Then

\[
 \boxed{q=3s^2\quad\text{for an odd positive integer }s.}
\tag{1}
\]

This is a necessary condition, not a construction. It does not cover even
determinants, norm-two/four commutants, or nonproper restrictions. In
particular it does not exclude every abelian E8 host.

## 1. Capacity saturation supplies the odd extension and rootless K

The capacity theorem gives [L_E:L_B]=3, V_K contained in W, rootless K,
and a pointed local extension

\[
 T=V_K\otimes D_0\subset W
\]

of order q, where D0=Com(W1,W). Thus det(L_B)=9q and D01=0.
Since the extension group has odd order, every nonidentity simple-current
summand is paired with a distinct contragredient summand. Their characters
agree grade by grade, so their aggregate contribution to each integral
weight is even.

Let N4,N6 count vectors of squared lengths four and six in K. Both are
even, by pairing v with -v. The elementary rank-six oscillator partition
coefficients give

\[
 \dim(V_K)_1=6,\quad
 \dim(V_K)_2=27+N_4\equiv1\pmod2,
\]
\[
 \dim(V_K)_3=98+6N_4+N_6\equiv0\pmod2.
\]

Consequently the specified coefficients of W imply

\[
 \dim D_{0,2}\text{ odd},\qquad
 \dim D_{0,3}\text{ even}.
\tag{2}
\]

The minimum hypothesis puts D02 inside the three-dimensional quadratic
Heisenberg Jordan algebra. Dimension three contains a rational pair of
rank-one stresses and is excluded by the
[rational-axis full-index argument](hi_cft_third_e8_griess_constraint.md).
This step uses its compatible-expectation and c=1 classification
hypotheses, not a general subfactor join inequality. Therefore

\[
 D_{0,2}=\mathbb C\omega,\qquad \dim D_{0,3}\ge2.
\tag{3}
\]

## 2. Minimal-shell geometry removes every weight-three vertex

Suppose, for contradiction, that det(L_B) has squareclass different from
1 and 3. If norm-six vectors occur, they are minimal vectors. Two
consecutive minimal directions have angle at least sixty degrees:
otherwise the difference of their equal-length vectors is shorter.
There are therefore at most three opposite pairs in the norm-six shell.
If there are three pairs, all six cyclic angles equal sixty degrees,
and the lattice determinant has squareclass3. If two pairs are
orthogonal, their Gram determinant is a square, forcing squareclass1.

Thus under the contradictory squareclass assumption there are at most
two nonorthogonal norm-six axes. The case with no norm-six vector is
included. The oscillator weight-three Virasoro primaries consist of an
antisymmetric bilinear (rotation type0) and a harmonic cubic doublet
(types plus/minus3). Every matrix element of a traceless weight-two
quadratic between these oscillator primaries is zero, by rotation
types: a type2 operator cannot connect any of those angular charges.

For a Hermitian weight-three primary with vertex components, the
traceless quadratic part of its self-OPE is therefore the traceless part
of a positive sum

\[
 \sum_{p\in L_B,\ p^2=6} w_p\,p\otimes p,
 \qquad w_p\ge0.
\]

A positive sum supported on one axis, or two nonorthogonal equal-length
axes, cannot be isotropic. Hence a nonzero vertex component regenerates
a traceless quadratic, contradicting (3). All genuine weight-three
primaries of D0 are pure oscillator states. There are three available,
and (2) now leaves exactly one or three.

## 3. Both oscillator possibilities contradict finite-index rationality

If all three primaries occur, they generate H(2)^C3. The finite-orbifold
Fock theorem and det-squareclass assumption exclude a finite-index
current-free extension containing this algebra: a nonzero C3 Fock
orbit meets L_B once, so its inclusion forces a current. See the
[source-verified proof](hi_cft_third_heisenberg_c3_basechange_audit.md)
and the explicit generators in
[Lian--Linshaw Section13](https://arxiv.org/pdf/2107.03243).

If exactly one primary occurs, its mixed antisymmetric/harmonic
direction is excluded by the exact oscillator identity

\[
 bF_A-aF_B=-96a^3b.
\]

The algebraic proof and the independently executed rational-arithmetic
check are in the
[weight-three analysis](hi_cft_third_e8_host0_lowweight.md).
The identity is polynomial and remains valid with the required
Hermitian phase a=i t. The pure antisymmetric direction generates
H(2)^SO(2) and is excluded by the
[compact/finite Fock argument](hi_cft_third_heisenberg_SO2_obstruction.md).

The pure harmonic direction generates W3 at c=2. If no Miura root lies
in the rational lattice plane, the
[generic-orientation theorem](hi_cft_third_e8_miura_orientation.md)
leaves only rank-one charge support and gives a zero character ratio.
If a norm-two root is rational, let Delta denote the positive squarefree
representative of det(L_B). The rational plane has coordinates

\[
 (a,b)\in\mathbb Q/\sqrt2\ \times\sqrt{2\Delta}\,\mathbb Q.
\]

The one-screening irreducible character is supplied by FKRW. The other
Weyl transformations involve sqrt(3 Delta), which is irrational because
Delta is not3. Thus all transverse isotypic copies have the same
relative-stress expectation

\[
 j^2/4-\Delta r^2\ne0
\]

because Delta is not1. Fully degenerate zero-transverse copies have
A2-weight-lattice coordinates and cannot mix into them, by the same
sqrt(3 Delta) arithmetic. The expectation regenerates a forbidden
quadratic, and the remaining rank-one support again gives zero
character ratio. This is the general form of the
[rational-screening proof](hi_cft_third_miura_rational_screening.md),
which uses the primary
[FKRW character theorem](https://arxiv.org/pdf/hep-th/9405121).

Every oscillator possibility is exhausted. Therefore det(L_B), and
hence q, must have squareclass1 or3.

## 4. Odd even-lattice determinants cannot have squareclass one

Write the even binary Gram matrix as [[2a,b],[b,2c]]. If its determinant
q is odd, b is odd and q=4ac-b² is 3 modulo4. An odd integer of squareclass
one is an odd square, which is1 modulo4. Thus squareclass one is impossible.
The remaining option is q=3s², with s odd, proving (1).

For the executed determinant575 lattice, q=25·23 violates (1). Its
proper-action construction is therefore excluded by this theorem as
well as by the detailed candidate-specific proof. The exact lattice and
low-grade certificates remain valid; the obstruction arises from the
additional finite-index module and OPE constraints.

## 5. Corollary for the entire norm-six cocharacter family

Suppose, in addition, that the order-three action is represented by
alpha=exp(2 pi i h0/3) with h in L_E and h²=6. Such an h is primitive:
if h=m v with m>1, the positive even norm v² would imply h²>=8.
Extend h to a lattice basis (h,k), and put a=(h,k).

Capacity already forces the alpha action on V_(L_E) to be nontrivial.
Since (h,h)=6 is divisible by3, nontriviality means a is not divisible
by3. The determinant therefore satisfies

\[
 q=6k^2-a^2\equiv2\pmod3.
\]

This contradicts (1). Hence the entire primitive rank-two-plane family
containing a norm-six representative of alpha is excluded whenever q
is odd and L_B has minimum at least six, under the other theorem
hypotheses. This includes more than the determinant575 example.

The corollary is not universal: alpha being trivial on K only places an
appropriate cocharacter in the complementary rational plane. It does
not prove that a globally shortest norm-six representative can be
chosen in that plane. Even q and shorter L_B remain outside this
corollary as well.

## 6. Every surviving odd/minimum-six case has a lone Miura primary

The exceptional hexagonal norm-six shell can also be removed in this
proper setup. Three opposite norm-six pairs contain the lattice
sqrt(3) A2 of determinant27. Its index inside the even lattice L_B
is1 or3, since the squared index divides27. Index3 would give
det(L_B)=3 and hence a norm-two vector: Minkowski's rank-two ball
bound already supplies a nonzero vector of norm squared below four.
That violates the minimum assumption. Thus a three-pair shell would
force det(L_B)=27 and q=3.

But a rootless even rank-six lattice K cannot have determinant3.
Its covolume would be sqrt(3). The radius-two ball has volume
64 pi³/6, strictly greater than 2^6 sqrt(3). A slightly smaller
ball still satisfies Minkowski's convex-body inequality and contains
a nonzero K vector of norm squared less than four. Positive evenness
then makes that norm squared two, a contradiction. No sharp Hermite
constant or lattice classification is needed.

Therefore even in the surviving squareclass3 case there are at most
two nonorthogonal norm-six axes. The vertex positivity argument of
Section2 still applies, leaving one or three oscillator primaries.
The independently audited
[rotation-core theorem](hi_cft_third_e8_rotation_core_obstruction.md)
now excludes both H²^C3 and H²^SO(2) for every binary lattice using the
full E8 index; it does not require properness or a squareclass
restriction at that step. The exact mixed-primary identity still
applies unchanged.

Thus under the hypotheses of this note every surviving construction
must have q=3s²>3, D02=C omega and dim(D03)=2. Its unique genuine
weight-three field generates a pure harmonic Miura W3 algebra at c=2.
Classifying the finite-index extensions of that Miura algebra in the
remaining squareclass3 lattices is still required; this final condition
is not an exclusion of those cases.

The shell geometry and all module-theoretic steps have been independently
reviewed by the root and uniform agents in their respective component
proofs. This synthesis keeps the properness, odd-order, minimum, and
fixed-character prerequisites explicit.
