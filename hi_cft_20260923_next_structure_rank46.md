# Rank-four or rank-six consequences of the sharp top bound

23 September 2026. Analytical work only. No numerical calculation was
launched by this agent. This note uses the newly accepted bound
0<=h<=17/10 for every simple U-module and the already proved strong
rationality. Properness is still an explicit hypothesis wherever stated.
The exact all-sector certificate
`hi_cft_20260923_next_81top_all.json` now proves the finite-top assertion
used below for all four mixed sectors; root launched the calculation.

## 1. The nine lattice sectors

Label the B=V(E6+A2) modules by (a,b) in Z3 x Z3. A nonzero E6 label
has lowest weight 2/3 and a 27-dimensional top; a nonzero A2 label has
lowest weight 1/3 and a three-dimensional top. Consequently:

| Lattice label | Initial weight | Initial dimension | Possible U top weights |
| --- | --- | --- | --- |
| (0,0) | 0 | 1 | 0,1 |
| (0,+), (0,-) | 1/3 | 3 | 1/3,4/3 |
| (+,0), (-,0) | 2/3 | 27 | 2/3,5/3 |
| Four labels with both entries nonzero | 1 | 81 | 1 only |

The last column follows from the actual lattice grading plus h<2, with
17/10 still allowing 5/3. Thus an irreducible action of certified U zero
modes on an 81-dimensional mixed-sector top proves that its entire U
restriction is simple. This inference is valid because there is no
possible later U top. For the three- and 27-dimensional sectors, initial
top irreducibility alone does not exclude new summands one grade later.

All four mixed-sector top actions have now passed exact irreducibility.
The certificate records 81-dimensional cyclic closures from a
one-dimensional simultaneous Cartan eigenspace, together with exact
positive-metric adjoint checks for the generating operators. The latter
checks make the generated associative algebra a star algebra. Hence a
proper invariant subspace would have an invariant orthogonal complement;
the unique Cartan eigenline lies in just one irreducible summand, and its
81-dimensional cyclic span leaves no other summand. This is stronger than
cyclicity alone. Source hashes and field/word provenance are in the JSON.
Thus the entire U restrictions of all four mixed B sectors are simple.

In the proper case, the known irreducibility of the complementary
80-dimensional current space gives B=U direct_sum X, with X simple,
lowest weight one, and dim X(0)=80. The alternatives are still U=B or
this proper case; the top bound does not choose between them.

## 2. The E8 branching and the rank identity

Let H=V(E8)=B direct_sum J direct_sum J^2 be the actual index-three
simple-current extension. Denote the two now-proved simple mixed-sector
restrictions by Y and Y'. Contragredient duality gives
Y'=Y*, but does not imply that they are distinct. In the proper case,

    H = 1 direct_sum X direct_sum Y direct_sum Y*.

Here 1, X and Y are pairwise nonisomorphic, since their ambient lowest
spaces have dimensions 1,80,81. Let s=FPdim_U(B). Positivity of categorical
dimensions and the extension dimension formula give

    d(X)=s-1,  d(Y)=d(Y*)=s,
    Dim Rep(U)=9 s^2,  Dim F=3s,  F=Rep(U)_H.

The mixed B modules have B-dimension one, hence U-dimension s. H is a
Lagrangian algebra, and the canonical center equivalence identifies
Rep(U) with Z(F) and H with I(1), where I is right adjoint to the
forgetful functor T:Z(F)->F. These are the Lagrangian-algebra conclusions
of [DMNO, Section 4](https://arxiv.org/html/1009.2117).

The rank formula requires only adjunction and the ordinary center
induction formula:

    dim End_Z(F)(I(1))
      = dim Hom_F(T I(1),1)
      = dim Hom_F(direct_sum_{a simple in F} a tensor a*,1)
      = # Irr(F).

Thus rank(F)=dim End_U(H), with no unproved branching assumption beyond
those explicitly made above. Semisimplicity computes this endomorphism
dimension as the sum of squared multiplicities. The only unresolved
hypothesis of this branching alternative is properness:

* If Y is self-dual, H=1 direct_sum X direct_sum 2Y, and rank(F)=6.
* If Y is not self-dual, the four summands are distinct, and rank(F)=4.

An exact intertwiner for a *subset* of top zero-mode operators does not
yet prove Y is self-dual: additional U fields can act differently.
Conversely, inequivalence under a certified subset already proves
inequivalence as U-modules. A full intertwiner or complete Zhu action
is needed for a positive isomorphism assertion.

## 3. What a rank-four reduction would leave

The canonical Lagrangian algebra automorphism group identifies with
the invertible objects of its boundary fusion category. For example,
this identification is stated in the proof of Theorem 1.3 of
[Jones--Schatz--Williamson](https://arxiv.org/html/2410.08884), through
the full-center/Picard correspondence. The actual order-three lattice
automorphisms of H fixing B therefore give a Z3 subgroup of Inv(F).
For a rank-four F there are exactly three invertibles and one
noninvertible object rho: a group of four invertibles cannot contain
an element of order three.

Therefore F has near-group fusion rules

    g rho = rho g = rho,
    rho^2 = 1 + g + g^2 + m rho,
    d(rho)^2 = 3 + m d(rho),
    3s = 3 + d(rho)^2.

The rank-four near-group restriction m in {0,2,3,6} is recorded in
[Dong et al., Theorem 6.2](https://doi.org/10.1016/j.jalgebra.2022.02.020),
using the rank-four classification. Use the published theorem here: the
older arXiv version states only m=2 or divisibility by three. The published
proof invokes Larson's rank-four classification to get the finite list.
Its possible indices are

| m | d(rho) | s |
| --- | --- | --- |
| 0 | sqrt(3) | 2 |
| 2 | 3 | 4 |
| 3 | (3+sqrt(21))/2 | (7+sqrt(21))/2 |
| 6 | 3+2sqrt(3) | 8+4sqrt(3) |

Section 7 below sharpens the rank-six alternative to a quadratic ring
with one still-undetermined integer multiplicity. Rank six does not
by itself determine the Haagerup index.

## 4. Excluding the m=0 rank-four alternative

Here s=2, so d(X)=1 and X is invertible. Since B=1 direct_sum X is a
connected extension, X has order two and multiplication respects its
Z2 grading. Acting as +1 on U and -1 on X is a nontrivial VOA
automorphism of B fixing U. This contradicts the previously established
triviality of Aut(B/U). Thus the m=0 alternative is excluded in the
proper case. The branching statements needed here are now established.

## 5. Excluding both m=2 categorifications using E8 traces

There are two categorifications of the Z3+2 near-group ring, not merely
Rep(A4). Nevertheless both are Morita equivalent to Vec_(A4)^omega:
[Etingof--Gelaki--Ostrik, Theorem 7.1 and Corollary 7.4](https://arxiv.org/html/math/0304194#S7)
construct the relevant pointed dual from the Frobenius group
V4 semidirect Z3=A4. This argument applies to fusion categories, without
an extra C*-structure hypothesis.

Here ribbon compatibility is essential. Strict positivity of every
nonvacuum U-module's lowest weight implies positive categorical
dimensions, so Rep(U) carries the canonical positive spherical/ribbon
structure of a pseudo-unitary category. The braided center equivalence
with Z(Vec_(A4)^omega) preserves that structure by uniqueness of the
positive spherical structure. Hence its electric Rep(A4) subcategory
really has twist one, not just symmetric braiding.

Consequently Rep(U) would contain the electric Rep(A4) Lagrangian
subcategory, whose regular function algebra gives a holomorphic
strongly rational conformal VOA extension H' of U via the
[VOA/algebra-object correspondence](https://arxiv.org/abs/1406.3420).
The right A4 translations of its regular function algebra induce a
faithful VOA automorphism action, with invariant object exactly 1 and
therefore fixed VOA U. Strict positivity of the nonvacuum lowest weights
ensures H' is of CFT type. No unitarity assumption on H' is needed here.
The holomorphic c=8 classification identifies H' with V(E8); see
[Dong--Mason, Theorem 1](https://msp.org/pjm/2004/213-2/pjm-v213-n2-p05-p.pdf).

But every A4 action on the complex Lie algebra E8 has at least sixteen
fixed currents. Here is a short independently checkable calculation.
The affine E8 marks are 1,2,2,3,3,4,4,5,6. Kac coordinates of order two
give fixed Lie algebras D8 or E7+A1, of dimensions 120 or136. Their
adjoint traces are respectively -8 and24. Order-three coordinates give
A8, E6+A2, D7+one-dimensional center, or E7+one-dimensional center,
of dimensions 80,86,92,134; their traces are -4,5,14,77. Exhaustiveness
for order three is immediate from the marks: either one mark-three
vertex is selected, or a mark-two vertex plus the affine mark-one
vertex. The nontrivial order-two list similarly uses one mark-two
vertex. The fixed algebras of the order-three constructions can also
be checked in [Elduque, Section 5 and its diagram table](https://ems.press/content/serial-article-files/38100).

In particular t2>=-8 and t3>=-4. The three involutions in A4 are
conjugate. Its eight order-three elements need not be in one A4
conjugacy class, but each has trace at least -4, which is sufficient.
Averaging the character gives

    dim(E8^A4) >= (248 + 3*(-8) + 8*(-4))/12 = 16.

This contradicts dim U1=6 in the proper case. Hence both m=2
categorifications are excluded. The argument needs no claim that the
pointwise centralizer of the particular K embedding is exactly Z3.

## 6. Remaining boundary

With properness and the categorical identifications above, the rank-four
alternative reduces to m=3 or6. The mixed-sector simplicity certificates
are now completed and no longer an outstanding hypothesis.
Their indices are different from the Haagerup target. No exclusion of
those two cases is claimed here. Neither ordinary top dimensions nor
the bound h<2 determines categorical dimensions. The current finite
calculations also do not prove properness or identify all U modules.

## 7. The rank-six fusion algebra and the quadratic ring

In the proper case, every VOA automorphism of H fixing U preserves
B=1 direct_sum X: X is the unique simple summand of H with an
80-dimensional top, while the other nonvacuum summands have top dimension
81. Its restriction to B belongs to Aut(B/U), which is trivial. Thus

    Aut(H/U)=Aut(H/B)=Z3.

Under the canonical Lagrangian automorphism correspondence above, this
gives Inv(F)=Z3 in either rank alternative. In particular, in rank six
there are exactly three noninvertible simple objects.

The algebra structure on End(H), not just its dimension, is useful.
[Bischoff--Jones, Corollary 3.4](https://arxiv.org/html/1909.02816)
identifies End_Z(F)(I(1)) with the complexified fusion ring as associative
algebras, with ordinary composition corresponding to fusion product.
It applies to spherical fusion categories and needs no C*-hypothesis.
Consequently, if Y is self-dual,

    K0(F) tensor C = C direct_sum C direct_sum M2(C).

This is noncommutative. Let a generate its order-three invertible group.
If the left action of a fixed all three noninvertible simples, duality
would make its right action trivial on them as well. Then a is central;
the two nontrivial character idempotents of C[Z3] split off two
one-dimensional summands. Their complementary ideal has dimension four
and admits the FPdim character. It therefore cannot be M2(C), the only
noncommutative semisimple algebra of dimension four. This contradicts
the displayed fusion algebra. Hence the left action is transitive.

The right action commutes with the free left cyclic action, and it is
free by duality. It is therefore either the same cycle or the inverse
cycle. The same cycle makes the ring generated by commuting a and rho,
so is excluded. Thus rho a=a^2 rho. Writing rho*=a^k rho, duality fixes
all three noninvertibles: on their indices it is translation by k, and
involutivity gives 2k=0 in Z3, so k=0. Frobenius reciprocity now gives

    rho^2 = 1 + m0 rho + m1 a rho + m2 a^2 rho.

Associativity of (rho^2)a=rho(rho a)=a rho^2 forces m0=m1=m2=m.
The case m=0 would make rho invertible and is impossible. Therefore

    a^3=1,  rho a=a^2 rho,
    rho^2=1+m(rho+a rho+a^2 rho),  m>=1.

Writing d=FPdim(rho), the dimension relations become

    d=(3m+sqrt(9m^2+4))/2,
    d^2=1+3md,  s=1+d^2.

For m=1 this is the Haagerup fusion ring and
s=(13+3 sqrt(13))/2. For m>=2 the index is at least
20+6 sqrt(10). No claim that m=1 follows just from categorifiability is
made: the verified low-rank classification of Liu--Palcoux--Ren assumes
multiplicity one. Schopieray's 2023 general two-orbit framework is not
a classification of these noncommutative rank-six rings at arbitrary m.

There is an additional associator constraint. The local B-module
category, followed by H-module formation, embeds fully faithfully as
(Rep(B))_H into F. Indeed H-linear maps automatically intertwine the
restricted B action. This fusion subcategory has dimension three and
is pointed. Rep(B) has metric group Z3 x Z3 with
q(a,b)=(2a^2+b^2)/3; H corresponds to a diagonal isotropic line. The
quadratic space is hyperbolic and this pointed boundary category is
Vec_(Z3), with trivial associator. Equivalently, either nonzero cyclic
order-three anomaly has order-nine twists in its center, absent here.
Thus the full pointed subcategory of F is untwisted Vec_(Z3), not merely
a group of three unspecified invertibles. This does not determine m.
