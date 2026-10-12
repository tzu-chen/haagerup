# Host614: a lattice times tricritical Potts obstruction

15 September2026. Reading and algebra only; no numerical job.

Under the finite rational/unitary E8 Haagerup fixed-algebra hypotheses
of the [rank-two restriction lemma](hi_cft_third_e8_rank_two_restriction.md),
the full-current host614 is excluded. Its residual central charge is13/7.
This is an exclusion of a catalogued current host, not an identification
or exclusion of the physical chain at that central charge. Host497 also
supports13/7 and is not covered by this note.

## 1. Actual ambient commutant

The host is

    H=A2_1 × A2_1 × A1_5,       c(H)=43/7.

Use the regular A2^4 embedding in E8, whose lattice glue is the ternary
tetracode. The two full level-one A2 factors are the first two factors.
Taking their affine vacuum removes every nonzero glue word: the
tetracode has minimum support three, whereas such a word would have
support contained in the last two coordinates. The remaining ambient
VOA is therefore exactly A2_1 × A2_1.

The A1_5 projects to a regular A1 of index one in one factor and a
principal A1 of index four in the other. These are the only nonzero
A1 embedding indices in A2, and their sum five fixes this choice up to
exchange. This gives the catalog's A1_5+A2_1+A2_1 linear class; the
stored host614 has precisely those levels and one centralizing current.
The full1183-class saved table has exactly one factor list
A1_5+A2_1+A2_1, at database number614 (a direct multiline lookup of
the immutable factor metadata). Thus type and levels identify its
linear class in this particular case; they are not asserted to do so
for arbitrary E8 embeddings.
Matching the linear class gives the actual conjugacy class here by
[Minchenko, Corollary3](https://pi.math.cornell.edu/~andreim/semsimC.pdf);
the exceptional linear-versus-conjugacy case for a simple A2 is not
this semisimple A1+2A2 algebra.
The same regular A2^4 realization and conjugacy input are used in
[the host615 proof](hi_cft_third_e8_host615_commutant.md).

Let t=(1,1,-2) in the first remaining A2, so t²=6, perpendicular to
its regular A1 root. The elementary index-two lattice decomposition is

    V_A2 = (A1_1(0) × V_Zt)
         ⊕ (A1_1(1) × V_(Zt+t/2)).                       (1)

The second A2 has the conformal principal branching

    A2_1 = A1_4(0) ⊕ A1_4(4).                         (2)

An odd first A1 label in(1), combined with either even label in(2),
cannot contain the diagonal A1_5 vacuum: the diagonal SU2 center acts
as minus one. Thus the shifted lattice branch contributes nothing to
the commutant. The diagonal GKO coset in A1_1(0)×A1_4(0) is Vir_6/7;
the A1_4(4) branch contributes its weight-five simple current. Hence

    D_E=Com(H,E8_1)=V_Zt × T,
    T=Vir(6/7,0) ⊕ Vir(6/7,5).                         (3)

The GKO branch weight follows directly from the unitary minimal Kac
formula: (r,s)=(5,1) has h=((7r−6s)²−1)/168=5. This is the familiar
tricritical-Potts extension. Its rationality, nine modules and fusion
rules are stated explicitly in
[Yamauchi, Theorems5.4.7–5.4.8](https://www.math.twcu.ac.jp/~yamauchi/math/phd/myphd.pdf),
following Lam–Yamada and Lam–Lam–Yamauchi. In particular(3) is an actual
rational VOA identity, not just a central-charge match.

## 2. Every simultaneous alpha fixes D_E

The first two A2 Cartans put alpha inside their connected torus
centralizer, contained in the image of SU3^4. Pointwise fixing their
full A2 currents makes its first two SU3 lifts central. Fixing the
diagonal A1 pointwise makes the third and fourth components centralize
their respective SU2 images separately. A finite central quotient
does not permit a nonconstant commutator with this connected SU2.

The principal SU2 acts irreducibly on its fundamental3, so its SU3
centralizer is the center. The regular SU2 centralizer in the other
factor consists of diag(a,a,a^−2). Write the four lifts as

    (z1,z2,diag(a,a,a^−2),z4),

where the z_i are SU3 central elements. Since alpha³=1 in E8, their
cubes form an element of the tetracode central kernel. Only the third
coordinate could be nonidentity, and the kernel has no word of support
one. Consequently diag(a³,a³,a^−6)=1, so a³=1 and the third lift is
also central. This also rules out a hidden order-nine lift.

All four components therefore act trivially on the A2^4 vacuum VOA.
Equation(3) lies in that vacuum sector. Thus

    D_B=Com(H,E8^alpha)=D_E                            (4)

for every simultaneous alpha in the host class. Its order-three action
is not assumed to be a particular preselected representative.

## 3. A categorical obstruction with an elementary module-graph proof

Write y=N(1/7), x=N(5/7), and let g=N(4/3)^+ be an invertible
tricritical-Potts module. The cited fusion rules give

    g³=1,    y²=1+x,    xy=x+y,    x²=1+x+y.

The y,x twists are exp(2πi/7),exp(10πi/7), respectively, and g has
twist exp(2πi/3). Their nine products exhaust the simples. The pointed
C3 is nondegenerate and centralizes {1,y,x}, as can also be checked
from the listed conformal weights. Thus

    Rep(D_E) = S ⊠ P,
    S=PSU(2)_5^rev,       P=C6 × C3.                   (5)

Here S denotes the rank-three even-label SU2_5 category, not the
different even-level SO3 condensation used for host33. Put

    u=dim(y)=2cos(π/7),    dim(x)=u²−1.

The three numbers1,u,u²−1 are independent over Q, and

    p(u)=u³−u²−2u+1=0.                                (6)

The polynomial has no rational root and is irreducible. Let N be the
y fusion matrix on one connected component of any finite S-module
category. It is symmetric, nonnegative integral, and p(N)=0. The
positive categorical dimension vector gives its Perron root u<2.
Every entry is therefore zero or one. If its characteristic polynomial
is p^m, its number of vertices is3m, its number of loops is tr(N)=m,
and tr(N²)=5m gives2m ordinary edges. Connectedness demands at least
3m−1 ordinary edges, so m=1. The graph is a three-vertex path with one
loop. A middle loop has norm2; hence the loop is at an endpoint. This
is exactly the regular T3 graph. No classification of associators or
general ADE graph theorem is needed.

Suppose now that a proper rank-two Haagerup quotient acts on D_E.
Use the actual central inclusion and indecomposable complement module
from [Bischoff's construction](https://arxiv.org/abs/1608.00253), with

    d=(3+sqrt13)/2,       I=1+d².

The pointed group P permutes the regular S-components transitively.
The T3 graph has no nonidentity automorphism. If there are r components,
let h=18/r be the stabilizer size of a least-dimension object. The
squared Perron norm of the regular S-component is Dim(S), so all
complement dimensions are

    sqrt(h) d times {1,u,u²−1},       h divides18.      (7)

For h=2,3,6,18, sqrt(h) lies outside F(sqrt13), where F=Q(u) has
odd degree three. Indeed F contains no nontrivial quadratic subfield,
and adjoining sqrt13 cannot introduce sqrt2, sqrt3 or sqrt6: the
otherwise included biquadratic field would have degree four dividing
the total degree six. Comparing the two field components in a product
of complement simples first forbids any complement summand, then
contradicts the nonzero d coefficient of its squared dimension.
Therefore h is one or nine.

For products of two least objects, Frobenius reciprocity fixes the
neutral part to the h pointed stabilizer objects; no nontrivial S
object appears there. The remaining dimension is3h d, hence after
division by sqrt(h)d it is3sqrt(h). Linear independence of1,u,u²−1
forces every complement summand to be another least object. Thus P
and the least objects form an actual closed central fusion
subcategory. This is a consequence of the fusion coefficients, not
an assumed tensor splitting or a group grading.

The [pointed near-group reduction](hi_cft_third_pointed_neargroup_factorization.md)
forces h=9 and an actual NG(C3²,9) subcategory. There is only one order-nine
subgroup of P: its 3-primary part. For the lattice factor V_Zt, an
order-three discriminant generator is t/3 with conformal weight1/3;
the Potts invertible also has weight4/3=1/3 modulo one. Therefore the
quadratic form on that subgroup is

    q(a,b)=exp(2πi(a²+b²)/3),                           (8)

which is anisotropic. The unitary NG(C3²,9) central lift instead has
the hyperbolic metric, by Izumi's all-category theorem and Example12.13;
see the primary-source audit in
[the Potts-pair obstruction](hi_cft_third_potts_pair_hypergroup_obstruction.md).
They are inequivalent, also after reversing braiding. This excludes
the proper case.

## 4. Applying the restriction lemma

The nontrivial case of the universal restriction lemma forces exactly
the proper inclusion just excluded. If D0=D_B instead, the rational
full-conformal frame H×D_B has quantum dimensions in

    F=Q(2cos(π/7)),

because A2_1 and the residual lattice are pointed, A1_5 dimensions
are the integral Chebyshev polynomials [n] in2cos(π/7), and no other
denominator factor occurs. This field has odd degree three and does
not contain sqrt13. The actual finite
branching index ratio [B:W]=I would belong to that field, which is
impossible.

Thus host614 is excluded under the explicitly stated finite-rational
VOA/net bridge. There is no numerical fit or spectral-fingerprint
assumption in the argument. Host497 and all other catalog witnesses
must be assessed separately before deleting the charge13/7 itself.
