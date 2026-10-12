# Host497: the hyperbolic residual and its later modular exclusion

15 September2026. Algebra and primary-source reading only; no numerical job.

**Later update.** The [joint flavoured-character argument](hi_cft_third_flavoured_host497_obstruction.md)
excludes host497, and the [universal modular theorem](hi_cft_third_flavoured_universal_obstruction.md)
excludes the entire nineteen-current character. The embedding and
saturation calculations below remain exact, but their arithmetic
survivors no longer represent unexcluded full-current hosts.

Host497 was not excluded by the initial categorical test here. Its residual differs from the excluded
[host614](hi_cft_third_e8_host614_commutant.md): after the actual alpha
projection it is a rank-one lattice times tricritical Potts, but its
possible order-nine metric is hyperbolic. The necessary arithmetic
condition below leaves a concrete class of cases. None supplies a VOA
action or an identification of the H3 chain without further construction.

## 1. The full-current embedding and its pre-radical commutant

The host is A3_1×A1_5 plus one radical current, with total current
central charge43/7. Use the regular D5_1×A3_1 embedding of E8_1.
Taking the full A3 affine vacuum leaves exactly D5_1. In standard
D5 coordinates e1,...,e5, split D3 on the first three coordinates and
D2 on the last two. Put

    t=e1+e2+e3,     v=2t,       v²=12,
    a=e4−e5,       b=e4+e5,    a²=b²=2.

The A2 in D3 has roots e1−e2,e2−e3. Its principal A1 has index four;
the diagonal of this A1 and the regular A1_a has level five. The
remaining A1_b and the t circle centralize it. Equivalently the D5
vector10 restricts to SU2_5 as3⊕3⊕2⊕2. Its connected orthogonal
centralizer is SO2×SU2, of rank two and dimension four, matching the
saved host497 centralizer. The constructed A1_5+A3_1 linear class
matches the catalog, and
[Minchenko's conjugacy criterion](https://pi.math.cornell.edu/~andreim/semsimC.pdf)
applies as for the neighbouring hosts.

Write T=Vir(6/7,0)⊕Vir(6/7,5), the tricritical-Potts VOA, and let
g be one of its order-three invertible modules of weight4/3. The
regular D3/A2 lattice glue has three sectors:

    V_D3=(A2_1(0)×V_Zv)
        ⊕(A2_1(3)×V_(Zv+v/3))
        ⊕(A2_1(3bar)×V_(Zv−v/3)).                     (1)

Here the two nonvacuum A2 branches become principal A1_4 label2.
Their diagonal A1_a,1×A1_4 / A1_5 vacuum multiplicities are the two
weight4/3 simple currents of T. The D5/D3×D2 nonvacuum glue has
D2 labels(1,1); its a label is odd, while every principal A1 label
from D3 is even. Thus the diagonal center forbids denominator vacuum
in that branch. Consequently the exact pre-radical commutant is

    C_pre=A1_b,1 × E,
    E= ⊕_(j in Z3) (V_(Zv+jv/3) × g^j).              (2)

The charges v/3 have lattice weight2/3, giving integral extension
weight2 together with g. Equation(2) is a local order-three
simple-current extension, so it is strongly rational. Its central
charge is20/7 and its weight-one algebra is A1_b plus one abelian
current. The tricritical-Potts module/fusion input is explicitly
listed in [Yamauchi, Theorems5.4.7–5.4.8](https://www.math.twcu.ac.jp/~yamauchi/math/phd/myphd.pdf).

Any one-dimensional radical can be conjugated by the connected
centralizer into the Cartan plane span(b,v). Its direction is rational
with respect to the charge lattice when the actual rational radical
lattice completion inside W is imposed. That rational-completion
premise is part of the standing E8 fixed-VOA framework.

## 2. Alpha removes the order-three extension

Pointwise fixing A3 makes alpha an element of the Spin10 centralizer:
the regular D5/A3 graph of centers absorbs the A3 lift, and Spin10
injects in E8. Thus an alpha of order three has an honest order-three
Spin10 representative, not an order-nine representative modulo center.

The centralizer of SU2_5 in SO10 is connected SO2×SU2. The SO2 acts
on the multiplicity space of the two real triplets; a reflection has
determinant minus one on their six-dimensional space and cannot be
paired with a determinant-minus-one transformation in the quaternionic
doublet centralizer. Its spin preimage is connected because a full
SO2 turn rotates three orthogonal planes. After conjugacy an
order-three element has D5 Cartan parameters

    (A,A,A,B,B)/3,       A,B in Z/3Z,                  (3)

with a lift chosen so that the triple of this vector lies in D5.
The E8 adjoint decomposition is

    (45,1)+(1,15)+(10,6)+(16,4)+(16bar,4bar).

Its exact fixed dimensions are

| A | B | fixed dimension |
|---|---|---:|
|0|0|248|
|0|nonzero|134|
|nonzero|0|86|
|nonzero|nonzero|80|

For example, the86 case consists of15 D5 centralizer currents,
15 A3 currents,24 vector-glue states and32 spinor-glue states. The
80 case has25+15+0+40; the134 case has19+15+36+64. These are direct
weight counts, using that all nonzero mod-three values differ only
by sign in the spinor sum. No numerical enumeration is needed.

The required E6+A2 fixed Lie algebra has dimension86. Hence A is
nonzero and B=0. Alpha is trivial on A1_b and on V_Zv, while it
multiplies the j=±1 sectors of(2) by nontrivial cube roots of unity.
It follows that

    (C_pre)^alpha=A1_b,1 × V_Zv × T.                  (4)

This is the actual distinction from host614: alpha is nontrivial on
the pre-radical extension, although it fixes every current.

## 3. All possible residual lattices and the order-nine test

Let the radical direction be r in span(b,v). Since A1_b,1=V_Zb,
the alpha-fixed pre-radical algebra has rank-two lattice

    Q=Zb⊕Zv,       Gram(Q)=diag(2,12).

For a rational radical direction, the primitive perpendicular lattice
is N=Z(pb+qv), where gcd(p,q)=1. Therefore

    D_B=Com(H,E8^alpha)=V_N × T,
    N has norm2m,       m=p²+6q².                     (5)

This specifies the actual commutant, rather than replacing it with
the full E8 commutant. The sign of p or q does not change m, but the
formula alone is not a classification of all simultaneous embeddings
of the full fixed VOA W.

The nonpointed tricritical-Potts factor is the rank-three category S
of the host614 proof. Its simple dimensions are1,u,u²−1 with
u=2cos(π/7). That proof shows elementarily that every connected
S-module graph is the regular T3. Hence, for any proper rank-two
Haagerup quotient on(5), the pointed group

    P=Z_(2m) × Z3

acts transitively on regular components. If a least object has
stabilizer size h, its dimension is sqrt(h)d. Frobenius reciprocity
fixes the neutral part of XX* to the h stabilizer invertibles, so the
remaining dimensions give

    integer combination of {1,u,u²−1} = 3sqrt(h).     (6)

The cubic field Q(u) contains no nontrivial square root of a rational
integer. Thus h is a square. Independence of1,u,u²−1 then eliminates
the two nontrivial S dimensions from every least-object product.
There is an actual closed pointed Haagerup quotient, so the previously
proved near-group reduction forces h=9. This reduction holds for
arbitrary m; it does not assume an upper bound on the lattice norm.

If3 does not divide p, then m=1 mod3 and |P| is not divisible by9,
which is impossible. If3 divides p, primitivity gives3 not dividing q,
and

    m=6 mod9.                                       (7)

The 3-primary part of P is then exactly C3². The lattice order-three
generator has weight m/9=2/3 modulo one; the Potts generator has
weight1/3 modulo one. Their metric is therefore

    q(a,b)=exp(2πi(2a²+b²)/3),                        (8)

which is hyperbolic. It matches, rather than contradicts, the unique
NG(C3²,9) central metric. There is no cyclic C9 alternative because
v3(m)=1. Thus the categorical test leaves precisely the directions
with3|p. The smallest example is p=0,q=1, giving V_sqrt12×T.

In precisely this surviving case, the full E8 commutant is also
explicit. Since N/3=(p/3)b+(q/3)v belongs to the charge lattice of(2),
one obtains

    D_E= ⊕_(j in Z3) (V_(N+jN/3) × g^(qj)).         (9)

Its nontrivial extension fields have integral conformal weight because
m/9+4/3 is integral when m=6 mod9. The extension has index three,
and alpha gives its nontrivial quantum C3 action, with fixed algebra
exactly D_B. Thus D_E and D_B are different even though their
central charges agree. The surviving case has a concrete strongly
rational ambient extension; the unknown step is its Haagerup fixed
subalgebra, not rationality of this ambient VOA.

The trivial-residual alternative D0=D_B is excluded by the cubic
dimension field just as in host614: the current SU2_5 dimensions and
all T dimensions lie in Q(u), while the lattices and A3 are pointed,
so a rational-frame index ratio cannot equal I=(13+3sqrt13)/2.
The universal restriction lemma consequently makes the remaining
case proper, under its finite rational/VOA-net hypotheses.

## 4. What this does and does not establish

The result is a complete necessary congruence reduction of the
rank-one residual lattice in this embedding:3|p and m=6 mod9. The
surviving metric is an actual allowable categorical case, so it must
not be deleted by importing host614's anisotropic argument.

The fixed-character targets for this nineteen-current branch are
W_2=198 and W_3=1307. No branching or character theorem in this note
forces the nonpointed S factor or a full ambient lattice into W.
The host0 simple-current parity proof cannot be transferred silently:
the present current algebra contains the nonpointed SU2_5 category.
A compatible local VOA action, its full E8 extension, and those
fixed-character constraints remain to be solved before this becomes
a construction or an exclusion.

For reference, if M is the actual rank-one radical lattice and
[Q:M⊕N]=r, its norm2a obeys a m=6r². Writing s=Dim(S), the exact
global dimensions are

    Dim(H)=16a s,   Dim(D_B)=6m s,   Dim(B)=9.

Hence [B:H×D_B]=8r s belongs to the cubic field F=Q(u). The rank-two
index equality gives [W:H×D0]=8r s as well. After the independently
derived [categorical factorization](hi_cft_third_host497_factor_audit.md)
Rep(D0)=S×R_H×P', positivity in F(sqrt13) therefore forbids nonvacuum
R_H labels in this extension. Here R_H is the actual centralizer of
the supplied order-nine lift in Z(NG(C3²,9)); only its dimension list
and unique invertible vacuum are needed, not an additional naming
of it as a particular Haagerup center.
This conclusion alone does not force a VOA realization of the S
factor inside D0, or force the entire ambient radical lattice into W.
In particular M is not assumed to be the primitive perpendicular
lattice. For p=0,q=1 that primitive lattice is Zb of norm two; retaining
it would add two unwanted weight-one root fields. The actual M must
instead be a proper sublattice, for example2Zb. Its multiplier is
included in r. This observation does not exclude N=Zv itself.

There is also no extra independent C3 exclusion from that neutral
selection. The tricritical-Potts charge is the principal SU3 triality,
already neutral in B=E8^alpha. On the residual lattice, the character
exp(2πi(pb+qv)_0/3) equals alpha^q on E8 because3|p; it too is
already trivial on B. Confusing either character with a new nontrivial
order-three action on B would produce a false index-divisibility
argument.

## 5. The saved proper-denominator witnesses in this host

Reading the already executed eleven-host catalogue shows exactly ten
remaining denominator rows supported by497 in the c-window[3/2,5/2].
There are only two resulting charges,13/7 and33/14; none lies near2.1.
The rows and levels are

| row | denominator currents | residual c |
|---:|---|---:|
|6|A1_5 + U1^4|13/7|
|99|A1_5 × A1_1 + U1^3|13/7|
|198|A1_5 × A1_4 + U1^2|13/7|
|286|A1_5 × A2_1 + U1^2|13/7|
|497|A1_5 × A3_1 + U1|13/7|
|894|A1_5 × A1_1² + U1^2|13/7|
|993|A1_5 × A1_2² + U1|13/7|
|143|A1_5 × A1_2 + U1^2|33/14|
|225|A1_5 × A1_10 + U1|33/14|
|344|A1_5 × B2_1 + U1|33/14|

These are saved necessary graph/rank witnesses. They are not ten
proved simultaneous embeddings of W. For any actual inclusion A⊂H
from the first seven rows, c(A)=c(H). Unitarity makes their Sugawara
stress tensors equal. The zero-H-energy space in any positive-energy
ambient H-module contains only its vacuum multiplicity. It follows
that Com(A,E8)=Com(H,E8), and likewise inside B and W. Thus these
seven actual conformal-current replacements do not produce different
commutants for a fixed full host and radical direction.

For the last three rows the relative H/A commutant has c=1/2 and is
Ising. Their A3 replacements are respectively A1_2 plus a commuting
Cartan, principal A1_10, and B2_1. The first uses the conformal
A1_2×A1_2 embedding of A3_1 and K(A1,2)=Ising. The other two use
SO5_1⊂SO6_1, with principal A1_10 conformally embedded in SO5_1;
the spinor and vector branches have no extra A1_10 vacuum. Hence
every such actual proper-current coset retains that relative Ising
stress. This does not assert a tensor-product full CFT: ambient glue
can still pair nonvacuum relative and residual modules.

The counts here are a readout of
[the root's immutable catalogue result](hi_cft_third_e8_filtered_grid_host11_results.json),
not a newly executed enumeration.

## 6. A concrete double-commutant saturation

The categorical graph algebra does force a specific larger current
commutant into W, without forcing the tricritical-Potts stress into D0.
Let

    C_W=Com(D0,W),       C_max=Com(D_B,B).

Since D0 has the same conformal vector as D_B, every vector of C_W
has zero D_B energy. Unitarity and the unique zero-energy vacuum in
the ordinary D_B decomposition of B imply C_W⊂C_max.

First compute C_max independently. In B=A2_1×E6_1, use the regular
conformal A1_a,1×A5_1 embedding of E6_1. Its nonvacuum glue is the
order-two pair of labels(1,3), whose weights are1/4 and3/4. The
diagonal GKO vacuum selection for the tricritical-Potts algebra gives

    Com(T,B)=(A1_5(0)×A5_1(0))
              ⊕(A1_5(5)×A5_1(3)).                   (10)

The second summand has weight5/4+3/4=2. In GKO labels the two zero-T
branches are(a,r,s)=(0,1,1) and(1,5,6), with the latter identified
with the same Virasoro vacuum. No other tricritical-Potts module has
zero energy. Thus(10) is the actual order-two simple-current
extension, not an inferred tensor factor from modular data.

Choose A5 coordinates with the A3 on the first four coordinates.
Then the primitive orthogonal Cartan lattice is exactly Q, with

    b=(0,0,0,0,1,−1),
    v=(1,1,1,1,−2,−2).

Its Gram matrix is diag(2,12), agreeing with the preceding embedding.
The primitive N generator has coordinates

    n=(q,q,q,q,p−2q,−p−2q).

Put K=n^perp∩A5 and δ=div_A5(n). Direct pairing with the A5 roots
gives

    δ=gcd(2p,3q−p),       det(K)=12m/δ².              (11)

For3|p and gcd(p,q)=1, δ is either three or six. The actual radical
lattice M and A3 form a finite-index sublattice of K. Using am=6r²,

    [K:A3⊕M]=sqrt(8a/det(K))=2δr/m.                 (12)

The A5 label-three module has zero-N-charge states precisely when
δ=3. Indeed its ground weights pair with n as ±p or±3q, and all
other weights change these values by δZ. If δ=3 they can reach zero.
If δ=6, write p=3k: then k,q are odd, so every pairing is3 modulo6.
There is no zero-charge vector in that case.

Therefore(10), after removing V_N, contributes one additional
order-two simple-current extension when δ=3 and no such extension
when δ=6. Both cases give the same exact index

    [C_max:H]=12r/m.                                 (13)

Now compare with the graph algebra from the
[independent factor proof](hi_cft_third_host497_factor_audit.md).
Its pointed part L is Lagrangian in A_H×P', with

    |A_H|=16a,       |P'|=2m/3,       |L|=8r.

Here A_H is the pointed factor of Rep(H), and all groups carry their
actual nondegenerate braidings. The equality D0=Com(H,W) makes the
projection L→A_H injective: a nonvacuum kernel summand, in the
unit-S graph component, would add a new H-vacuum D0-module to W.
Because L=L^perp, the annihilator of its image in P' is then trivial;
so its projection onto P' is surjective. Exactly the kernel of this
second projection has D0-vacuum label. Hence

    [C_W:H]=|ker(L→P')|=12r/m.                       (14)

The inclusion C_W⊂C_max and equal indices(13)–(14) prove

    C_W=C_max.                                      (15)

This is an actual subVOA-retention conclusion obtained from the
explicit ambient branching and index, not from identifying modular
factors with local stress tensors.

In particular V_K lies in W. Its A5 roots are differences of equal
coordinates of n. The first four coordinates always give A3. Extra
roots occur precisely if p=0 or p=±3q (q=0 was already excluded by
the order-nine condition). They respectively give A3+A1 or A4.
All these additional weight-one vectors contradict the prescribed
W1=A3+A1_5+U1. The simple-current term of(10) cannot compensate:
its A1_5 label-five energy alone is5/4, so it has no weight-one
vectors to remove or mix with them.

Thus m=6 (p=0,q=±1) and m=15 (p=±3,q=±1) are excluded. The first
remaining value is

    m=33,       (|p|,|q|)=(3,2),       N²=66.        (16)

Generic directions still have exactly the A3 roots in K, so(15)
does not exclude all of host497. It supplies a larger retained
rank-four lattice/current extension and a stronger explicit lower
norm bound for the remaining construction problem.
