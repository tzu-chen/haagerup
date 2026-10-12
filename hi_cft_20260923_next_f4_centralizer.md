# The index-twelve F4 centralizer and its order-three fixed algebra

23 September 2026. Independent analytical and primary-source audit; no
numerical calculation. The compact centralizer of the index-twelve sl2
in F4 is S4. In particular, its nonidentity elements of order three
form one conjugacy class. This removes a finite-group ambiguity in the
neighbor construction. The application to the actual residual below
requires the stated transport and pointwise-fixing premises.

## Primary sources and the index convention

[Westaway, *Birational Induction of Nilpotent Orbit Covers in Exceptional
Types*, arXiv2312.01838v3, Section4.9](https://arxiv.org/html/2312.01838#S4.SS9)
works over C and gives the orbit F4(a3), component group S4, and weighted
Dynkin diagram0200, with the first two nodes long and the last two short.

[Penkov--Zuckerman, *Algebraic methods in the theory of generalized
Harish-Chandra modules*, Section3, immediately before TableB, printed
page8](https://math.constructor.university/penkov/papers/gen_hc_r_final.pdf)
states that the conjugacy class of an sl2 in F4 is determined by its
Dynkin index. Their normalization gives long roots squared length2.

Take simple roots

    e2-e3, e3-e4, e4, (e1-e2-e3-e4)/2.

The diagram0200 has h=(4,2,2,0). Since the standard sl2 Cartan has
squared norm2, the index is (h,h)/2=12. Consequently the unique
index-twelve embedding has nilpotent orbit F4(a3).

For an independent check, counting the roots ±ei±ej, ±ei and
(±e1±e2±e3±e4)/2 gives adjoint h-weight multiplicities

    weight0:12; weights+2,-2:12 each;
    weights+4,-4:6 each; weights+6,-6:2 each.

Thus, writing Vj for the sl2 representation of highest weight j,

    f4 restricted to sl2 = 6 V2 + 4 V4 + 2 V6.

This matches the embedding used in the neighboring-lattice argument.

## The finite group is the triple centralizer

There is no V0 in this decomposition. Hence the Lie algebra of the
centralizer of the full sl2 triple is zero. In characteristic zero,
the nilpotent centralizer decomposes as the centralizer of the triple
times its connected unipotent radical. It follows that the finite
triple centralizer is the entire component group, namely S4.

This statement must not be replaced by saying that the nilpotent
centralizer itself is finite. Its dimension is dim ker(ad e)=6+4+2=12;
its identity component is the twelve-dimensional unipotent radical.
For a compact triple, polar decomposition shows that every element
of its finite complex centralizer is compact: the positive factor
would supply a nonzero infinitesimal centralizer. Thus the compact
centralizer is the same S4.

Every order-three element of S4 is a three-cycle. There are eight such
elements and one conjugacy class; the four cyclic order-three
subgroups likewise form one conjugacy class. This assertion does not
say that all order-three elements of the ambient F4 are conjugate.

[Premet, *Nilpotent orbits in good characteristics and the
Kempf--Rousseau theory*, Section3.9 case(4), printed page21](https://eprints.maths.manchester.ac.uk/496/2/nilp.pdf)
gives an additional check. For F4(a3) its four nonidentity component
classes have orders4,3,2,2, with the order-three class corresponding
to the pseudo-Levi A2+tilde-A2. The paper explicitly compares this
description with the characteristic-zero classification.

## A standard representative and the all-weight fixed VOA

Inside F4 take the commuting root subsystems

    A2(long):  e1-e2, e2-e3;
    A2(short): e4, (e1+e2+e3-e4)/2.

The two affine levels inside F4 at level one are1 and2. Their
central charges2 and16/5 sum to26/5, the central charge of F4_1.
Positivity makes the inclusion A2_1 tensor A2_2 conformal.
The principal sl2 has index4 in either A2; hence the diagonal
principal sl2 has index4+8=12 in F4. A nontrivial central element
of order three in the long A2 factor centralizes this sl2 and
acts nontrivially on F4. This supplies a standard representative
of the unique order-three class in the finite centralizer.

The finite Lie branching is

    52 = (8,1) + (1,8) + (3,6bar) + (3bar,6),

up to independently conjugating the A2 conventions. It can also be
read directly from the displayed root subsystems. The central element
acts by1,1,zeta,zeta^-1 on the four summands.

The corresponding affine decomposition is exactly

    L_F4(1,0)
      = L_A2(1,0) tensor L_A2(2,0)
        + L_A2(1,Lambda1) tensor L_A2(2,2Lambda2)
        + L_A2(1,Lambda2) tensor L_A2(2,2Lambda1).

Here is an all-weight justification, rather than an inference from
weight one alone. The integrable A2_1 top weights are0,1/3,1/3.
At level two they are0,4/15,4/15,2/3,2/3,3/5. The only pairs with
integer total conformal weight have total0 or1: the vacuum pair,
or a level-one fundamental paired with a level-two6 or6bar.
The conformal tensor-product subVOA is regular, so its actual
ordinary summands have precisely these top weights, with no arbitrary
integer shifts. The ambient weight-zero and finite weight-one
branching therefore fix all multiplicities. They leave exactly the
three summands displayed above. The central element acts by a scalar
on each irreducible summand. Its two nonvacuum scalars are primitive
cube roots. Consequently, at every weight,

    (F4_1)^Z3 = A2_1 tensor A2_2.

## Conditional application to the actual residual

Suppose the already constructed neighbor identification transports
the actual core to the standard commuting affine pair A1_3,A1_13,
and transports the order-three action defining the original ambient
B so that it fixes this pair pointwise. The full commutant of A1_3
is F4_1 tensor A1_1, as proved in
[the independent neighbor audit](hi_cft_20260923_next_neighbor_independent_audit.md).
The second A1 is diagonal between the index-twelve F4 sl2 and
the external A1. A factor-preserving automorphism fixing it
pointwise has trivial action on the external A1 and centralizes
the index-twelve F4 sl2. If its F4 restriction is nontrivial of
order three, the S4 result identifies it with the representative
above, up to conjugation fixing the diagonal sl2.

For an automorphism g fixing a subVOA D pointwise,

    Com(D,V)^g = Com(D,V^g).

Thus, for Y=Com(A1_13,F4_1 tensor A1_1), the actual residual is

    Y^Z3 = Com(A1_13, A2_1 tensor A2_2 tensor A1_1).

This is an exact VOA identification once the transport premises and
the nontrivial order-three restriction are established. It does not
by itself prove rationality of this diagonal coset. It also does not
identify the physical c=2 rho-chain CFT.
