# The two retained current pairs inside E6_1 times A2_1

This note gives explicit standard embeddings for catalog125, with
A1 levels(1,39), and187, with levels(3,13). It also gives exact finite
representations of the ambient weight-one and weight-two spaces.
Those formulas supply independent checks and upper multiplicities for
the quartic current test. Section1 also fixes their placements inside
B from the current trace and weighted Dynkin diagrams. Every commutant
and low-grade count below is taken in B, not in the larger E8 VOA.
The formulas do not by themselves exclude either current pair.

The setting is the additional E8 construction with B=E6_1 times A2_1,
W contained in B and B as a W-module equal to0 plus b. Thus B_1 has
dimension86, W_1 dimension6 and the b ground dimension80. The saved
[E8 catalog](hi_cft_sixhour_e8_subalgebra_results.json) records125 and187
with exact Lie-centralizer dimension zero. Their full-current residual
charges are170/41 and18/5. The
[joint catalog intersection](hi_cft_third_e8_joint_intersection_results.json)
retains these actual host numbers.

## 1. Factor indices are fixed by the ambient trace

For either A1 factor let its total level be k, and let a be its
ordinary Dynkin index on the three-dimensional c1 ground. The exact
gamma0 trace table gives

    Tr_(B1)(H/sqrt2)^2 = 4+t_b = 24k-18a.

If k_E,k_A are its nonnegative integral embedding indices into E6
and A2, then k=k_E+k_A and the same adjoint trace is24k_E+6k_A.
Consequently

    k_A=a,  k_E=k-a.                              (1)

The surviving small-ground witnesses have a=(0,4). Thus the first
A1 is wholly in E6; the second has principal index4 in the external
A2 and E6 index35 or9. This is stronger than matching only the total
E8 levels.

There is no remaining placement ambiguity inside B. For index1 in E6,
the A1 coroot has squared norm2 and belongs to the unique root orbit.
For index3 it has squared norm6. By the weighted-Dynkin-diagram
classification its dominant simple-root values are in{0,1,2}; the
diagram determines its A1 conjugacy class. In Bourbaki order the E6
inverse Cartan matrix is one third of

    [4,3, 5, 6, 4,2]
    [3,6, 6, 9, 6,3]
    [5,6,10,12, 8,4]
    [6,9,12,18,12,6]
    [4,6, 8,12,10,5]
    [2,3, 4, 6, 5,4].

Its only nonnegative integral label vector of squared norm6 is e4.
Indeed the single-label norms are4/3,2,10/3,6,10/3,4/3; the only
other vectors of norm at most6 are twice a leaf, the two opposite
leaves, or the adjoint node plus either leaf, with norms16/3,4,16/3.
All entries are positive, so every other support or larger coefficient
has larger norm. The existing short A1 of G2 realizes e4, proving
uniqueness. This is the3A1 nilpotent class; see the weighted-diagram
framework and Table7 in
[de Graaf, Computations with nilpotent orbits in SLA](https://citeseerx.ist.psu.edu/document?doi=dcb9430e36f22b0c2069ad49fb123c806575e1e5&repid=rep1&type=pdf).

Its connected centralizer is A1_1 times A2_2, as the explicit adjoint
branching below confirms. An additional commuting A1 of E6 index9
must use index1 from the first factor and principal index8 from the
second: the possible second-factor contributions are0,2,8. At
host125, the analogous index35 in A5 is uniquely principal. Equation(1)
also fixes the external principal A1_4. Conjugacy inside these connected
centralizers therefore fixes the entire pair inside B. This argument
does not identify or require the larger E8 commutant.

## 2. Host125: root A1 and the principal A1 of A5

The index-one A1 in E6 is a root A1, with centralizer A5. The conformal
embedding A1_1 times A5_1 in E6_1 is the index-two root-lattice glue,
with vacuum decomposition(0,0) plus(1,lambda3). In particular

    Com(A1_1,B)=A5_1 times A2_1.                  (2)

An A1 index35 in A5 is its principal embedding: the defining6 is
irreducible and its index is35, the maximal index among partitions
of6. The second current factor is diagonal across this A1_35 and
the principal A1_4 in the external A2. Hence the residual commutant
in this placement is exactly

    Com(A1_39^diag,A5_1 times A2_1).              (3)

The finite E6 branching is78=(3,1)+(1,35)+(2,20). Under the principal
A1 of A5,35 becomes3+5+7+9+11, while20=Lambda^3(6) becomes10+6+4.
The external A2 adjoint becomes3+5. Removing the two W current
adjoints gives the following exact b ground; pairs denote dimensions
of the two A1 irreducibles:

    b_125=(1,3)+2(1,5)+(1,7)+(1,9)+(1,11)
              +(2,4)+(2,6)+(2,10).               (4)

Its two second traces, mixed trace and same-axis fourth traces are

    (20,860), 210, (10,22186).                   (5)

All five agree with the independent executed Jacobi predictions.
Thus these ambient weight-one data give a consistency check rather
than a new obstruction.

## 3. Host187: G2_1 times A2_2 and a diagonal A1

The conformal embedding G2_1 times A2_2 in E6_1 is in
[Adamovic--Kac--Moseneder--Papi--Perse, Section5, equation5.1](https://arxiv.org/html/1702.06089#S5.E1).
Their equation5.9 supplies the finite complement7 times8:

    78=(14,1)+(1,8)+(7,8).

Use the conformal A1_3 times A1_1 inside G2_1. Its finite branchings
are14=(3,1)+(1,3)+(4,2) and7=(3,1)+(2,2). Inside A2_2 take the
principal A1_8. Diagonalizing the internal A1_1 with it gives E6
index9; including the principal A1_4 of the external A2 gives13.
This explicitly realizes the catalog's level pair(3,13).

The affine G2 vacuum branches into labels(0,0) and(3,1), and its
7-module into(2,0) and(1,1), with labels referring to A1_3,A1_1.
The E6 vacuum extension over G2_1 times A2_2 has only the vacuum
and(7,adjoint) summands. Selecting the full A1_3 affine vacuum
therefore gives exactly

    Com(A1_3,B)=A1_1 times A2_2 times A2_1,
    D_B,187=Com(A1_13^diag,A1_1 times A2_2 times A2_1).  (6)

The finite b ground in this placement is

    b_187=2(1,3)+2(1,5)+(4,2)+(3,3)+(3,5)
              +(2,2)+2(2,4)+(2,6).               (7)

Its five current moments are

    (68,236), 162, (154,1594).                   (8)

These again agree exactly with the independent Jacobi predictions.
The two standard embeddings have the catalog type and levels, and
there is only one saved E8 linear class for each pair. Minchenko's
[Corollary3](https://pi.math.cornell.edu/~andreim/semsimC.pdf) turns
these matched non-A2 linear classes into inner E8 conjugacy classes.
This catalog match alone would not identify every compatible ambient
alpha action. The separate index/weighted-diagram argument in Section1
is what fixes the actual placement inside B used here.

## 4. Exact ambient weight-two upper multiplicities

At level one, the E6 vacuum's weight-two representation is

    1+78+650 = 27 tensor 27bar,

since the2430 in Sym^2(78) is the affine null representation. For
A2_1 the corresponding representation is1+2 times8. Thus, if E is
the E6 adjoint restricted to the current pair, A=(1,3)+(1,5), and
P is the restricted27, the exact ambient representation is

    B_2=P tensor P+E tensor A+1+2A.              (9)

All the A1 representations involved are selfdual, so Pbar=P in this
finite restriction. Its dimension is729+624+17=1370=120+1250.
For the two placements,

    P_125=(2,6)+(1,9)+(1,5)+(1,1),
    P_187=(3,3)+(2,4)+(2,2)+(1,5)+(1,1).        (10)

The first comes from27=(2,6bar)+(1,15) in the A1 times A5 subgroup;
the second from27=(7,3)+(1,6bar) in G2 times A2. Formula(9), combined
with the elementary Clebsch--Gordan rule, gives exact upper bounds
on every irreducible multiplicity in W_2. No large root enumeration
or tensor calculation is needed. Strange owns the separate bounded
representation-support certificate using these data.

## 5. The full host187 commutant has an extra weight-two field

Equation(6) contains a conformal Potts factor P of charge4/5 and the
bare diagonal coset

    C=Com(A1_13,A1_1 times A1_8 times A1_4), c_C=14/5.

Here P=Com(A1_8,A2_2), the maverick Potts coset already established
in the [host615 note](hi_cft_third_e8_host615_commutant.md).
One must not identify D_B,187 with P times C without checking extensions.
There is an additional weight-two state: the spin2 primary in A2_2
has A1_8 label4 of weight3/5 and Potts epsilon weight2/5; the spin2
primary in A2_1 has A1_4 label4 of weight1. Contracting their finite
spin2 representations to a diagonal singlet gives an affine-highest
A1_13 vacuum state at total weight2. Its P,C weights are(2/5,8/5).

Independently, equation(9) has nine finite current singlets at grade2:
five from P tensor P, three from E tensor A and one explicit identity.
Four are affine descendants of the grade-one adjoint copies: one
copy for the level3 factor and three for the level13 factor. Thus

    dim(D_B,187)_2=5,

whereas dim(P times C)_2=1+3=4. A classification of conformal vectors
inside the bare diagonal coset therefore does not classify the full
commutant in B. This is not a statement about the commutant in E8.
The extra field must be included in any such
non-current stress analysis. This is an ambient statement; retention
of P,C or the extra field inside the unknown fixed VOA remains a
separate condition.
