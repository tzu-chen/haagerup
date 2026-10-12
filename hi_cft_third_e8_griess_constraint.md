# A weight-two restriction on the abelian E8 host

This is a conditional obstruction in the finite-index unitary E8 setup,
not a determination of the chain's central charge. It uses the compatible
conditional expectation assumed in the [c=1 host argument](hi_cft_third_e8_c1_hosts.md).
Write E=V_E8, W⊂E, [E:W]=3I with I=(13+3√13)/2, and suppose W1 is the
six-dimensional abelian current algebra. Its actual rank-six radical lattice
V_M lies in W. The orthogonal rational two-plane has ambient lattice L;
write D0=Com(W1,W) and DB=Com(W1,B), with B=E^alpha.

Assume DB is a rank-two lattice VOA with no vectors of norm two or four.
This holds for the explicit determinant575 construction, whose DB lattice
has Gram matrix [[6,3],[3,864]]. D0 has central charge two and no currents.

## The quadratic oscillator algebra

Every weight-two state of DB is a linear combination of a(-2)1 and
a(-1)b(-1)1. For v∈(D0)2, L1v lies in (D0)1=0. On the derivative
states L1 a(-2)1=2a(-1)1, whereas it vanishes on the quadratic states.
Consequently (D0)2 is contained in the three-dimensional space Sym²(R²),
after choosing the unitary real form.

For a symmetric matrix A put

    omega_A = (1/2) sum_ab A_ab a_a(-1) a_b(-1) 1.

Wick contraction gives omega_A(1)omega_B=omega_(AB+BA), and the ambient
stress is omega_Id. Thus (D0)2 is a unital Euclidean Jordan subalgebra of
Sym²(R²). Its possible dimensions are one, two and three. In dimension
two its two primitive idempotents are the stresses of a fixed orthogonal
pair of Heisenberg axes. In dimension three every such pair is present.
This uses only the elementary two-by-two symmetric-matrix algebra. The
ambient quadratic Griess algebra and its role in rank-two lattice VOAs
are also described by [Dong–Griess](https://sites.lsa.umich.edu/rlg/wp-content/uploads/sites/1335/2024/09/rank2plus.pdf).

## A rational orthogonal pair is impossible

Suppose D0 contains the two rank-one Heisenberg stresses omega_1,omega_2
along rational lattice axes. Let L1,L2 be the corresponding rank-one
intersection lattices. Their direct sum has finite index in L. The
commutant in E of V_M and the opposite Virasoro algebra is exactly V_Li:
zero conformal energy on the orthogonal directions permits neither their
oscillators nor nonzero momenta.

The expectation E→W is bimodular over V_M and both Virasoro algebras,
so its restriction to V_Li has range

    Di = Com(V_M ⊗ Vir(omega_j), W),  j≠i.

The Pimsner–Popa lower bound restricts with it. Hence Di⊂V_Li is a
finite-index unitary c=1 inclusion. The rank-one classification used in
the [earlier proof](hi_cft_third_e8_c1_hosts.md) applies to each factor.
Every ordinary lattice module that actually occurs in E has integer
constituent dimensions after restriction to Di. At square radii this
uses the equivalent SU(2)1 finite-group description and its pointed
twisted sectors; it does not assert that arbitrary orbifold modules
always have integer dimensions.

Now T=V_M⊗D1⊗D2 lies in W and has full central charge eight. The full-rank
sublattice M⊕L1⊕L2 has finite index in E8. Restricting the resulting finite
ordinary lattice branching to T gives integer dimensions for all its
constituents. Therefore qdim_T(E) and qdim_T(W) are positive integers.
Index multiplicativity implies

    [E:W] = qdim_T(E) / qdim_T(W) ∈ Q,

contrary to [E:W]=3I. This argument does not assume that the restricted
two-element action on D0 is proper, or that [DB:D0]=I.

## Consequence and remaining gap

Under the stated hypotheses, (D0)2 cannot have dimension three. If it has
dimension two, the primitive idempotent axes must be irrational with
respect to the ambient lattice. Dimension one remains possible. Strong
rationality of D0 has not here been shown to force those axes to be rational;
that step must not be inserted without a separate theorem.

The dimension-three exclusion and its application to the full index
[E:W], avoiding properness, have both passed independent review by the
CFT-constraints agent. The result does not classify all finite-index
subalgebras of a rank-two lattice VOA.
