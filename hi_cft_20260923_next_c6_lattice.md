# The explicit rank-six lattice in the conditional c=6 construction

23 September 2026. Read-only algebra from the frozen neighbor certificate;
no new numerical job. The identification of the lattice itself is
unconditional on properness of U. Its Haagerup interpretation retains
the hypotheses in the [c=6 coset note](hi_cft_20260923_next_c2_asymmetric_coset.md).

The perpendicular lattice N has rank six, determinant39 and root system
A2+A2+A1. More explicitly, it is the even index-six extension

    N = (A2 + A2 + A1 + <78>) + Z(omega,omega,alpha/2,u/6),

where omega is an A2 fundamental weight with squared norm2/3,
alpha is the A1 root with squared norm2, and u has squared norm78.
The displayed glue vector has squared norm4. This describes an isometry
class, including the glue, rather than just a root system or determinant.

## An integral Gram matrix and the actual embedding

One convenient abstract basis is a1,a2,b1,b2,c,v, with the first five
vectors the simple roots of A2+A2+A1 and v the glue vector. Its Gram is

    [ 2,-1, 0, 0, 0, 1]
    [-1, 2, 0, 0, 0, 0]
    [ 0, 0, 2,-1, 0, 1]
    [ 0, 0,-1, 2, 0, 0]
    [ 0, 0, 0, 0, 2, 1]
    [ 1, 0, 1, 0, 1, 4].

The Schur complement gives determinant
18*(4-2/3-2/3-1/2)=39. Its perpendicular vector is

    u=6v-4a1-2a2-4b1-2b2-3c,  u^2=78.

Here is also a basis directly in the saved original E8 coordinates.
Let e0,...,e7 have diagonal Gram2 and off-diagonal entries -1 on
the edges (0,1),(1,2),(2,3),(3,4),(2,5),(6,7). The ambient lattice is
the index-three extension of this E6+A2 root lattice by

    lambda=(4/3,5/3,2,4/3,2/3,1,2/3,1/3).

The vectors e0,...,e6,lambda are an integral basis of E8. The saved
plane is spanned by

    a=(-1,-2,-3,-2,-1,-2,0,0),
    H=(5,8,9,8,5,0,2,2).

Indeed Ga=(0,0,0,0,0,-1,0,0) and
GH=(2,2,2,2,2,-9,2,2). For an E8 vector
sum_(i=0..6)y_i e_i+k lambda, the two orthogonality equations say

    y5=-k,  y6=-sum_(i=0..4)y_i-8k.

They give a complete integral basis of N:
n_i=e_i-e6 for i=0,...,4 and n5=lambda-e5-8e6.
Replacing n5 by w=n5-2n0-2n1-2n2-n3-n4 gives

    w=(-2/3,-1/3,0,1/3,-1/3,0,2/3,1/3),

and the Gram in n0,...,n4,w is

    [ 4, 1, 2, 2, 2,-2]
    [ 1, 4, 1, 2, 2,-1]
    [ 2, 1, 4, 1, 2,-1]
    [ 2, 2, 1, 4, 1, 0]
    [ 2, 2, 2, 1, 4,-2]
    [-2,-1,-1, 0,-2, 2].

This is an explicit embedding certificate derived directly from the
two linear equations. The root-and-glue proof below identifies it with
the simpler first Gram; no uncomputed change-of-basis matrix is claimed.

## Why its root system is exactly A2+A2+A1

The frozen [neighbor output](hi_cft_20260923_next_neighbor_roots.json)
has joint Cartan-zero multiplicity22 in its E8 adjoint. Subtracting
the eight Cartan directions gives14 perpendicular roots. The
[independent neighbor audit](hi_cft_20260923_next_neighbor_independent_audit.md)
proves that the original and neighbor lattices have exactly the same
perpendicular lattice N, so this counts the actual original N roots.

None of these roots lies in the E6+A2 root sublattice. For an E6 root,
orthogonality to a forces its e5 coordinate to vanish. Such roots form
the parabolic A5 on e0,...,e4. H pairs to2 with every one of those
simple roots, so no positive or negative A5 root is perpendicular to H.
The same positivity argument works for the separate A2 on e6,e7.
Thus every N root has nonzero charge in E8/(E6+A2)=Z3.

An A3 subsystem is impossible. If its consecutive simple roots are
r,s,t, the roots r+s and s+t must also have nonzero charge. Since
each charge is +1 or -1 in Z3, this forces all three simple charges
to agree. But then r+s+t is a neutral root, a contradiction. Every
irreducible simply laced root system of rank at least three contains
an A3, so only A1 and A2 components remain.

Fourteen roots and rank at most six leave A2+A1^4 or A2^2+A1;
A1^7 has excessive rank. The former has full rank and determinant48,
so its index in N would have square48/39, impossible. Therefore the
root lattice is exactly R=A2^2+A1, of rank five and determinant18.

## The glue is forced

The discriminant quadratic form of R, with q(x)=x^2/2 mod1, is

    D_R=Z3^2+Z2,
    q_R(a,b,c)=(a^2+b^2)/3+c^2/4 mod1.

It has no nonzero isotropic element. Thus R has no proper even
overlattice in its real span and is primitive in N. Let K=R^perp
intersect N have generator u with u^2=2m, and let the index of
R+K in N be r. The glue projects injectively into both discriminant
groups. Since D_K is cyclic and D_R has exponent6, r divides6.
Determinants give

    39=18*(2m)/r^2,  hence m=13r^2/12.

Integrality of m forces r=6 and u^2=78. A generator of the unique
order-six subgroup on the K side is u/6, with quadratic value
13/12=1/12 mod1. Its partner must have value11/12 in D_R. This
forces both A2 components and the A1 component to be nonzero.
Independent diagram conjugations of the two A2 factors reverse their
Z3 generators, so there is a single glue choice up to isometry. It is
precisely (omega,omega,alpha/2,u/6) displayed above.

Consequently V_N is a fully specified rank-six lattice VOA, with
weight-one Lie algebra A2+A2+A1 plus one abelian current, dimension20.
Its discriminant form is the reverse of the saturated plane lattice:
Z39 with q(n)=-n^2/39. In contrast, the conditional subVOA C6 has
no weight-one currents. These statements concern the c=6 construction;
they do not identify the physical chain, whose central charge is only
approximately2 in the available data.

The independent structure agent audited the ambient linear equations,
both root-system alternatives, the no-isotropic-class argument, the
index-six glue, the abstract Gram determinant and the perpendicular
u expression. All passed without correction. Root independently
checked the same abstract Gram and determinant/glue calculation.
