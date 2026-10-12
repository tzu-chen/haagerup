# Host615 has the ambient commutant Potts squared

For the E8 current host

    H=A2,1 tensor A2,1 tensor A1,8,
    c_H=32/5,

the actual ambient commutant is

    D_E=Com(H,V_E8)=Potts tensor Potts,   c_D=8/5.       (1)

Every order-three E8 automorphism alpha fixing H pointwise fixes D_E
pointwise. Therefore the actual commutant in B=E^alpha is also the
algebra in (1). The denominator148 with two commuting currents, whose
formal coset charge is21/10, has ambient coset Ising times Potts squared.
These are ambient VOA identifications, not a retention assertion for
the eventual fixed CFT. No numerical calculation is used.

## 1. Exact placement in the catalog

The saved [current-host scan](hi_cft_sixhour_e8_proper_current_results.json)
lists denominator148 as A1,2 times A1,8 with abelian rank2, and host615
as its sole possible full nineteen-current host. The denominator and
host charges are59/10 and32/5, respectively, leaving the relative
charge1/2. The [semisimple catalog](hi_cft_sixhour_e8_subalgebra_results.json)
has exactly one row with factor levels A1,8 times A2,1 squared: row615.
Its exact Lie-centralizer dimension is zero. This last uniqueness check
is a read-only filtering of saved metadata, not a new embedding search.

Use the regular A2 to the fourth root sublattice of E8. Take the first
two A2 factors in full. In each remaining A2, take its principal A1,
which has index4, and take their diagonal A1. Its induced level is8.
Thus this construction has precisely the catalog type and levels of615.
[Minchenko, Corollary3, printed page245](https://pi.math.cornell.edu/~andreim/semsimC.pdf)
states that the only semisimple E8 linear class splitting under inner
conjugacy is an exceptional simple A2 class. It is not the present
A1 times A2 squared type. The exhibited embedding consequently
represents the actual inner-conjugacy class615.

The A2 fourth-power glue is the ternary tetracode

    C=span{(1,1,1,0),(0,1,-1,1)} subset F3^4.          (2)

Every nonzero word has support three. In particular the projection
to any two coordinates is an isomorphism. Selecting the full affine
vacuum of the first two A2 factors in V_E8 therefore removes every
nonzero glue sector and gives exactly

    Com(A2,1 tensor A2,1,E)=A2,1 tensor A2,1            (3)

on the last two coordinates. This is a vacuum-module selection, not
merely a zero finite-dimensional Cartan-weight selection.

## 2. Two successive cosets give two commuting Potts algebras

The diagonal A1,8 factors through

    A1,8 subset A2,2^diag subset A2,1 tensor A2,1.

The commutant of A2,2^diag is the ordinary three-state Potts chiral
algebra P, of charge4/5. This VOA identity is the k=3 instance of
[Arakawa--Lam--Yamada, Introduction and main parafermion/W-algebra theorem](https://arxiv.org/pdf/1701.06229).
Inside A2,2, the principal A1,8 commutant is also P. It is the smallest
maverick coset:

    Com(A1,8,A2,2)=P.                                 (4)

The two descriptions are explicitly compared in
[Cordova--Garcia-Sepulveda, Section3.2, equations3.30--3.31](https://arxiv.org/html/2312.16317).
For a direct primary branching check of (4),
[Dunbar--Joshi, Table1 and the discussion preceding equation11](https://arxiv.org/pdf/hep-th/9309093)
give its vacuum character beginning1+q^2+2q^3+3q^4+4q^5.
The extra weight-three vector is precisely the h=3 simple-current
extension of the unitary Virasoro minimal algebra atc=4/5. Its only
integer-weight irreducible Virasoro modules are h=0 andh=3; the vacuum
and weight-three coefficients fix both multiplicities to one. Hence
this identifies the Potts VOA, not only its central charge.

These two Potts algebras commute and their conformal vectors sum to
the A1,8 coset vector. Their product is simple and embeds conformally
in D_E. The six irreducible Potts modules have lowest weights

    0, 2/3, 2/3, 2/5, 1/15, 1/15.

No sum of two nonzero entries, and no individual nonzero entry, is an
integer. Thus a unitary integer-graded conformal extension of P times P
contains only its vacuum module. There cannot be extra shifted copies:
the ambient L0 equals the product L0, so a highest vector in a module
has its specified lowest weight. The total vacuum space is one-dimensional.
This proves (1) exactly. In particular there is no unexamined simple-current
or mixed-module extension of the two Potts factors.

## 3. Every simultaneous order-three action is trivial on D_E

The automorphism group of the E8 lattice VOA is the compact E8 current
group in the unitary setting; there is no diagram automorphism. An alpha
fixing H pointwise centralizes the first two A2 Cartan tori. Their torus
centralizer is connected, and its roots are the other two A2 systems:
none of the glue roots in (2) has zero projection onto the first two
Cartans. Connectedness of torus centralizers is the compact-group result
in [Knapp, Section3](https://www.math.stonybrook.edu/~aknapp/pdf-files/1-27.pdf).
It follows that alpha lies in the image of SU3 to the fourth and has
a lift

    (z1,z2,g3,g4),

with z1,z2 central because alpha fixes the first two full A2 algebras.
The final A1 is diagonal principal in the last two factors. Its
commutator with the displayed lift could only lie in the finite central
kernel of SU3^4 to E8. That commutator is continuous on the connected
A1 subgroup and equals one at the identity, so it is identically one.
Each g3,g4 therefore separately centralizes a principal SU2 acting
irreducibly on the fundamental3. Schur's lemma gives

    g3=z3,  g4=z4,  with every zi in the SU3 center C3.

The full centralizer of H is consequently the image of C3^4. The
kernel is the tetracode annihilator, which equals C by self-duality.
Thus

    Z_E8(H)=C3^4/C is C3 squared.                      (5)

There is no projective order-nine possibility: all four lift components
are actual cube-one central elements. Each element in (5) fixes the
four affine A2 vacuum VOAs pointwise. In particular it fixes the full
remaining A2,1 squared in (3), and therefore fixes D_E pointwise.

For completeness, every nonidentity element of (5) belongs to the
required E6+A2 fixed-Lie class. Its character on the two-dimensional
glue code has a one-dimensional kernel, containing exactly two nonzero
words. The E8 Lie algebra consists of four8-dimensional adjoints and
eight27-dimensional glue ground spaces. Hence its fixed dimension is

    4 times8 + 2 times27 =86.

This is the E6+A2 root algebra. The conclusion transports under the
actual inner conjugacy used in Section1, so it holds for all compatible
simultaneous pairs, not only for one chosen intrinsic alpha.

## 4. The denominator148 ambient coset

Inside host615, an A1 of level2 must be diagonal in index-one A1
subgroups of the two full A2,1 factors. A single A2 has A1 indices1
or4, while the remaining A1 factor has level8. The commuting A1,8
of the denominator must be the host's level-eight factor: using both
principal A1s inside the first two A2s would leave no commuting
level-two factor. These index and centralizer observations fix the
semisimple placement up to the inner conjugacies already allowed.

The centralizer of the two regular A1s in the two A2s is exactly a
two-dimensional torus. Therefore the denominator's two independent
commuting currents span that torus. Any change of basis gives the
same Heisenberg commutant. In each A2, choose its torus direction
(1,1,-2); the nonzero discriminant modules have torus charges nonzero
modulo3, and cannot have charge zero. Thus zero charge under both
currents first removes all nontrivial E8 glue and leaves

    A1,1 tensor A1,1 tensor A2,1 tensor A2,1.

The first diagonal A1,2 has the usual Ising commutant in A1,1 squared.
The second diagonal principal A1,8 has the Potts squared commutant just
proved. Consequently the complete ambient denominator coset is

    C_E=Ising tensor Potts tensor Potts,   c=21/10.     (6)

Equation (6) is an ambient statement. A later hypergroup-fixed algebra
can be smaller and need not retain any individual factor. Previously
proved minimal-product exclusions apply to a physical theory retaining
these factors under their stated assumptions; (6) alone does not assert
that retention.

## 5. The host615 Haagerup realization is excluded in the rational frame

Let W subset B=E^alpha be the proposed finite rational inclusion with
ambient rank two and index I=(13+3sqrt13)/2, and suppose its full
current algebra is host615. The
[universal restriction lemma](hi_cft_third_e8_rank_two_restriction.md)
shows that D0=Com(H,W) is either D_E or a proper rank-two subalgebra
of D_E at index I, under the explicit unitary VOA/net bridge.

The first case is impossible by an elementary dimension-field argument.
H times D_E is then a rational conformal subalgebra of W and B. All
its simple quantum dimensions lie in the real cyclotomic field
Q(zeta20+zeta20 inverse): the only nonpointed affine factor is A1,8,
and the Potts dimensions are1 andphi. Therefore the ratio of the two
extension dimensions [B:W] lies in that field. Its unique quadratic
subfield is Q(sqrt5), so it cannot contain I or sqrt13.

For the remaining proper case,

    Rep(D_E)=Fib tensor Fib tensor P,
    P=C3 squared with q(a,b)=2(a^2+b^2)/3 mod1.        (7)

P is nondegenerate and anisotropic, with normalized Gauss sum-1.
This is useful categorical input; the mere fusion rule Fib squared
times C3 squared is not itself an obstruction.

A complete reduction through the two Fibonacci module graphs is now
proved in the independently reviewed
[Potts-pair categorical obstruction](hi_cft_third_potts_pair_hypergroup_obstruction.md).
The two commuting Fibonacci actions have only diagonal two-vertex or
regular four-vertex components. A quadratic-field norm excludes the
diagonal case. In the regular case, positivity of the phi coefficient
forces the minimum-dimension objects, together with the pointed C3
squared, to form an actual fusion subcategory. The pointed stabilizer
theorem removes the free case; the only other case is a near-group
C3 squared plus9 subcategory with the given central pointed lift.
No tensor factorization of the whole fusion category is assumed.

The needed metric contradiction has a primary theorem: [Izumi, Theorem9.1 and
Example12.13](https://maths.anu.edu.au/files/8%2520Izumi_2.pdf) give the
all-finite-abelian scope and the unique unitary C3 squared plus9 category;
its pointed central lift is hyperbolic and has two Lagrangian C3s.
[Evans--Gannon, Proposition6, Table2 and Section4.3](https://arxiv.org/pdf/1208.1500)
independently display the bicharacter diag(1,-1) and its unique central
lifts. It cannot equal the anisotropic metric (7), even after reversal.
Thus the proper case is impossible as well as the trivial case.

Host615, and hence its uniquely supported denominator148 with two
commuting currents, is excluded from the stated finite rational E8
fixed-algebra realization. The ambient identification and all-alpha
proof were independently read by the root and CFT-constraints agents;
the categorical proof was independently read by all three research
agents. The unitary finite-index VOA/net bridge remains an explicit
hypothesis. This does not exclude every abstract CFT at21/10 or prove
the physical chain's central charge.
