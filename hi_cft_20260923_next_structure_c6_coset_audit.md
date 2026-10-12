# Independent audit of the lattice c=6 commutant

23 September 2026. Read-only mathematical and primary-source audit of
`hi_cft_20260923_next_c2_asymmetric_coset.md`; no numerical job.

The lattice-coset construction and categorical transitivity argument
pass. They give a concrete c=6 construction, conditional on properness
for the Haagerup fusion-ring conclusions. They do not construct the
physical c=2 limit. The older c=2 lattice-companion obstruction cited at
the end of that note was not independently re-audited here.

## The rationality hypothesis is a proved special case

Let Lambda=E8, P be the rank-two Cartan plane, L=Lambda intersect P, and
N=Lambda intersect P-perpendicular. The actual core contains V_L, and
L has Gram matrix [[2,3],[3,24]], determinant39. Since39 is squarefree,
there is no proper integral overlattice in the same plane. Thus its
displayed integral basis already gives the saturated plane lattice.

Inside the positive lattice VOA V_Lambda, the Heisenberg commutant of
P is V_N. It is also the commutant of V_L. Hence, for the actual U,

    C6 = Com(V_L,U) = Com(H_P,U) = U intersect V_N.

Its stress is the perpendicular Heisenberg stress. The zero eigenspace
of that stress in V_Lambda consists precisely of vectors with no
perpendicular momentum or oscillators, namely V_L. Therefore

    Com(C6,U)=V_L.

This verifies the precise standing hypothesis in
[Creutzig--Kanade--Linshaw--Ridout, Section4.3](https://arxiv.org/html/1611.00305#S4.SS3):
the Heisenberg coset has a positive-definite lattice double commutant.
Under this hypothesis Lemma4.6 gives C2-cofiniteness, Theorem4.12 gives
rationality, and Corollary4.13 supplies the modular category. Simplicity,
CFT type and self-contragredience hold here by the unitary realization.
This is not an appeal to rationality of arbitrary cosets.

## Full lattice support determines the spectator factor

The already established actual A_L decomposition has all39 lattice
labels nH/39 modulo L. Thus U has all39 V_L labels as well. Since V_L
and C6 are strongly rational mutual commutants, the mirror theorem
identifies their branching subcategories and makes each multiplicity
space a distinct simple C6 module. The full lattice support gives the
entire nondegenerate pointed category

    P39^rev subset Rep(C6),    q_P39(n)=n²/39 modulo1.

Müger decomposition gives Rep(C6)=P39^rev tensor D. With this choice of
factorization the actual U extension of V_L tensor C6 is

    Delta_P39 tensor 1_D,

where Delta_P39 is the diagonal connected étale algebra in
P39 tensor P39^rev. Its local-module category is Vec. The local-module
category of the displayed algebra is therefore D, and also Rep(U), so

    Rep(C6) = P39^rev tensor Rep(U).

This factorization does not assume any classification of categories
with the Haagerup modular data. In the proper case, those data yield
rank468, and C6 has no weight-one fields because the retained six
currents have either nonzero P charge or a nonzero positive
Heisenberg mode.

## The ambient extension really transports the same algebra

Write C=Rep(U), and let A_U be the actual connected étale Lagrangian
algebra corresponding to U subset V_Lambda. After the preceding
factorization, the ambient algebra over V_L tensor C6 is

    Delta_P39 tensor A_U.                                  (1)

One way to see this without an algebra-uniqueness guess is to first
condense Delta_P39. Its local category is C. An algebra extending U is
then precisely an algebra in C. Under the inverse correspondence it
is the tensor product (1), including its multiplication, since the
pointed local category is Vec. This is the usual transitivity of
connected étale extension algebras.

Taking the V_L vacuum multiplicity in (1) gives

    1_(P39^rev) tensor A_U.

The same vacuum multiplicity inside V_Lambda is exactly V_N. Thus the
actual chiral extension C6 subset V_N realizes this particular algebra,
not merely an algebra with its numerical dimension or branching vector.

Consequently its algebraic C6-preserving bimodule category is

    P39^rev tensor Bimod_(A_U)(C),

and contains the latter factor faithfully. Put F=C_(A_U). Lagrangian
reconstruction identifies C with Z(F) and A_U with its canonical
induction algebra I(1), so

    Bimod_(A_U)(C) = F tensor F^op

as fusion categories (up to the choice of tensor-op convention).
Primary categorical sources are
[DMNO, Proposition4.4 and Proposition4.8](https://arxiv.org/pdf/1009.2117)
for Lagrangian reconstruction and
[Müger, Section4 and Section8.1](https://arxiv.org/pdf/math/0111205)
for the canonical Morita duality; the double-centralizer step is also
[EGNO, Theorem7.12.11](https://math.mit.edu/~etingof/egnobookfinal.pdf).

In particular the same actual Lagrangian algebra, and hence the same F
with all its associativity data, is transported from the c=8 extension
to this c=6 extension. Identifying F specifically as the desired H3,
rather than a categorification in its established proper-case class,
remains whatever separate identification was required at c=8. The
argument does not need to reconstruct F from S and T alone.

These defects preserve the C6 chiral algebra. They are not additional
noninvertible simple modules of the lattice VOA V_N: its own chiral
representation category remains the pointed category P39^rev.
The algebraic statement does not remove any separate complete-unitarity
or VOA/conformal-net compatibility hypothesis needed to identify every
such bimodule with a unitary physical defect operator. Those realization
requirements should be carried over explicitly from the c=8 framework.
# Subsequent explicit-lattice audit

The separate `hi_cft_20260923_next_c6_lattice.md` was independently read
and checked on23 September2026. Its explicit E8 equations give
`(a,lambda)=-1` and `(H,lambda)=7`, hence exactly
`y5=-k` and `y6=-sum(y0,...,y4)-8k`. These give a full integral basis of
the perpendicular lattice, rather than an index-unknown sublattice.

The root-system argument and glue classification also pass: the nonzero
Z3 charge of every perpendicular root forbids A3;14 roots leave
A2^2+A1 or A2+A1^4, and the latter has impossible squared index48/39.
The former root lattice has anisotropic discriminant form, so is
primitive. Cyclic glue has order dividing6, and the determinant equation
forces order6 and the perpendicular norm78. Isotropy then forces the
nonzero component in both A2 discriminants and in the A1 discriminant,
uniquely up to diagram conjugation. The displayed abstract Gram has
determinant39 and the displayed vector u has norm78.
