# Independent audit of the E8 two-neighbor commutant route

23 September 2026. Algebra and primary-source audit only; no numerical
job. The lattice and all-weight reconstruction steps below pass, using
the already established actual PF3/PF13 subalgebras and actual
39-sector description of A_L. They do not derive these premises merely
from the two stress central charges.

## Lattice data and the perpendicular lattice

Write Lambda for the actual E8 lattice, a=a0, and

    a^2=2, H^2=78, (a,H)=0,
    t=(3a+H)/2, t^2=24, (a,t)=3,
    P=span_R(a,H), L=Z a+Z t.

The Gram determinant of L is39. Therefore L is saturated in Lambda:
the square of any saturation index would divide39. Let

    Lambda_even={x in Lambda : (x,t) is even},
    Lambda'=Lambda_even union (t/2+Lambda_even).

The parity map is nontrivial because (a,t)=3. Lambda_even has index2;
t/2 has even norm6, pairs integrally with Lambda_even, and its double
is in Lambda_even. Thus Lambda' is integral, even, determinant one,
rank eight, and hence is another E8 lattice.

The rank-six perpendicular lattice N=Lambda intersect P^perp is exactly
Lambda' intersect P^perp. Inclusion of N in Lambda_even is immediate.
Conversely, a new-coset vector t/2+x perpendicular to P would satisfy
(x,a)=−3/2, impossible for x in the integral lattice Lambda. This
last argument is essential: perpendicular lattices are not preserved
by arbitrary neighbor constructions.

The new torus lattice is

    L'=Lambda' intersect P=Z(2a)+Z(t/2).

Indeed L intersect Lambda_even=Z(2a)+Z t. Set

    alpha=t/2, gamma=4a−t/2, beta=(alpha+gamma)/2=2a.

Then alpha^2=6, gamma^2=26, (alpha,gamma)=0, and

    Gram(alpha,beta)=[[6,3],[3,8]], det L'=39.

## Exact discriminant transport and its sign

The old discriminant generator is mu=H/39, with q_L(mu)=1/39.
The natural new generator is

    lambda=mu+a=alpha/3+3gamma/13,
    q_L'(lambda)=40/39=1/39 mod Z.

It has order39 modulo L'. If mu+eta is an old glue lift, with
eta in N*, then lambda+eta=(mu+eta)+a lies in Lambda_even because
its t-pairing is1+3=4. Consequently the gluing map for Lambda'
identifies n lambda with exactly the same N discriminant class as
n mu did for Lambda. Unimodularity and discriminant order39 make
this a complete gluing description, not merely an inclusion.

The expression −alpha/3+3gamma/13 is a different valid discriminant
generator, equivalent to14 lambda modulo L'. It is not the natural
transport of mu. The earlier proposed equality with −mu+a is false.

## Transport the actual core, not just its character

Let P_b denote the actual PF3 simple-current sector of charge b,
and Q_k the actual PF13 simple-current sector of charge k. The
established old core has the decomposition

    A_L = direct_sum_(n mod39) V_(L+n mu) tensor P_(-n) tensor Q_(3n).

Each P_(-n) tensor Q_(3n) is an actual multiplicity subspace in the
corresponding N-lattice module. The changed gluing leaves that module
and that subspace unchanged, so in V_Lambda' there is the actual sum

    D' = direct_sum_(n mod39) V_(L'+n lambda) tensor P_(-n) tensor Q_(3n).

This sum is closed under vertex products: all multiplicity-space
intertwining operators are the old ones, and the torus factors have
the same charge fusion. Old closure excludes additional output
multiplicity spaces. Changing the torus cocycle only rescales the
nonzero intertwining operators. Thus this is an embedded simple-current
extension, not a proposed abstract VOA with the same dimension table.

Lattice cocycles can be chosen to agree on the common sublattice and
in particular on N. Two choices have the same commutator and differ
by a coboundary; extending the correcting cochain to the second
lattice identifies their V_N copies. Once this identification is
made, the actual fields p and z are the same fields in both V_N's.
The positive lattice Hermitian form can likewise be chosen to extend
the old form on N: its positive character on N extends to Lambda'.
The transported sum is stable under conjugation, which exchanges
n with −n and each parafermion sector with its dual. Thus the
unitarity/positivity used below is preserved by this construction.
For the finite simple-current extension, uniqueness also follows from
[Arakawa--Lam--Yamada, Theorem2.4](https://arxiv.org/html/1701.06229):
the base is strongly rational and positive, the supported modules are
invertible and have integral weights. Hence no unverified cocycle phase
can change the resulting VOA isomorphism type.

## Actual affine reconstruction in the neighbor

The lattice-parafermion decompositions (2.13),(2.16) and the charge
conjugation (2.19) in the same ALY source identify D' as

    D_std=(L_sl2(3,0) tensor L_sl2(13,0))
          direct_sum (L_sl2(3,3) tensor L_sl2(13,13)).

The second summand has lowest weight3/4+13/4=4. There is also a direct
way to isolate both affine factors inside the transported sum:

    13lambda−alpha−6beta=alpha/3,
    9lambda−alpha−4beta=gamma/13.

The first has PF charges(−1,0), the second(0,1). Their one-dimensional
parafermion tops have weights2/3 and12/13; their lattice energies are
1/3 and1/13. They therefore give the actual weight-one raising and
lowering fields for two commuting affine sl2 algebras, with Cartans
alpha,gamma and levels3,13. Their Sugawara stresses are respectively

    omega_alpha+p,  omega_gamma+z.

This reconstructs the actual PF13 z inside the affine factor; it is
not an identification inferred only from central charge8/5. PF charge
sign conventions may be reversed using the parafermion conjugation
automorphism; ALY explicitly describes this automorphism and the two
equivalent lattice-parafermion decompositions. The primitive lattice
field e^beta supplies the order-two extension above.

## Equality of the full commutants

Both cores have the same stress

    omega_A=omega_P+p+z,

where omega_P is the two-dimensional Heisenberg stress. A vector in
either ambient commutant has zero omega_P energy, hence lies in the
shared V_N. Conversely positivity of the unitary core identifies its
commutant with its zero-energy space. Therefore, inside this common
V_N, both commutants are exactly

    {v in V_N : p_1 v=0 and z_1 v=0}.

It follows at every weight that

    Com(A_L,V_Lambda) = Com(D',V_Lambda').

The order-two extension and its affine subVOA share their stress, so
the right side also equals the commutant of the reconstructed commuting
A1_3 tensor A1_13. This argument assumes no rationality of either
commutant and no finite-branching descent theorem.

## Audit of the subsequent affine-pair conjugacy argument

The level-three Cartan has norm6. All norm-six E8 vectors form one
Weyl orbit; this is precisely
[Nakamura--Sugawara, Lemma8.3](https://www.math.sci.hokudai.ac.jp/~nakamura/451nakamura.pdf).
For a fixed semisimple h, every sl2 triple (e,h,f) has an open orbit
under the connected centralizer G_0 on g_2: sl2 representation theory
makes ad(e):g_0→g_2 surjective. Two open orbits in the irreducible
vector space g_2 must coincide. Once e,h agree, ad(e) is injective
on g_(-2), so f is unique. Thus the Weyl-orbit statement upgrades to
conjugacy of the level-three affine sl2 embeddings; it is not merely
a comparison of Cartan norms.

For the standard inclusion G2_1 tensor F4_1 in E8_1 and
A1_1 tensor A1_3 in G2_1, the full finite Lie centralizer of A1_3
is F4 direct_sum A1. Indeed

    248=(14,1)+(1,52)+(7,26),
    14 under A1_3 x A1_1 = (3,1)+(1,3)+(4,2),
    7 under A1_3 x A1_1 = (3,1)+(2,2).

The last line contains no A1_3 singlet, so there is no missing
centralizer coming from the mixed E8 summand. The two centralizer
factors both have affine level one.

Any commuting level-thirteen sl2 projects to either zero or an
isomorphism in the external A1, contributing index0 or1. Its F4
projection has the remaining index. Section3, immediately before
TableB of
[Penkov--Zuckerman](https://math.constructor.university/penkov/papers/gen_hc_r_final.pdf)
states both that F4 sl2 conjugacy is determined by index and that its
possible indices are

    1,2,3,4,6,8,9,10,11,12,28,35,36,60,156.

Thus the only possibility is index12 in F4 plus index1 in the
external A1. The F4 component is unique up to inner conjugacy, and
any relative sl2 automorphism in the external factor is inner as
well. Hence the ordered commuting pair is conjugate to the standard
level3,13 pair. This step passes independently; no index13 F4
embedding or additional nonconjugate index12 embedding is left open.

## Complete the standard affine commutant step at all weights

There is a short all-weight argument beyond the Lie centralizer.
The standard affine product

    R=A1_3 tensor A1_1 tensor F4_1

has central charge9/5+1+26/5=8 and is a unitary conformal subVOA
of E8_1. Its factors are regular. Their simple lowest weights are

    A1_3: 0,3/20,2/5,3/4 for i=0,1,2,3;
    A1_1: 0,1/4 for j=0,1;
    F4_1: 0,3/5 for l=0,26.

Among these sixteen triples, the only integral sums are the vacuum
(0,0,0), and (3,1,0),(2,0,26),(1,1,26), each of weight one.
Regularity and the shared conformal vector imply that E8_1 is a direct
sum of the corresponding actual ordinary R-modules, with finite
multiplicities; the vacuum multiplicity is one because (E8_1)_0=C.
There are no shifted module copies with a different top weight.
The finite Lie branching above supplies one copy of each nonvacuum
triple, although these multiplicities are not needed for the next step.

Only the R vacuum triple has zero A1_3 energy. Hence

    Com(A1_3,E8_1)=A1_1 tensor F4_1

exactly, with no further affine commutant extension. Together with
the pair conjugacy, the neighbor argument therefore identifies

    Com(A_L,V_Lambda)
       ≅ Com(A1_13, F4_1 tensor A1_1),

where A1_13 is diagonal from the unique index12 A1 in F4 and the
external index1 A1. This is the full VOA identification. It does not
use a general affine-coset rationality assertion or infer an all-weight
commutant from the finite-dimensional Lie centralizer alone.
