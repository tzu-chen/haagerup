# The c=18/5 F4 diagonal coset is excluded

23 September 2026. Consider the unitary affine coset

\[
 Y=\operatorname{Com}(L_{A_1}(13,0),
                       L_{F_4}(1,0)\otimes L_{A_1}(1,0)),
\]

where the first A1 has Dynkin index twelve in F4, and the displayed
level-thirteen algebra is diagonal. Its central charge is 18/5. The
character calculation below gives **dim Y_2=13**, whereas the full
actual residual commutant has dimension five in weight two. Thus this
candidate is excluded as the actual residual VOA. This comparison does
not require an identification of Y's module category.

## An explicit index-twelve embedding and three commuting stresses

Use the standard F4 roots in Euclidean four-space: the long roots
are ±e_i±e_j and the short roots are ±e_i and
(±e_1±e_2±e_3±e_4)/2. Two commuting A2 root systems have simple roots

\[
 e_1-e_2,\quad e_2-e_3;
 \qquad e_4,\quad(e_1+e_2+e_3-e_4)/2.
\]

Their long-root normalizations give levels one and two inside F4 at
level one. Their central charges are 2 and 16/5, totaling F4's 26/5;
unitarity makes this inclusion conformal. The principal A1 of each
A2 has index four, so the affine subalgebras have levels four and
eight. Their diagonal has level twelve. Adding the separate level-one
A1 gives level thirteen as required.

The following three stress differences are mutually commuting,
nonzero, and lie in Y:

| stress difference | central charge |
|---|---:|
| omega_(A2,2) minus omega_(A1,8) | 4/5 |
| omega_(A1,4) plus omega_(A1,8) minus omega_(A1,12) | 64/35 |
| omega_(A1,12) plus omega_(A1,1) minus omega_(A1,13) | 34/35 |

The principal embedding A1,4 in A2,1 is conformal because both have
central charge two. Hence the three differences sum to omega_Y.
Orthogonality of commuting Virasoro stresses and their positive
central charges prove their linear independence.

For comparison with established coset results, the first coset is the
familiar SU(3)_2/SU(2)_8 Potts example discussed by
[Dunbar and Joshi](https://arxiv.org/abs/hep-th/9309093).
The middle diagonal coset falls under the level-four family proved
rational and C2-cofinite by
[Lin](https://arxiv.org/abs/2107.09400).
The last is the unitary Virasoro minimal model M(14,15).
These identifications support the candidate's rational frame, but the
three-dimensional lower bound uses only the explicit affine stresses.

## The full weight-two dimension is thirteen

Write V_j for the (j+1)-dimensional simple sl2 representation. Under
the diagonal principal embedding of the two A2 factors,

\[
 52\downarrow A_1=6V_2+4V_4+2V_6,\qquad
 26\downarrow A_1=2V_0+3V_2+3V_4.
\]

These can be checked directly from the displayed roots. The principal
Cartan is h=(4,2,0,2). The adjoint weights are the 48 roots and four
zero weights; the 26-dimensional representation has the 24 short roots
and two zero weights. Counting their h-values gives the decompositions.
The standard tensor identities are

\[
 \operatorname{Sym}^2(26)=1+26+324,\qquad
 \operatorname{Sym}^2(52)=1+324+1053'.
\]

Here 1053' has highest weight 2theta, distinguished from the other
1053-dimensional F4 representation. These identities and their
highest-weight labels are tabulated in
[Slansky, Tables 44–46](https://web2.ph.utexas.edu/~vadim/Classes/2004f/Slansky.pdf).

For even j, a multiplicity-m copy of V_j contributes m(m+1)/2
singlets to its symmetric square. Distinct j do not contribute cross
singlets. It follows that Sym^2(26) has 3+6+6=15 singlets, hence 324
has 15-1-2=12. Similarly Sym^2(52) has 21+10+3=34 singlets, so 1053'
has 34-1-12=21.

The full ambient affine current space of F4,1 tensor A1,1 restricts as
7V_2+4V_4+2V_6. Its symmetric square has 28+10+3=41 singlets. At
grade two the integrable F4 level-one vacuum relation is precisely
the highest-2theta representation 1053'; the external level-one A1
relation is V_4 and contains no singlet. Derivatives of currents have
no singlet either. Thus the ambient grade-two horizontal-singlet
space has dimension 41-21=20.

The diagonal A1,13 affine vacuum contributes one such singlet, its
Sugawara vector. At ambient weight one, after removing the diagonal
currents, there are six affine highest-space copies of V_2, four of
V_4, and two of V_6. Each V_2 copy contributes one horizontal singlet
among its first affine descendants; V_4 and V_6 contribute none.
There are no level-thirteen integrability relations at this grade.
There is no commutant weight-one space, because the ambient currents
contain no horizontal singlet. Complete reducibility for the unitary
affine subalgebra therefore gives

\[
 \dim Y_2=20-1-6=13.
\]

## Limits of the candidate

The actual A_L inside U has four weight-one states. The familiar
E8 construction involving F4,1 and G2,1 has a different visible
affine core, so matching central charges or braided categories does
not identify the actual embedding here. Nor does a rational ambient
VOA and rational A_L automatically prove rationality of
Com(A_L,B); its C2-cofiniteness remains an independent question.

The root-coordinated exact producer
`hi_cft_20260923_next_residual_ambient2.py` determines the full
weight-two commutant in B. Its output is the relevant comparison,
rather than the kernel restricted to the certified generated span S2.
The completed certificate gives dimension five, which differs from
thirteen and excludes this F4 coset candidate. This is an all-ambient
weight-two comparison, independent of whether U is proper in B.

## A universal-Griess shortcut does not settle properness

[Roitman's On Griess Algebras](https://arxiv.org/html/math/0302021),
Theorem 6.1 and Remark 6.2, construct an OZ vertex algebra from a
commutative algebra with invariant form. The universal presentation
there imposes that the entire weight-one space vanishes. Thus its
universal property cannot be applied to our generated subVOA before
excluding additional currents. The paper's initial-segment discussion
does not remove this circularity. Closure of the certified low-weight
products alone still does not exclude higher-weight products producing
new currents.
