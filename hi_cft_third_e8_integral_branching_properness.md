# Integral ambient branching transfers properness for hosts496 and613

This note extends the [abelian normal-pair argument](hi_cft_third_abelian_normal_pair_index.md)
to the two remaining nonabelian current hosts whose residual commutants are
rank-two lattices. The argument does not assume that restriction preserves
extremality. It derives that conclusion from the ambient branching and
index. It retains the same unitary rational VOA/conformal-net compatibility,
finite-index conditional expectation, and proper ambient rank-two inclusion
hypotheses as that note.

Let E=V_E8, W subset B=E^alpha, [E:B]=3 and [B:W]=I, with

    I=(13+3sqrt(13))/2,   I^2-13I+13=0.

Choose the actual rational affine/lattice completion H inside W:

    host496: H=A3_1 tensor A1_4 tensor V_M, rank M=1;
    host613: H=A2_1 tensor A2_1 tensor A1_4.

The [simultaneous-alpha proof](hi_cft_third_alpha_commutants.md) gives
D_B=Com(H,B)=Com(H,E)=V_L in both cases. The rational completion M
need not be maximal; subsequent extensions of H are handled explicitly.
Put D0=Com(H,W), J=[D_B:D0], and C=Com(D0,W).

## 1. Only integral H dimensions occur in E

Both embeddings factor through the conformal inclusion A1_4 subset A2_1.
Its complete affine branching is

    A2 vacuum -> A1 labels 0 + 4;
    A2 fundamental and antifundamental -> A1 label 2.

An explicit primary reference is [JHEP07(2020)009, Eq.(2.25)](https://inspirehep.net/files/a287988fa47ff5f0cc61feac136efd68).
It also follows from equality of the stress tensors, the allowed A1_4
weights, and the ground representations 8=3+5 and 3=3. The relevant
quantum dimensions are 1,1,2. Labels1 and3, of dimension sqrt(3), never
occur on restriction of an ordinary A2_1 module.

For496, use A3_1 tensor A2_1 inside E8 and the rational orthogonal
rank-three lattice N of the [pointed-host note](hi_cft_third_e8_pointed_hosts.md).
The sum of M and L has finite index in N. Thus A3, A2, M and L form
a full-rank lattice frame in E. For613, use the regular A2_1^4 lattice
frame, replacing the third A2 by its principal A1_4. Every other
factor is pointed. It follows that every simple H tensor D_B
constituent of E has an integer quantum dimension. In particular

    k=[E:H tensor D_B] is a positive integer.                 (1)

This is an assertion about the ordinary modules actually appearing
in E, not about every module of Rep(H). It avoids any general theorem
that an arbitrary condensation preserves weak integrality.

## 2. The maximal commutant may extend H without spoiling integrality

D0 contains the full D_B stress tensor. A vector of C therefore has
zero D_B conformal energy. Since D_B is a positive-definite lattice
VOA, every nonvacuum lattice module has strictly positive lowest
weight. Zero D_B energy in E is exactly the D_B-vacuum highest space.
Consequently

    C subset Com(D_B,E),   C tensor D_B subset E.              (2)

H subset C, and both have the same conformal vector. Rationality of
H and finite branching make C a finite local extension of H. Its
dimension a=[C:H] is an integer by Section1. For any simple C-module
X occurring in E, its restriction is a finite sum of H-modules from
Section1, so

    dim_C X = dim_H Res(X)/a in Q.

The left side is an algebraic integer and positive; hence it is a
positive integer. This proves precisely the integrality needed for
the modules of C appearing in W, even if C is a proper extension of H.
Also [E:C tensor D_B]=k/a is rational (indeed integral).

The pair C,D0 is normal in W. One commutant equality is its definition.
Since H subset C, Com(C,W) is contained in Com(H,W)=D0; the reverse
inclusion follows from C=Com(D0,W). Equation(2) and H subset C likewise
give

    Com(C,B)=D_B.                                             (3)

## 3. Mirror equivalence and the norm force J=I

Apply [McRae, Theorem1.1](https://arxiv.org/pdf/2107.06577) to the
finite rational normal pair C,D0. It yields distinct simple modules
X_i,Y_i and a braid-reversed equivalence, with

    W = direct sum_i X_i tensor Y_i,
    dim X_i=dim Y_i,
    g=[W:C tensor D0]=sum_i (dim X_i)^2 in Z_(>0).             (4)

Only X_0 is the C vacuum, and Y_0 is the D0 vacuum. Positivity/unitarity
identifies the categorical and Frobenius-Perron dimensions.
Index multiplicativity now gives

    (k/a) J = 3I g,
    J = (3ag/k) I = r I,   r in Q_(>0).                      (5)

The restricted Pimsner--Popa estimate gives J<=I. J is an algebraic
integer. Writing r=u/v in lowest terms, its field norm is
13u^2/v^2 in Z, which forces v^2 to divide13, so v=1. Thus r is a
positive integer at most one:

    J=I.                                                     (6)

## 4. Induction transfers canonical rank

The isotypic-evaluation proof of Section6 of the
[normal-pair note](hi_cft_third_abelian_normal_pair_index.md) applies
without requiring the X_i to be invertible. For the W extension
algebra A in Rep(C tensor D0),

    Hom_A(Ind(1 tensor Y),Ind(1 tensor Z))
       = sum_i Hom_C(1,X_i) tensor Hom_D0(Y,Y_i tensor Z)
       = Hom_D0(Y,Z).

Thus induction is fully faithful on the D0 factor. Equation(3) identifies
the multiplicities of these simple induced modules in B with the
ordinary D0-module multiplicities in D_B. Their occurrence in B makes
them local; locality is not assumed for arbitrary induced modules.
The resulting isotypic embedding Ind(D_B) into B has dimension J=I,
so is an isomorphism. Therefore

    dim End_D0(D_B)=dim End_W(B)=2.                           (7)

The canonical-hypergroup interpretation and multiplicity-freeness in
[Bischoff, Corollary4.2 and Proposition4.10](https://arxiv.org/pdf/1608.00253)
then give exactly two canonical operations for D0 subset D_B.
Together with J=I, the canonical Haar decomposition makes the
restricted nonidentity operation extreme. The residual action is proper.

## 5. Consequence and scope

The [proper pointed-commutant obstruction](hi_cft_third_e8_pointed_hosts.md)
requires nine to divide the lattice discriminant. Host613 has
discriminant3. Every allowed host496 binary lattice has 3-adic
determinant valuation at most one. Both contradict that condition.
Therefore these two hosts are excluded even when residual properness
was not initially assumed, provided the ambient proper rank-two and
unitary finite-index hypotheses above hold.

This is a deduction for the specified E8 realization. It does not
establish that the H3 lattice chain is a current commutant, and it does
not classify unrestricted quantum operations on lattice VOAs.
No numerical computation is used. The ambient branching and normal-pair
steps are the additional ingredients compared with an unsupported
claim that extremality survives arbitrary restriction.
