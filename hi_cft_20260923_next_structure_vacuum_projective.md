# The vacuum module is projective

23 September 2026. This is a consequence of the positive-stress
identity and regular subalgebras already certified for U. It uses no
new numerical calculation and no unproved properness assumption.
The permanent resource limits remain in force.

**Proposition.** The vacuum U is a projective object in the finite
abelian category of grading-restricted generalized U-modules. Since
contragredient duality is exact and U is self-contragredient, it is
also injective.

The input from
`hi_cft_20260923_next_structure_top_bound.md` is that every irreducible
ordinary U-module has nonnegative lowest weight, and the vacuum is the
only irreducible with lowest weight zero. The same note carefully
justifies restriction of an actual U lowest space to the highest
spaces of the regular subalgebras with their different stress tensors.

Let pi:E->U be an epimorphism of grading-restricted generalized
U-modules. C2-cofiniteness makes this a finite-length module category,
so all composition factors of E have nonnegative weights. It follows
that E has no negative generalized conformal weights. Its finite
generalized weight-zero space E_[0] maps onto C1 in U.

Every ambient lowering mode annihilates E_[0]. Hence, for every
regular subalgebra A_i occurring in a finite positive stress identity
omega_U=sum_i c_i e_i, the space E_[0] is contained in Omega_A_i(E).
Regularity decomposes E as a weak A_i-module into ordinary simples.
Thus e_i,1 is diagonalizable on E_[0], with nonnegative eigenvalues
among the actual lowest weights of A_i.

The operator L_U(0) is nilpotent on E_[0]. Taking traces in the stress
identity gives

\[
 0=\operatorname{Tr}_{E_{[0]}}L_U(0)
   =\sum_i c_i\operatorname{Tr}_{E_{[0]}}e_{i,1}.
\]

All summands on the right are nonnegative and all c_i are positive.
Every e_i,1 therefore has zero trace, hence is zero on E_[0] by its
diagonalizability and nonnegative spectrum. The only A_i simple of
weight zero is its vacuum module. Consequently each vector in E_[0]
belongs to a sum of A_i vacuum tops, and e_i,0 kills E_[0]. Summing the
stress identity at mode zero now yields

\[
 L_U(-1)E_{[0]}=0.
\]

Choose v in E_[0] with pi(v)=1. Translation covariance and lower
truncation imply that v is vacuum-like. Explicitly, a negative leading
power in Y_E(a,z)v would yield a still lower power after differentiating,
whereas L(-1)Y_E(a,z)v has the original lower bound. The coefficient
of that leading power must therefore vanish; all negative powers
vanish. The standard vacuum-like-vector construction gives a module
homomorphism

\[
 s:U\longrightarrow E,\qquad s(a)=a_{-1}v.
\]

Since pi(s(a))=a_{-1}1=a, this is a section of pi. Every epimorphism
onto U splits, proving projectivity. Exact contragredient duality and
U'=U give injectivity.

## Scope of the consequence

If rigidity of the U-module category can now be proved, projectivity
of the tensor unit implies that every object is projective and the
finite category is semisimple. This would prove rationality without
needing a separate calculation of the categorical dimension of B.
The relevant implication in the rigid setting is used explicitly in
[McRae, end of the proof of Theorem 5.18](https://arxiv.org/html/2108.01898).

The argument above does not prove rigidity. In particular, it must not
be combined with a theorem that already assumes semi-rigidity and
then presented as an unconditional rationality proof.
[Miyamoto, arXiv:0906.1407](https://arxiv.org/abs/0906.1407) requires
semi-rigidity for its projective-cover tensor-product statement. The
ordinary character S-transform condition of McRae's rigidity theorem
also remains an additional hypothesis.

## Subsequent resolution of the rigidity gap

The boundary above concerns those older theorems. It is resolved for
the present U by Etingof–Penneys, arXiv:2412.17681v3, Theorem 1.1,
which does not assume semisimplicity or exactness of tensoring. In a
finite abelian category with right-exact tensor product, tensor-power
endomorphism dimensions have at most exponential growth, hence are
less than n! for some n. Grothendieck–Verdier evaluation to the simple
projective vacuum splits, so every nonzero indecomposable object is
non-negligible in the theorem's sense. The theorem therefore proves
rigidity. Projectivity of the unit then implies semisimplicity.

The complete argument and source audit are in
`hi_cft_20260923_next_structure_rationality.md`. Thus U is strongly
rational. Properness and the identification of its braided module
category remain separate questions.
