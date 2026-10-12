# What strong rationality now proves about the lattice extension

23 September 2026. Write B=V_(E6+A2), H=V_E8 and
C=Rep(U). The separate rationality proof makes C a modular fusion
category. The positive-stress argument proves that every nonvacuum
simple U-module has strictly positive lowest conformal weight.

## Positive dimensions and actual algebra objects

All simple objects have positive quantum dimensions, given by the
high-temperature character ratios S_i0/S_00; these dimensions are
multiplicative and agree with Frobenius–Perron dimensions. This follows
from [Dong–Jiao–Xu, Lemma 4.2 and Proposition 4.9](https://arxiv.org/html/1201.2738).
The modular-category dimension is the same one. Thus C has the
positive spherical structure. This assertion does not require a
priori unitarity of every irreducible U-module.

The actual finite conformal extensions U⊂B⊂H define connected
commutative algebra objects with trivial twist. This is the
[Huang–Kirillov–Lepowsky extension correspondence](https://arxiv.org/abs/1406.3420).
They are separable: a simple self-dual extension has the nondegenerate
invariant pairing, and its categorical dimension is positive, so the
associated Frobenius multiplication can be normalized to split.
Equivalently one can use the finite-index extension theorem in
[McRae, arXiv:2103.07657](https://arxiv.org/abs/2103.07657).

Let s=FPdim_C(B). Since the U vacuum occurs once, s≥1, with equality
if and only if B=U. If B is proper, positivity and the lower bound 1
on a simple Frobenius–Perron dimension give s≥2. These are actual
categorical assertions, but no numerical value of s is yet known.

The local B-module category is Rep(B), whose nine simples are the
discriminant sectors of E6+A2 and all have dimension one. Therefore

\[
 \boxed{\operatorname{FPdim}(C)=9s^2.}
\]

The index-three lattice extension B⊂H is an order-three simple-current
extension. Multiplicativity of quantum dimensions along extensions
therefore gives FPdim_C(H)=3s. Since H is holomorphic, H is a
Lagrangian algebra in C. In particular

\[
 \boxed{C\simeq Z(\mathcal F),\qquad
        \mathcal F=C_H,\qquad \operatorname{FPdim}(\mathcal F)=3s.}
\]

Here C_H is the category of all right H-algebra modules in C; it is
not the local module category, which is Vec. The dimension formula
and the center conclusion are
[DMNO, Corollaries 3.32 and 4.1](https://arxiv.org/html/1009.2117).
Thus Witt triviality is now proved for the actual U.

## Properness and the numerical Haagerup target remain separate

The Haagerup target would give

\[
 s=\frac{13+3\sqrt {13}}2,\qquad
 \operatorname{FPdim}(C)=9s^2.
\]

None of the facts above distinguishes this value from s=1 or another
positive algebraic index. The finite ordinary dimension 80 of the
complementary current space is not its categorical dimension. A
rank-two branching assertion B=U⊕X would also still need an all-weight
proof; rationality alone does not exclude summands starting at higher
weights. The sharp top bound now confines any such summands to
integer weights 1 through 5.

The known triviality of Aut(B) fixing U implies that any proper
extension here is not an ordinary nontrivial fixed-point inclusion.
It does not force s=1: connected commutative algebra objects can have
trivial automorphism group and nontrivial dimension. In particular,
ordinary group-index classification cannot supply the missing value.

What rationality supplies is a valid finite tensor-category setting
for constructing and checking an extension algebra or a compatible
noninvertible symmetry. A finite spectral projection, or its rescaled
quadratic polynomial, still lacks the multiplication/intertwiner
compatibility that would identify that algebra.
