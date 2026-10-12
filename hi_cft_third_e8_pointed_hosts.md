# The remaining pointed E8 commutants and a stabilizer-nine constraint

Update: the [rank-two restriction lemma](hi_cft_third_e8_rank_two_restriction.md)
now derives restricted properness whenever the residual inclusion is
nontrivial in the stated finite rational current-frame setup. The
ordinary-fixed field argument excludes the trivial case. Thus the
proper obstructions below now exclude496 and613 without an initial
restricted-properness assumption. Host0 is also excluded by the later
[complete abelian theorem](hi_cft_third_e8_proper_abelian_exclusion.md).
The earlier categorical examples below remain valid as abstract
possibilities; they do not supply compatible E8 fixed-algebra embeddings.

The full-current hosts0,496,613 have ambient commutants which are
rank-two lattice VOAs. None can have an ordinary finite-group fixed
commutant of the full ambient lattice in the proposed Haagerup E8
realization. The specified proper rank-two hypergroup action is
impossible on the actual commutants for613 and496. The simultaneous
order-three action has now been checked: \(\alpha\) fixes both ambient
commutants pointwise, so \(D_B=D_E\).
Host0 is different: its lattice discriminant can support
the required order-nine structure, and an explicit primitive E8
lattice with that structure exists.

These statements retain the finite-index unitary fixed-algebra
hypotheses of [the residual-c=1 report](hi_cft_third_e8_c1_hosts.md).
They do not establish a quantum operation or a chain-to-coset map.
No numerical computation was used.

## 1. The exact ambient lattices

Let \(E=V_{E_8}\), \(H=\langle W_1\rangle\), and
\(D=\operatorname{Com}(H,E)\).

For host0, \(H=M(1)^6\). The rational completion of the radical inside
\(W\), followed by an ambient Cartan conjugation, gives
\[
 D=V_L,\qquad L=E_8\cap\mathfrak z^\perp,\qquad
 \operatorname{rank}L=2.                            \tag{1}
\]
The lattice \(L\) is primitive in \(E_8\). Its metric is not fixed
by the Lie-algebra host label.

For613, the exact semisimple centralizer dimension is eight and the
residual charge is two. One can identify its embedding directly
inside the regular \(A_{2,1}^4\subset E_{8,1}\): take two whole
\(A_{2,1}\) factors and the principal \(A_{1,4}\) in a third.
The catalog has exactly one class with these factor levels.
The principal conformal embedding \(A_{1,4}\subset A_{2,1}\)
does not change the affine vacuum commutant, so
\[
 D=A_{2,1}=V_{A_2},\qquad L^*/L=C_3.                 \tag{2}
\]
Equivalently, the dimension-eight centralizer must be \(A_2\):
the alternatives have Sugawara charge greater than two.
The level is one, and its nonvacuum modules have weight \(1/3\),
so no further integer-graded conformal extension is possible.

For496, use the regular \(D_{5,1}\otimes A_{3,1}\subset E_{8,1}\).
Inside \(D_5\), put \(A_2\) on the first three coordinates and
take its principal \(A_{1,4}\). The resulting semisimple
centralizer is \(A_1^2\oplus\mathfrak u(1)\), of dimension seven,
matching the unique catalog entry with levels \(A_{1,4}A_{3,1}\).
The Lie conjugacy qualification is the same
[Minchenko Corollary3](https://pi.math.cornell.edu/~andreim/semsimC.pdf)
used in the c=1 report.

Removing the \(A_{3,1}\) vacuum leaves exactly \(D_{5,1}\).
In the \(D_5+A_3\) root-lattice glue, a nontrivial glue class has
a nonvacuum \(A_{3,1}\) module, so it cannot survive.
Replacing the principal \(A_{1,4}\) by the whole \(A_{2,1}\)
is justified by equality of their stress tensors and positivity,
as in the c=1 proof. Its commutant is the rank-three lattice
\[
 N=\{(a,a,a,b,c)\in\mathbb Z^5:3a+b+c\equiv0\pmod2\},
 \qquad \|(a,a,a,b,c)\|^2=3a^2+b^2+c^2.             \tag{3}
\]
For example, the basis
\[
 (a,b,c)=(1,1,0),(0,1,1),(0,1,-1)
\]
has Gram matrix
\[
 \begin{pmatrix}4&1&1\\1&2&0\\1&0&2\end{pmatrix},
 \qquad \det N=12.                                  \tag{4}
\]
The rank-one radical is a rational torus in the centralizer.
After conjugating it into this Cartan,
\[
 D=V_L,\qquad L=N\cap\mathfrak z^\perp.              \tag{5}
\]
Thus \(L\) is a primitive rank-two sublattice of \(N\).
This covers every actual radical placement in the host, not only
a preferred coordinate line.

The exact saved levels and centralizers are in
[the verified E8 catalog](hi_cft_sixhour_e8_subalgebra_results.json).
All the commutant statements are ambient statements; \(D\) must
not be identified with its unknown fixed subalgebra \(D_0\).

## 2. Every ordinary fixed algebra is excluded

Suppose \(D_0=D^G\) for any finite group of unitary automorphisms.
Let \(\widehat H\subset W\) be the rational affine/lattice
completion of \(H\). The ambient algebra \(E\) is a finite
ordinary \(\widehat H\otimes D\)-module.

Under restriction from the pointed lattice algebra \(D\) to
\(D^G\), its ordinary modules only produce neutral
equivariantization constituents. Each such constituent has
integer quantum dimension: the dimension-one lattice module is
multiplied by an integer orbit size and an integer projective
representation dimension. This is the ordinary-module case of
[Dong–Ren–Xu](https://arxiv.org/abs/1507.03306).
No assertion about the dimensions of all twisted modules is
needed. The group \(G\) need not preserve a chosen Heisenberg
Cartan, and need not be classified.

Consequently every constituent of \(E\), and of \(W\subset E\),
over \(T=\widehat H\otimes D^G\) has dimension in
\[
 \mathbb Q\quad(\text{host0}),\qquad
 \mathbb Q(\sqrt3)\quad(\text{hosts496,613}).          \tag{6}
\]
The only nonpointed affine factor is \(A_{1,4}\), whose dimensions
are \(1,\sqrt3,2,\sqrt3,1\).
The resulting ratio
\[
 [E:W]=\frac{\operatorname{qdim}_T E}
              {\operatorname{qdim}_T W}
 \in\mathbb Q(\sqrt3)                               \tag{7}
\]
contradicts \([E:W]=3(13+3\sqrt{13})/2\).

This excludes all ordinary finite-group fixed algebras, including
the trivial group, independently of the chain's tentative
primary dimensions. It does not classify arbitrary conformal
subalgebras of a rank-two lattice VOA.

The same argument survives any finite tower of ordinary orbifolds,
without a lifting assumption on later automorphisms. After the first
restriction, every simple constituent of the ambient \(E\)-module
already has integer dimension in the residual factor. Restriction
under another finite group again multiplies that dimension by an
integer orbit size and projective-representation dimension.
Induction proves the claim for the whole tower. In particular it
covers \(D_E\to D_B=D_E^{\langle\alpha\rangle}\to D_B^G\)
even when \(G\) does not lift to automorphisms of \(D_E\).

## 3. Any proper rank-two quotient over a pointed category needs nine

Here is a categorical statement independent of the lattice rank.
Let \(\mathcal B\) be pointed with finite abelian group \(G\),
and suppose a unitary fusion category
\(\mathcal C=\mathcal B\oplus\mathcal M\) realizes the proper
rank-two quotient of weight \(d^2\), where
\[
 d=(3+\sqrt{13})/2,\qquad d^2=1+3d,\qquad I=1+d^2.
\]
Assume the full central inclusion of \(\mathcal B\) and the
double-coset/neutral-dimension identity supplied by the
[Bischoff finite-index proper-action construction](https://arxiv.org/abs/1608.00253).
The category \(\mathcal M\) is one \(G\)-orbit, as in
[the previous categorical audit](hi_cft_kA2_hypergroup_obstruction.md).

Choose \(X\in\mathcal M\), with stabilizer \(H\leq G\), of order
\(h\). Reciprocity gives
\[
 \pi_{\mathcal B}(XX^*)=\bigoplus_{a\in H}a,\qquad
 \dim X=\sqrt h\,d.                                 \tag{8}
\]
All simples of \(\mathcal M\) have this dimension.
Comparing the nonpointed part of \(XX^*\) gives an integer
multiplicity \(m=3\sqrt h\); hence \(h=s^2\) with \(s\) an integer.

If \(H\ne1\), choose a character of \(G\) nontrivial on \(H\).
It extends to the whole fusion ring by sending all nonpointed
simples to zero. Products of two such simples cause no problem,
because the character annihilates every translate of
\(\sum_{a\in H}a\).
This one-dimensional representation has formal codegree \(|G|\).
[Ostrik, Theorem2.13](https://arxiv.org/abs/1309.4822)
therefore supplies a center object of dimension
\[
 \frac{\operatorname{Dim}\mathcal C}{|G|}=I=2+3d.
\]
Its image under forgetting is a nonnegative integer sum of simples
of dimensions \(1\) and \(sd\). Thus \(s\mid3\).
For nontrivial \(H\), this forces
\[
 |H|=9.                                            \tag{9}
\]

The free case \(H=1\) is impossible, as follows. There are
\(|G|\) nonpointed simples \(gX\), all of dimension \(d\).
Since \(XX^*\) has three nonpointed summands counted with
multiplicity, its duality-invariant odd multiset contains a
selfdual object. Relabel \(X\) to be selfdual. Then
\[
 X^2=1+MX,\quad M=\sum_g m_g g,\quad
 m_g=m_{g^{-1}},\quad \sum_gm_g=3.                   \tag{10}
\]
Centrality makes the ring commutative. Every character \(\chi\)
of \(G\) has two extensions with values \(t_\pm\) on \(X\),
where
\[
 t^2-m_\chi t-1=0,\qquad
 m_\chi=\sum_gm_g\chi(g)\in\mathbb R.
\]
Their formal codegrees are \(|G|(1+t_\pm^2)\). The two
associated center objects have dimensions
\[
 z_\pm=\frac{I}{1+t_\pm^2},\qquad z_++z_-=I.         \tag{11}
\]
By the same theorem, each forgetful image contains the tensor
unit once, because the ring representation is one-dimensional.
Write \(z_\pm=a_\pm+b_\pm d\), with nonnegative integers
\(a_\pm\geq1,b_\pm\). Equation(11) forces
\(a_\pm=1\) and \(b_++b_-=3\).

If the \(b\)'s are1 and2, then
\[
 m_\chi^2
 =\frac{(z_+-z_-)^2}{z_+z_-}
 =\frac{d^2}{(1+d)(1+2d)}
 =\frac13,
\]
which is impossible because \(m_\chi\), a sum of roots of unity,
is an algebraic integer. Thus the \(b\)'s are0 and3 and every
\(|m_\chi|=3\). Equality in the triangle inequality for every
character forces the support of \(M\) to be a single element
\(g\), because characters separate elements of \(G\).
Inverse symmetry gives \(g^2=1\), and \(Y=gX\) obeys
\[
 Y^2=1+3Y.
\]
The rank-two fusion subcategory generated by \(Y\) is excluded
by Ostrik's rank-two classification.

We have proved the necessary condition
\[
 \boxed{9\mid |G|,\quad\text{with a stabilizer of order nine}.}   \tag{12}
\]
The free-orbit argument was independently reviewed by the
integrability agent. It uses both parts of Ostrik's theorem:
the dimension formula and the unit multiplicity of the
forgetful image.

## 4. Consequences for613 and496

For613, \(|G|=\det A_2=3\), immediately violating (12).

For496, equation(3) gives a stronger uniform fact:
\[
 v_3(\det L)\leq1                                  \tag{13}
\]
for every primitive rank-two \(L\subset N\). To see this,
localize at three, where the parity condition disappears and
\(N_{\mathbb Z_3}\) has Gram form \(\operatorname{diag}(3,1,1)\).
The last binary form is anisotropic over \(\mathbb F_3\):
\(b^2+c^2=0\) implies \(b=c=0\).
Primitivity makes \(L/3L\) a two-dimensional subspace of
\(N/3N\).

If this plane avoids the radical of the mod-three form, its
projection to the last two coordinates is an isomorphism,
and the determinant is a unit. If it contains the radical,
choose one basis vector reducing to that radical and one
reducing to a nonzero vector in the last two coordinates.
The first has norm exactly three times a unit, the second
has unit norm, and their inner product is divisible by three.
The Gram determinant then has valuation exactly one.
This proves(13), contradicting(12).

Therefore the specified proper rank-two operation cannot act on
either full ambient commutant \(D_E=\operatorname{Com}(H,E)\).
The actual quotient acts on \(B=E^\alpha\), so the relevant domain
is \(D_B=D_E^\alpha\). This distinction cannot be omitted:
a nontrivial order-three lattice action could multiply the determinant
by nine and invalidate the preceding divisibility argument.

The [simultaneous-alpha audit](hi_cft_third_alpha_commutants.md)
now closes this point. In host613, the regular \(A_2^4\) glue and
the order-three lift force the fourth \(A_2\) action to be central;
the other possibilities have fixed Lie dimension80 or134, whereas
the required \(E_6+A_2\) fixed algebra has dimension86.
In host496, the honest \(\operatorname{Spin}(10)\) order-three lift
has toral representative \((A,A,A,B,C)/3\). The fixed-dimension86
condition forces \(A\ne0\), \(B=C=0\pmod3\), which acts trivially
on every lattice vector \((x,x,x,y,z)\in N\).
Thus it fixes \(V_N\) and every allowed binary residual slice.

Both arguments were independently reviewed here; the root agent
also ran the exact27/243-case integer certificate linked in that note.
Consequently \(D_B=D_E\), and the proper-restriction exclusions
for496 and613 are complete under the stated finite-index/unitary
setup. They still do not exclude a nongroup, nonproper restriction
of the ambient quantum operation.

Section2 remains an obstruction whenever the final \(D_0\) is an
ordinary fixed algebra of \(D_E\), or an iterated ordinary fixed
algebra as proved there. The latter induction handles ordinary
fixed algebras of \(D_B\) even when their automorphisms do not lift.

## 5. Why this does not exclude every pointed commutant

A fully faithful central inclusion of a nondegenerate pointed
category does not generally split a fusion category as a tensor
product. The near-group category with group \(C_3^2\) and
multiplicity nine is a counterexample relevant here; its
existence is recorded in
[Evans–Gannon, Table2](https://arxiv.org/abs/1208.1500).

One construction is to equivariantize a Haagerup category by the
inner \(C_3\) action generated by conjugation with \(\alpha\).
Its three invertibles each yield three invertibles, while the
three noninvertibles form one orbit and produce an object of
dimension \(3d\). It has global dimension \(9I\), and is
Morita equivalent to \(\mathrm{Hg}\boxtimes\mathrm{Vec}_{C_3}\).
The pointed factor of its center is \(Z(\mathrm{Vec}_{C_3})\),
of dimension nine. Its universal grading is trivial, because
the square of the noninvertible contains itself and every
invertible, so these center invertibles remain distinct under
forgetting. Thus the required central pointed inclusion can
exist without a rank-two tensor factor.

For host0, the lattice \(\operatorname{diag}(6,12)\) has
discriminant group \(C_6\times C_{12}\), with a hyperbolic
\(C_3^2\) metric factor. It passes (12). This is a categorical
possibility, not an established action on the lattice VOA.
The separate constructive note records its primitive E8
embedding and the remaining realization problem.
