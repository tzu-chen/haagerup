# A_L has no proper integer-graded conformal extension

23 September 2026. The actual c=22/5 core A_L is its own double
commutant in B=V_(E6+A2), in V_E8, and in U. More strongly, its
commuting residual stress s=omega_B-omega_(A_L) satisfies

\[
 \operatorname{Com}(\operatorname{Vir}(s),B)=A_L,
 \qquad
 \operatorname{Com}(\operatorname{Vir}(s),V_{E8})=A_L.
\]

The argument does not assert rationality or C2-cofiniteness of the
opposite c=18/5 commutant.

## Only one possible extension label, and it cannot extend

Use the fourteen simple labels x_a=(1,a), y_a=(tau,a), a=0,...,6,
of Rep(A_L)=Fib tensor SO(3)_13. Their actual conformal weights are
the table independently checked in
`hi_cft_20260923_next_structure_order13_top_check.json`.
Only x_0 and x_5 have integer conformal weights, respectively zero
and one.

Suppose D is a simple CFT-type integer-graded conformal extension of
A_L with finite-dimensional graded spaces. Regularity of A_L as a
weak-module theory implies complete reducibility of D. Because its
conformal vector is the same, there are no freely shifted copies of
an A_L module: each copy has that simple module's specified lowest
weight. Each multiplicity is finite by the corresponding graded-space
dimension. The vacuum multiplicity is one because D_0=C. Therefore

\[
 D\cong A_L\oplus mX,\qquad X=x_5,\qquad m\in\mathbb Z_{\ge0}.
\]

The SO(3)_13 label of X is the even affine label i=10. The truncated
SU(2)_13 fusion rule gives

\[
 X\boxtimes X=x_0\oplus x_1\oplus x_2\oplus x_3.
\]

In particular X does not occur in its own square. If m>0, the only
X-times-X channel that can land back in D is x_0. Consequently the
linear map sigma acting by +1 on A_L and -1 on mX preserves every
vertex product. It fixes the vacuum and conformal vector, has order
two, and D^sigma=A_L.

Apply the compact-orbifold tensor theorem of
[McRae, Corollary 4.8](https://arxiv.org/html/1810.00747).
For a simple VOA D whose fixed VOA admits the required vertex tensor
category, its G-isotypic constituent modules generate a tensor
subcategory equivalent to Rep(G). Here Rep(A_L) is already modular,
so the hypothesis holds for G=<sigma>=Z2. The odd part is therefore
one irreducible A_L module, and its square is the vacuum. Thus m=1
and X boxtimes X=x_0, contradicting the displayed four-channel
fusion rule.

Equivalently, its Frobenius-Perron dimension would have to be one,
whereas

\[
 \operatorname{FPdim}X
   =\frac{\sin(11\pi/15)}{\sin(\pi/15)}>1.
\]

Hence m=0 and D=A_L. This proof uses the orbifold tensor equivalence,
not the older quantum-dimension theorem with additional assumptions
on twisted-module positivity. If needed, strong rationality of a
hypothetical D also follows directly from McRae's Theorem 4.14 since
its fixed VOA A_L is strongly rational.

## Apply the extension obstruction to the actual ambient commutants

Let V be B or V_E8. The actual fields omega_(A_L) and s are commuting
unitary conformal vectors with omega_V=omega_(A_L)+s. Positivity and
the vacuum-like-vector property identify

\[
 D=\ker_V L^s(0)=\operatorname{Com}(\operatorname{Vir}(s),V).
\]

This D is a unitary simple VOA containing A_L. Its conformal vector
is omega_(A_L), and on D its grading agrees with the ambient integer
grading because L^s(0)=0. In particular D has finite-dimensional
graded spaces and D_0=C. The preceding regularity argument makes it
a finite conformal extension of A_L, and the obstruction gives D=A_L.

Set C=Com(A_L,V). Since Vir(s) is contained in C, taking commutants
reverses inclusions and gives

\[
 A_L\subseteq\operatorname{Com}(C,V)
   \subseteq\operatorname{Com}(\operatorname{Vir}(s),V)=A_L.
\]

Thus Com(C,V)=A_L. The same proof or restriction to U yields the
corresponding statements in U.

This establishes the full double-commutant property without assuming
that C is strongly rational. Mirror-category conclusions that require
C2-cofiniteness of C still need that separate input. Nor does this
identify C with an abstract affine coset having the same category or
central charge.
