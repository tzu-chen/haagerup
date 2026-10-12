# An explicit bound on every irreducible lowest conformal weight

23 September 2026. This argument uses the certified positive stress
identity and regular subalgebras in the preceding proof report. It is
analytic; no numerical job was launched. All permanent resource limits
remain in force and the September 15 exception is expired.

**Result, sharpened using the known core T.** Every irreducible ordinary
module M for the constructed U has lowest conformal weight

\[
 \boxed{0\leq h(M)\leq\frac{10190}{1521}<7.}
\]

Moreover h(M)=0 only for M isomorphic to U. In particular, every
irreducible summand in the restriction of B to U begins in one of the
integer grades 0,1,...,6. This applies to actual U-modules, not to
candidate current-top representations whose module existence is unproved.
The argument does not assume that all U-modules are unitary.

## A trace version of the positive-stress argument

Suppose a CFT-type VOA V has a finite positive identity

\[
 \omega_V=\sum_{i=1}^N c_i e_i,\qquad c_i>0,
\]

where e_i is the stress of a regular vertex subalgebra A_i, with the
same grading on A_i as inherited from V. Assume each A_i has finitely
many simple ordinary modules, whose lowest weights lie in [0,H_i].

Let M be an irreducible ordinary V-module, of lowest weight h, and let
E=M_h, a nonzero finite-dimensional space. Every ambient lowering mode
of every A_i-vector annihilates E, since its A_i weight equals its V
weight. Thus E is contained in the Zhu highest space Omega_{A_i}(M).
Regularity decomposes the weak A_i-module M into simple ordinary
A_i-modules. The highest space of each such simple module is exactly
its lowest space. It follows that e_i,1 is diagonalizable on E and all
its eigenvalues are among the actual simple lowest weights of A_i.

Here Omega_A means annihilation by **all** homogeneous a in A at
all indices n satisfying wt_A(a)-n-1<0. No finite-generator proxy for
Omega_A is used. The equality Omega_A(N)=N_top for a simple ordinary
module is the standard Zhu theorem; see, for example,
[Liu, Section 2.1.1, item (4)](https://doi.org/10.1007/s00209-026-03976-y).
Restriction is initially only a weak A-module because the stresses
differ. Regularity is what supplies its algebraic direct sum of
ordinary modules; each vector has finitely many components, so the
annihilation equations apply componentwise. The differing ambient
stress therefore causes no gap in the argument.

The stress identity on E says h I_E=sum_i c_i e_i,1. Taking ordinary
finite-dimensional traces gives

\[
 0\leq h
   =\sum_i c_i\frac{\operatorname{Tr}_E(e_{i,1})}{\dim E}
   \leq\sum_i c_i H_i.
\]

No common eigenbasis and no invariant positive form on M is used.
Individual e_i,1 need not commute. The finite positive decomposition
of the Haar averages is already justified in the proof report by
finite-dimensional convexity. Each conjugate A_i has the same set of
lowest weights, so the same bound applies term by term.

If the only simple A_i-module of weight zero is its vacuum module,
then equality h=0 implies e_i,1=0 on E for every i. Therefore E lies
in a sum of A_i-vacuum top spaces, and e_i,0 E=0. The stress identity
now gives L_V(-1)E=0. A nonzero v killed by L(-1) is vacuum-like:
the translation identity and lower truncation force Y_M(a,z)v to have
no negative powers of z, and a maps to a_{-1}v defines a V-module
homomorphism V to M. For simple V and irreducible M this map is an
isomorphism. Consequently the vacuum is the unique weight-zero simple
module.

## The exact maxima for the subalgebras used here

For the integrable affine VOA A1 at level k, simple tops have weights
j(j+2)/(4(k+2)), 0<=j<=k; their maximum is k/4. Thus the two affine
maxima are 1/4 and 39/4.

For K(sl2,k), a complete set of simple labels is 0<=j<i<=k. Their
actual, unreduced lowest weights are

\[
 h_{i,j}=\frac{i(k-i)}{2k(k+2)}+\frac{j(i-j)}{k}.
\]

The affine and parafermion formulas and this complete label range are
given in [Arakawa–Lam–Yamada, Section 2.4, (2.18)](https://arxiv.org/html/1701.06229).
These weights are nonnegative, and only the vacuum label has weight
zero. The formula gives

\[
 h_{i,j}\leq\frac{i(i+2)}{4(k+2)}.
\]

At k=13 the largest value with i<=12 is at most 14/5. At i=13,
j(13-j)/13 is maximal at j=6,7, giving exactly 42/13. Thus H_PF13=42/13.
At k=3 the same formula gives H_Potts=2/3, using the certified
identification of the Potts algebra with K(sl2,3). These are actual
lowest weights, not values reduced modulo one.

Insert these maxima into the certified identity

\[
 \omega_U=\omega_{A_{1,1}}
 +\frac{3403}{4563}\omega_{A_{1,39}}
 +\frac{25}{6}\overline p+\frac{25}{26}\overline z.
\]

It yields

\[
 \frac14+\frac{3403}{4563}\frac{39}{4}
 +\frac{25}{6}\frac23+\frac{25}{26}\frac{42}{13}
 =\frac{20390}{1521}.
\]

All the component module categories have unique weight-zero vacuum
sectors, so the uniqueness conclusion also applies.

## The rational core improves the bound to below seven

The actual strongly rational core T supplies additional constraints.
Write a lattice dual vector as

\[
 \lambda=\frac{s}{2}a_0+\frac{m}{78}H,
 \qquad s,m\in\mathbb Z,\quad s\equiv m\pmod2.
\]

The parity condition is precisely integrality of its pairing with
t=(3a0+H)/2. Its left A1 and H contributions to conformal weight are
s^2/4+m^2/156. In each left A1 coset the minimum left weight is 0 for
even m and 1/4 for odd m. The extension field has lattice momentum
r=a0/2+H/6 and shifts (s,m) by (1,13).

Label Potts simples by a Fibonacci flag epsilon=1,tau and a simple-current
charge a modulo 3. Their weights are respectively (0,2/3,2/3) and
(2/5,1/15,1/15). Pairing with r has fractional part 2m/3; the Potts
simple-current monodromy is a/3. Thus locality requires a=m modulo 3.
The extension identifies m with m+13 and a with a+1. The free order-three
orbits give exactly the 26 core modules, labelled by epsilon and m mod13.

Their actual lowest weights are therefore

\[
 h_T(\epsilon,j)=\min_{m\equiv j\ (13)}
 \left\{\frac{m^2}{156}+\frac{\delta_{m\ {m odd}}}{4}
          +h_P(\epsilon,m\bmod3)\right\}.
\]

The simple-current construction and Potts/lattice data used here are
those already established in the rational-core certificate; the table
below is a direct minimization, not a modular-weight computation.
Symmetry identifies j and -j, leaving:

| j | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| epsilon=1 | 0 | 12/13 | 9/13 | 4/13 | 10/13 | 14/13 | 3/13 |
| epsilon=tau | 2/5 | 21/65 | 6/65 | 46/65 | 11/65 | 31/65 | 41/65 |

For completeness, choosing |m|<=6 first gives the upper bound 14/13
for every row entry. Every |m|>=13 has m^2/156>=169/156>14/13 and
cannot minimize. It is therefore enough to check m=j and m=j-13 for
1<=j<=6, and m=0 for j=0. This gives the displayed exact table.
Consequently H_T=14/13. Every H-charge on every T top satisfies

\[
 m^2/156\leq14/13,\qquad |m|\leq12.
\]

Now E=M_h is contained in Omega_T(M). As a representation of the right
sl2 zero modes, E is finite-dimensional and completely reducible. Each
highest sl2 label j contributes an H eigenvalue j, hence j<=12. The
right affine stress acts there by its Sugawara Casimir, so its largest
possible eigenvalue improves from 39/4 to

\[
 \frac{12(12+2)}{4(39+2)}=\frac{42}{41}.
\]

Already the original positive stress identity now gives
41969/6084<7. A slightly smaller bound follows by averaging the core
stress. Since H^2=78 and the right affine level is 39, compact right
sl2 averaging gives

\[
 \overline{\omega_T}=\omega_{A_{1,1}}
       +\frac{41}{117}\omega_{A_{1,39}}+\overline p.
\]

This is the usual average of one Cartan square over the three
orthogonal current directions. Substitution in the certified identity
leaves the entirely positive identity

\[
 \omega_U=\overline{\omega_T}
  +\frac{1804}{4563}\omega_{A_{1,39}}
  +\frac{19}{6}\overline p+\frac{25}{26}\overline z.
\]

Applying the trace argument and the improved affine bound yields

\[
 h(M)\leq\frac{14}{13}
 +\frac{1804}{4563}\frac{42}{41}
 +\frac{19}{6}\frac23+\frac{25}{26}\frac{42}{13}
 =\boxed{\frac{10190}{1521}<7}.
\]

The core T is regular and its nonvacuum lowest weights are positive,
as the table confirms, so the uniqueness of the weight-zero U-sector
also follows from this refined identity.

## What this finite bound does and does not decide

By the previous unitary finite-branching argument, B is an orthogonal
finite sum of irreducible U-modules. Every summand has its top in B at
an integer weight bounded above as proved here. Hence B is generated
as a U-module by its grades through 6. Every U-submodule is determined
by its intersection with those grades: a nonzero orthogonal complement
would contain an irreducible summand whose top occurs there. Likewise
restriction gives an injection

\[
 \operatorname{End}_U(B)\hookrightarrow
 \operatorname{End}\!\left(\bigoplus_{n=0}^{6}B_n\right).
\]

The same bound applies to restrictions of all nine lattice sectors,
using their actual conformal weights rather than integer vacuum grades.

This is a bound on the top spaces of already existing modules. It does
not show that generator closure truncated at grade 6 equals the actual
U through grade 6. Relations arising from a higher-grade excursion
can still change that finite span. Nor does every matrix on the finite
space on the right extend to a U-endomorphism. Constructing such an
extension requires compatible relations for the generating fields;
the bound alone does not supply them. It therefore sharpens the finite
branching target without proving properness, Zhu semisimplicity,
rationality, or the Haagerup category.

The separate projective-vacuum and Etingof–Penneys argument in
`hi_cft_20260923_next_structure_rationality.md` now proves rationality.
The limitation just explained concerns what the top bound alone proves.
