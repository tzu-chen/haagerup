# The determinant-575 candidate: weight-two and weight-three constraints

This note concerns the conditional proper-action E8 construction, not an
identification of the physical chain. It assumes the unitary finite-index
VOA/net bridge and the proper quotient used in the
[host0 capacity theorem](hi_cft_third_e8_host0_proper_constraints.md).
The exact lattice certificate has been executed by the root agent:
[28 passed checks](hi_cft_third_e8_host0_det575_results.json).

Write
\[
 I=(13+3\sqrt{13})/2,\qquad
 D_B=V_{L_B},\quad
 \operatorname{Gram}(L_B)=\begin{pmatrix}6&3\\3&864\end{pmatrix}.
\]
Its determinant is 5175=9·575, of rational squareclass 23. Its only
norm-six vectors are the pair ±h, and it has no norm-two or norm-four
vectors. The actual rank-six lattice K is rootless, with
\[
 \dim(V_K)_1=6,\quad \dim(V_K)_2=55,\quad\dim(V_K)_3=316.
\]
The prescribed E8 fixed character gives
\(\dim W_2=120,\dim W_3=956\).

## 1. Odd extension order forces exactly one weight-two field

Capacity saturation makes W a local simple-current extension of
\(T=V_K\otimes D_0\) of order 575. Every nonidentity extension summand is
paired with a distinct contragredient summand, because the extension
group has odd order. The two graded characters agree, by the
nondegenerate graded pairing. Hence their aggregate contribution is
even in each integral conformal grade.

Since \(D_{0,1}=0\),
\[
 \dim T_2=55+\dim D_{0,2},\qquad
 \dim T_3=316+6\dim D_{0,2}+\dim D_{0,3}.
\]
The first congruence makes \(\dim D_{0,2}\) odd. The quadratic Heisenberg
Jordan algebra has dimension three, and the
[rational-axis argument](hi_cft_third_e8_griess_constraint.md)
excludes dimension three. Thus
\[
 \dim D_{0,2}=1,\qquad \dim D_{0,3}\ \text{is even and at least two}. \tag{1}
\]
The only weight-two field is the total stress tensor. The second
conclusion uses the nonzero derivative of that stress. In particular
there is an odd positive number of genuine weight-three Virasoro
primaries.

The same parity argument works for any odd-order proper host0 extension
with rootless K, provided the same fixed character and the stated
quadratic-current hypotheses hold. It does not apply to a general
nonproper restriction.

## 2. A weight-three primary cannot contain the norm-six vertices

Choose orthonormal real Heisenberg currents a,b. The zero-charge
weight-three primary space has three real dimensions: the antisymmetric
bilinear
\[
 A=a(-2)b(-1)\mathbf1-a(-1)b(-2)\mathbf1
\]
and the harmonic cubic doublet, represented by
\[
 a(-1)^3-3a(-1)b(-1)^2,\qquad
 3a(-1)^2b(-1)-b(-1)^3.
\]
Under rotations these are the spin-zero representation and the real
spin-three representation. This statement follows directly by imposing
\(L_1v=L_2v=0\) on the oscillator basis at weight three.
In the convention where a,b are Hermitian currents, the Hermitian
weight-three antisymmetric field is iA; this phase does not change its
rotation type or the projection argument. Real linear combinations in
the physical primary space must respect this PCT phase.

The only additional weight-three states in \(D_B\) are \(e^h,e^{-h}\).
Let X be the traceless weight-two tensor whose zero mode is the
difference of the oscillator energies parallel and perpendicular to h.
On the zero-charge primary space every matrix element of X vanishes:
X transforms as spin two, whereas the available angular charges differ
only by 0,3,6. X preserves lattice charge, so it has no matrix elements
between the oscillator primaries and the vertices. Both vertices have
X eigenvalue +3.

Consequently, if a Hermitian weight-three primary v has vertex
coefficients z and its conjugate, then
\[
 \langle v,o(X)v\rangle=3\bigl(\|v_h\|^2+\|v_{-h}\|^2\bigr).
\]
A nonzero value is precisely a nonzero X component in the self-OPE of v,
by invariance of the unitary form. That would put an additional
weight-two field in D0, contradicting (1). The vertex coefficients
therefore vanish.

Together with parity this leaves
\[
 \dim D_{0,3}=2\ \text{or}\ 4,                    \tag{2}
\]
and all its genuine weight-three primaries are pure Heisenberg
oscillator states. This conclusion does not identify the surviving
one-dimensional primary direction.

## 3. All three oscillator primaries generate the C3 Heisenberg orbifold

Let \(u=(a+ib)/\sqrt2,\ v=(a-ib)/\sqrt2\), so
\(u(z)v(w)\sim(z-w)^{-2}\). A 120-degree rotation acts with eigenvalues
\(\omega,\omega^{-1}\). The invariant weight-three fields are
\[
 A_0=\tfrac12(:u\partial v:-:\partial u\,v:),\quad
 C=:u^3:,\quad D=:v^3: .
\]
Lian–Linshaw give a minimal strong generating set of
\(\mathcal H(2)^{C_3}\) with weights
\(2,3^3,4,5^3\), and display the weight-four and weight-five neutral
generators as \((A_0)_{(1)}A_0\) and its product with \(A_0\).
Their remaining generators are \(C,D,:u^2\partial^2u:,
:v^2\partial^2v:\). One Wick contraction gives
\[
 (A_0)_{(0)}C=-3:u^2\partial^2u:,\qquad
 (A_0)_{(0)}D=+3:v^2\partial^2v:.
\]
Thus the stress and these three weight-three primaries generate the
entire C3 orbifold as a vertex algebra. This uses the explicit
generators in [Lian–Linshaw §13, pp69–70](https://arxiv.org/pdf/2107.03243),
not a classification of its modules or of extensions.

A pure harmonic cubic alone is not thereby identified with the full
S3 Heisenberg orbifold: the latter has an additional weight-four
generator. The strong generator distinction is visible in
[Milas–Penn–Shao](https://arxiv.org/abs/1804.01036).

## 4. A multiplicity-free Fock argument excludes the C3 branch

**Lemma.** Let L be a positive-definite rank-two even lattice whose
determinant does not have rational squareclass 3. If a unitary
current-free subVOA \(U\subset V_L\) contains
\(\mathcal H(2)^{C_3}\), then
\[
 U=\mathcal H(2)^{C_3}.
\]
In particular U cannot have finite index in \(V_L\).

Let R be rotation by 120 degrees. If a nonzero vector p belongs to
\(L\cap RL\), then a nonzero pair \(q,Rq\in L\) spans a full-rank
sublattice. Its Gram determinant is \(3\|q\|^4/4\).
It follows that \(\det L\) has squareclass 3, a contradiction. Thus
\[
 L\cap RL=\{0\}.                                  \tag{3}
\]

The lattice decomposition is
\(V_L=\mathcal H(2)\oplus\bigoplus_{p\ne0}\mathcal F_p\).
Every nonzero Fock module has trivial C3 stabilizer.
The finite-orbifold Schur–Weyl theorem therefore says that its
restriction to \(\mathcal H(2)^{C_3}\) is irreducible. Restricted modules
from different C3 orbits are inequivalent. These statements require
only a simple countable vertex algebra and a finite automorphism group,
not rationality or C2-cofiniteness; see
[Dong–Ren–Yang, Theorem7.4 and Corollary7.5, pp22–23](https://arxiv.org/pdf/2302.09474),
or [Dong–Yamskulna, Theorems6.1 and6.13](https://arxiv.org/pdf/math/0006005).

By (3), each nonzero restricted Fock module occurs exactly once inside
\(V_L\). Its zero-charge summand has three distinct simple components,
the C3 eigenspaces of the Heisenberg vacuum. Both nontrivial components
have weight-one states.

The entire displayed module is an algebraic direct sum of simple
modules. Any submodule, including U, splits by isotypic components.
Consequently U either contains all of a nonzero \(\mathcal F_p\) or
none of it. If it contains one, the unitary conjugation supplies
\(\mathcal F_{-p}\). The OPE of their ground states contains
\(p(-1)\mathbf1\) with nonzero coefficient, contradicting \(U_1=0\).
So U lies in the zero-charge Heisenberg algebra. Its two nontrivial
C3 eigenspaces are likewise prohibited by \(U_1=0\), proving the lemma.
No induction in a nonrational tensor category is used.

Finally, the Heisenberg subnet has infinite index in the lattice
subnet: it is the fixed subnet for the continuous lattice torus.
Equivalently its lattice decomposition has infinitely many charge
sectors. The finite C3 extension cannot change that conclusion.
There is also a direct VOA contradiction with strong rationality:
the continuously many real Fock charges, modulo finite C3 orbits,
give infinitely many inequivalent ordinary modules of the fixed VOA.

For the determinant-575 construction the lemma applies because
\(\det L_B=5175\) has squareclass 23. The second option in (2) would
contain all three primaries and hence the C3 orbifold, which is
impossible at finite index. We obtain the strengthened requirement
\[
 \boxed{\dim D_{0,2}=1,\qquad \dim D_{0,3}=2.}       \tag{4}
\]
There is exactly one real weight-three primary. Sections 5--7 below
resolve its mixed, pure antisymmetric, and pure harmonic possibilities.

The parity and vertex-projection steps were independently checked by
the root agent. The multiplicity-free module argument and its precise
Dong–Ren–Yang hypotheses were independently checked by the uniform
agent in a [separate audit](hi_cft_third_heisenberg_c3_basechange_audit.md).
These restrictions do not construct D0, prove its existence, or
identify the physical chain.


## 5. A mixed antisymmetric/harmonic primary is also excluded

Rotate the harmonic doublet so that the single Hermitian primary has
the form \(itA+bB\), with real t,b and
\(B=a(-1)^3-3a(-1)b(-1)^2\). The factor i is the PCT phase described
above. The following calculation is polynomial, so write \(a_0A+bB\)
during it and substitute \(a_0=it\) at the end.

Set
\[
 U=\sum_{j=1}^2a_j(-3)a_j(-1),\quad
 V=\sum_{j=1}^2a_j(-2)^2,\quad
 R_4=(a_1(-1)^2+a_2(-1)^2)^2 .
\]
Direct Wick contraction gives
\[
 A_{(1)}A=-10U+3V,\quad
 L_{-4}\mathbf1=U+\tfrac12V,\quad
 L_{-2}^2\mathbf1=U+\tfrac14R_4 .
\]
The genuine primary part of \(A_{(1)}A\) is
\[
 P_4=-4U+3V+\tfrac32R_4,\qquad \|P_4\|^2=384.       \tag{5}
\]
For example the Gram matrix of the two displayed vacuum descendants
is \(\left(\begin{smallmatrix}10&6\\6&10\end{smallmatrix}\right)\);
their inner products with \(A_{(1)}A\) are −36 and −60.

The C3-invariant weight-four oscillator space has dimension six:
three bilinears, one neutral quartic, and the two derivatives of the
charged cubics. Removing the two Virasoro vacuum states and the three
weight-three-primary derivatives leaves one genuine primary, P4.
It has rotation spin zero, so \(A_{(1)}B\) has no P4 component.
The following zero-mode actions also hold:
\[
 P_{4,(3)}A=-96A,\quad P_{4,(3)}B=0,\quad
 A_{(2)}B=-6C,\qquad
 C=3a(-1)^2b(-1)-b(-1)^3 .                         \tag{6}
\]
These can be checked without a large OPE: the U,V,R4 zero-mode
eigenvalues on A are respectively 15,−12,0 and on B are 9,0,24.
Invariance of the bilinear form then shows that \(B_{(1)}B\) also has
zero P4 component.

Thus the primary part of
\((a_0A+bB)_{(1)}(a_0A+bB)\) is \(a_0^2P_4\).
If both coefficients are nonzero, the generated subalgebra contains
P4, then A by (6), then B and C. It contains the full C3 orbifold,
contrary to Section4. The necessary single primary is therefore either

- the pure antisymmetric field iA, generating \(\mathcal H(2)^{SO(2)}\);
- a pure harmonic cubic, generating the zero-background-charge
  Miura \(W_3\) algebra at c=2.

The antisymmetric generator statement follows from the explicit
neutral generators cited in Section3. The harmonic free-field
\(W_3\) realization is described, for example, in
[Bouwknegt–McCarthy–Pilch §2](https://arxiv.org/pdf/hep-th/9509119).
It is not the full S3 Heisenberg orbifold.

Equations (5)–(6) were derived by hand and independently verified by the
root agent's bounded exact oscillator-mode checker, executed under the
128MiB guard at 18:39:27 UTC on 2026-09-15.
The [exact results](hi_cft_third_heisenberg_weight3_results.json) passed
all controls and also give the cubic map
\[
 F_A=-186a_0^3+540a_0b^2,\qquad
 F_B=-90a_0^2b+540b^3.
\]
Its collinearity obstruction is \(bF_A-a_0F_B=-96a_0^3b\),
independently excluding every nonzero mixed pair, including the
Hermitian substitution \(a_0=it\).

## 6. The pure antisymmetric branch is excluded

The [independent SO(2) argument](hi_cft_third_heisenberg_SO2_obstruction.md)
now excludes the pure antisymmetric branch for a lattice determinant
outside squareclasses 1 and 3, assuming D01=0 and D02=C omega.
It proves charged Fock irreducibility by finite-energy polynomial
interpolation of neutral bilinear modes, applies the corrected compact
quantum Galois theorem to D0 intersect H, and rules out both continuous
rotation-invariant charge support and finite cyclic orbit support.
The root and CFT-constraints agents independently reviewed that proof.

It remains to analyze the harmonic Miura W3 algebra. No classification
of all its rational extensions, and no retained c=1 factor inside D0,
is assumed in that analysis.

## 7. The pure Miura branch is excluded by exact module characters

The [generic-orientation proof](hi_cft_third_e8_miura_orientation.md)
first shows that a finite-index current-free extension with D02=C omega
must have a rational A2 screening root. Generic Fock modules cannot mix
with nongeneric ones by a positive-character comparison. Their Weyl
orbits meet this binary lattice in at most two nonorthogonal points,
whose positive quadratic self-OPE is anisotropic. Removing those
modules leaves only a finite union of rank-one charge subgroups unless
a screening root is rational; that support has zero character ratio to
the rank-two lattice.

A rational screening root is possible, for example (4h+k)/10, but the
[single-screening proof](hi_cft_third_miura_rational_screening.md) excludes
it too. The FKRW character formula proves the required semidegenerate
irreducibility, including the factor 1-q^(j+1). In determinant
squareclass23, inequivalent transverse momenta cannot acquire hidden
isotypic copies through the other Weyl transformations or through fully
degenerate zero-transverse sectors. Every transverse highest vector has
a fixed nonzero relative-stress expectation j²/4-23r², also for linear
combinations of copies. Its self-OPE would contradict D02=C omega.
The remaining rank-one charge support again has zero character ratio,
incompatible with finite-index strong rationality.

The root agent independently checked the primary character theorem;
the CFT-constraints and uniform agents independently checked the module
separation and relative-stress argument. Together Sections1--7 exclude
the **specified determinant575 proper-action construction**, under the
unitary finite-index and fixed-character hypotheses stated at the start.
They do not exclude all E8 constructions, do not close the nonproper
restriction gap, and do not determine the physical chain's central charge.
