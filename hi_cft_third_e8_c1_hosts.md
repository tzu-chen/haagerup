# Five residual-c=1 E8 current hosts: an index obstruction

Under the finite-index unitary E8 Haagerup fixed-algebra hypothesis,
the five full-current hosts 372, 483, 514, 579, and 617 are impossible.
This is an obstruction to the proposed fixed chiral algebra, independent
of the finite-chain spectrum and of whether its restricted quantum
operation remains proper. It does not identify the chain's CFT or prove
that its central charge is two.

The argument uses a complete classification of unitary conformal
subalgebras of rank-one lattice theories. The classification of all
strongly rational \(c=1\) VOAs has also just been completed, in
[Gannon–Rayhaun, Theorem3.1](https://arxiv.org/html/2609.00122v1#S3.SS1),
submitted31 August2026. The latter theorem supersedes the rational
classification gap mentioned in our older c=1 endpoint note. Its
AppendixD on general quantum operations is explicitly speculative and
is not used here.

No numerical job was launched for this argument. Database facts below
are read from the previously verified exact E8 embedding catalog.
The root agent independently checked the primary-source hypotheses,
and the strange-correlator agent independently reviewed the proof.
Both audits passed within the explicitly stated unitary-net bridge.

## 1. Precise conditional setting

Let \(E=V_{E_8}\), and suppose the proposed unitary Haagerup fixed
algebra \(W\) is realized through
\[
 W\subset B=E_{6,1}\otimes A_{2,1}\subset E,\qquad
 [B:W]=I=\frac{13+3\sqrt{13}}2,\qquad [E:B]=3.       \tag{1}
\]
Thus \([E:W]=3I\). The first inclusion is the proposed rank-two
fixed-algebra construction of
[Gannon–Rayhaun, Section4.3](https://arxiv.org/abs/2606.05279).
We require \(W\) to be strongly regular and unitary, with its stated
weight-one algebra and conformal vector.

For the index argument we use the finite-index unitary conformal-net
realization of this inclusion, or equivalently a compatible
vacuum-preserving conditional expectation with a finite
Pimsner–Popa bound. This is an explicit hypothesis about the physical
fixed-algebra construction. A formal modular character, a linear
operator satisfying the rank-two polynomial, or a conjectural VOA
without such an inclusion is not sufficient.

Write \(H=\langle W_1\rangle\), and let
\[
 D=\operatorname{Com}(H,E),\qquad
 D_0=\operatorname{Com}(H,W)\subset D.                \tag{2}
\]
The vacuum expectation \(E_W:E\to W\) is \(H\)-bimodular because it
fixes \(H\). It therefore restricts to an expectation
\(D\to D_0\), with the same positive lower bound. In particular,
\[
 [D:D_0]<\infty.                                    \tag{3}
\]
No assertion that this restricted expectation is an extreme quantum
operation, or that its index equals \(I\), occurs in this step.

The abelian radical of \(W_1\) has a full-rank rational lattice
completion \(V_L\subset W\). This is
[Mason, Theorem3 and Section15](https://arxiv.org/abs/1110.0544).
The rational-radical justification, which avoids applying an arbitrary
irrational-Cartan-subspace version of that statement, is recorded in
[our preceding index audit](hi_cft_e8_ordinary_fixed_obstruction.md).
Let
\[
 \widehat H=H_{\rm ss}\otimes V_L.
\]
It has the same conformal vector and commutant as \(H\).

## 2. Exact ambient commutants

The full-current data and exact Lie-centralizer dimensions are:

| Host | \(H\) | \(c_H\) | Dimension of the centralizer of \(H_{\rm ss}\) in \(E_8\) | Ambient \(D\) |
|---|---|---:|---:|---|
|372| \(A_{3,1}\otimes M(1)^4\) |7|45| rank-one lattice |
|483| \(A_{2,1}^2\otimes M(1)^3\) |7|16| rank-one lattice |
|514| \(A_{2,1}\otimes B_{2,2}\otimes M(1)\) |7|4| rank-one lattice |
|579| \(A_{1,1}^3\otimes A_{2,1}\otimes M(1)^2\) |7|5| rank-one lattice |
|617| \(A_{1,3}\otimes A_{2,1}\otimes A_{2,2}\) |7|3| \(A_{1,1}=V_{\sqrt2\mathbb Z}\) |

The exact input is
[the semisimple embedding catalog](hi_cft_sixhour_e8_subalgebra_results.json);
the surviving host list is
[the c=2 denominator bookkeeping](hi_cft_e8_c2_host_bookkeeping.json).
The entries concern the full \(W_1\), not merely a proper denominator
chosen inside \(W_1\).

For 372, 483, and 579, every semisimple factor is a simply-laced
level-one algebra. These are regular root-lattice subalgebras of
\(V_{E_8}\). After extending their Cartan together with the radical
to an ambient Cartan, the lattice commutant identity gives
\[
 D=V_{E_8\cap(\mathfrak h_{\rm ss}+\mathfrak z)^\perp}.
                                                               \tag{4}
\]
Here \(\mathfrak z\) is the radical Heisenberg space.
It is rational because its lattice completion actually lies in
\(V_{E_8}\). The root span plus \(\mathfrak z\) has rank seven,
so the lattice in (4) has rank one. The level-one parafermion
algebras are trivial, which is why imposing the whole affine
commutant gives exactly this lattice algebra.

The radius need not be fixed by the Lie-algebra catalog. We therefore
write \(D=V_{\sqrt{2m}\mathbb Z}\), allowing arbitrary positive
integer \(m\) compatible with the actual rational torus. The proof
below does not assume that \(13\) is absent from \(m\).

For 514, use the vector embedding
\[
 B_{2,2}=\mathfrak{so}(5)_2\subset \mathfrak{su}(5)_1=A_{4,1}.
                                                               \tag{5}
\]
Its Dynkin index is two and both Sugawara charges are four, so it
is conformal. This is the \(SO(N)_2\subset SU(N)_1\) family, also
described in
[Bouwknegt–Schoutens, Section7.3](https://arxiv.org/abs/hep-th/9210010).
Inside the regular \(A_{4,1}\otimes A_{4,1}\subset E\), put the
additional \(A_{2,1}\) in the second \(A_4\). Its centralizer is
\(A_1\oplus\mathfrak u(1)\), of dimension four.
The saved E8 catalog has exactly one entry with factor levels
\(A_{2,1}B_{2,2}\), namely514, also of centralizer dimension four.
The equality of these centralizers means that every allowed radical
torus also commutes with the larger \(A_{4,1}\).

The computational catalog records linear-equivalence classes.
[Minchenko, Corollary3](https://pi.math.cornell.edu/~andreim/semsimC.pdf)
shows that in \(E_8\) only a particular simple \(A_2\) class splits
under inner conjugacy. None of the classes here is that exception.
Thus this identification is transported by an actual inner
automorphism, not only by matching character data.

Replacing \(B_{2,2}\) by \(A_{4,1}\) does not change the commutant
in any ordinary \(E\)-module. Their conformal vectors agree, and a
\(B_{2,2}\)-vacuum highest vector has \(L_0^{B_2}=0\). Positivity
then allows it only in the ground of the \(A_{4,1}\) vacuum module;
there is one such vector. All nonvacuum integrable \(A_{4,1}\)
modules have strictly positive lowest weight. Hence the 514
commutant is again the rank-one lattice in (4), with the rank-six
regular algebra \(A_4+A_2\) and a rank-one torus removed.

For 617, the residual charge is one and the exact centralizer has
dimension three. Compact reductivity allows either
\(\mathfrak{su}(2)\) or three abelian currents. Three independent
abelian currents would have charge three, contradicting unitarity
of the residual coset. Therefore the centralizer is
\(\mathfrak{su}(2)\) at a positive integer level \(k\), and
\[
 \frac{3k}{k+2}\leq1
 \quad\Longrightarrow\quad k=1.                    \tag{6}
\]
It exhausts the residual stress tensor. The only nonvacuum
\(A_{1,1}\)-module has lowest weight \(1/4\), so it cannot occur in
an integer-graded conformal extension with the same stress tensor.
Consequently \(D=A_{1,1}\) exactly.

## 3. Finite-index unitary subalgebras of a rank-one lattice

The needed theorem is
[Carpi–Gaudio–Hillier, Theorems3.2,3.15 and4.4](https://arxiv.org/abs/1810.10459).
It classifies actual unitary subalgebras and conformal subnets,
without an initial rationality assumption on the subalgebra.

For nonsquare \(m\), every full-conformal subalgebra of
\(V_{\sqrt{2m}\mathbb Z}\), apart from \(\operatorname{Vir}_1\),
is an ordinary fixed algebra under a closed subgroup of the
circle-with-reflection automorphism group. The exceptional
additional subalgebras when \(m=2\) have central charge \(1/2\)
and are irrelevant here.
For square \(m=k^2\), identify
\[
 D=A_{1,1}^{C_k}.
\]
Every full-conformal unitary subalgebra is
\(A_{1,1}^G\), where \(G\) is a closed subgroup of \(SO(3)\)
containing \(C_k\).

Finite index (3) excludes the infinite closed groups and
\(\operatorname{Vir}_1\). Thus only finite groups remain.
These subalgebras are rational in the conformal-net setting.
The corresponding rational orbifold module formulas can also be
used on the VOA side under the compatible unitary realization.

Two elementary consequences are useful:

1. If \(m\) is nonsquare and \(D_0=D^G\), every irreducible
   \(D_0\)-constituent of an ordinary \(D\)-module has **integer**
   quantum dimension. Only the neutral equivariantization is used:
   an ordinary lattice simple has dimension one, and the resulting
   dimension is an integer orbit size times an integer
   projective-representation dimension. Reflection-twisted modules
   may have dimension \(\sqrt m\), but they do not occur in this
   ordinary-module restriction. The decomposition and dimension
   formula are the quantum-Galois/orbifold results of
   [Dong–Ren–Xu](https://arxiv.org/abs/1507.03306). A translation
   may act trivially on lattice-module labels; it then enlarges
   the stabilizer, not the dimension-one underlying simple.
   A nontrivial stabilizer cocycle likewise only changes the
   integer dimension of its projective irreducible representation.
2. For \(D_0=A_{1,1}^G\), every simple \(D_0\)-module has integer
   dimension. The action on the two semion modules is trivial, so
   it is a cleft action on a pointed category. The twisted category
   is itself pointed; equivariantization again gives integer
   dimensions. A rigorous statement and derivation appear in
   [Gannon–Rayhaun, AppendixB.1, equationsB.2–B.5](https://arxiv.org/html/2609.00122v1#A2.SS1).
   This uses AppendixB, not the speculative AppendixD.

The distinction in the first item is essential: a claim that every
rank-one reflection-orbifold module has integer dimension would be
false.

## 4. The extension dimensions cannot produce sqrt13

The algebra \(E\) is a finite ordinary
\(\widehat H\otimes D\)-module. For the regular cases this follows
from the full-rank lattice inclusion; for 514 it also uses the
finite conformal extension (5). For617 both factors are rational
and their stress tensors sum to that of \(E\), so ordinary
semisimplicity and finite graded multiplicities give finiteness.

Set
\[
 T=\widehat H\otimes D_0\subset W\subset E.           \tag{7}
\]
Its simple summands appearing in \(E\), and hence in \(W\), have
quantum dimensions in
\[
 \begin{array}{c|c}
 \text{hosts}&\text{dimension field for these summands}\\ \hline
 372,483,579&\mathbb Q\\
 514,617&\mathbb Q(\sqrt5).
 \end{array}                                       \tag{8}
\]
For the first line, all level-one affine and lattice modules are
invertible. For514, \(B_{2,2}\) has dimensions
\(1,1,2,2,\sqrt5,\sqrt5\); the other factors are pointed.
For617, \(A_{1,3}\) has dimensions \(1,\varphi,\varphi,1\),
and \(A_{2,2}\) has three simples of dimension one and three
of dimension \(\varphi\), with
\(\varphi=(1+\sqrt5)/2\). The remaining factor is pointed.

Finite local-extension indices therefore satisfy
\[
 [E:W]
 =\frac{\operatorname{qdim}_T E}
        {\operatorname{qdim}_T W}
 \in\mathbb Q(\sqrt5).                              \tag{9}
\]
But \(3I=(39+9\sqrt{13})/2\) does not lie in that field.
This contradicts (1).

Thus all five residual-c=1 current hosts are excluded under the
stated fixed-algebra assumptions. The argument handles arbitrary
rational torus placements and does not carry a gap in possible
all-current Sugawara charges over to unrelated proper denominators.

## 5. Remaining scope

The result removes the full-current hosts372,483,514,579,617,
not every denominator row they witness: some rows have other
possible full-current hosts. The bookkeeping must be recomputed
by deleting these host witnesses before inferring row exclusions.

The eight previously unanalysed hosts reduce to0,496,613, whose
full-current charge is six and whose residual ambient charge is
two. Hosts379 and600 still have the separate nongroup/nonproper
restriction loopholes discussed in their earlier reports.
This is a conditional structural restriction on an E8 realization;
the required realization of the physical H3 chain remains unproved.
