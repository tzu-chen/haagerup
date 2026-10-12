# A concrete host0 lattice candidate inside E6+A2

There is an explicit primitive rank-two lattice inside
\(B=E_{6,1}\otimes A_{2,1}\subset E_{8,1}\) whose discriminant form
supports the categorical Haagerup quotient. Its orthogonal
rank-six lattice admits a rootless sublattice of index three,
consistent with the proposed six-dimensional fixed weight-one space.

**Subsequent compatibility audit excludes this particular embedding
for the categorical realization in section4.** Although its abstract
pointed local extension has the right dimension, that extension
cannot fit inside the specified E8 inclusion: it requires three
times as many pointed branches as the ambient algebra contains.
The exact obstruction is in section5. The lattice and categorical
calculations remain useful, but are not an unexcluded model proposal.

This is a concrete algebraic candidate, not a constructed VOA action
or a continuum identification. Its exact lattice certificate was
run by the root agent under the128MiB safe launcher and passed all
15 checks:
[checker](hi_cft_third_e8_host0_lattice_check.py),
[results](hi_cft_third_e8_host0_lattice_results.json).
It uses standard-library rational arithmetic and the240 E8 roots;
no tensor or eigensolver job was used.

## 1. Primitive lattice and the intrinsic alpha action

Use the usual coordinate realization
\[
 E_8=\{x\in\mathbb Z^8:\sum_i x_i\in2\mathbb Z\}
 \cup\{x\in(\mathbb Z+\tfrac12)^8:\sum_i x_i\in2\mathbb Z\}.
\]
Choose the \(A_2\) roots on the first three coordinates.
The index-three \(E_6\oplus A_2\) sublattice is characterized by
\[
 x_1+x_2+x_3-3x_8\equiv0\pmod3.                     \tag{1}
\]
The expression is integral for every \(x\in E_8\).

The root agent's explicit vectors are
\[
 v=(0,0,0,2,1,1,0,0),\qquad
 w=(2,2,2,0,0,0,0,0).
\]
They belong to \(B\), and
\[
 (v,v)=6,\quad(w,w)=12,\quad(v,w)=0.
\]
Let \(L=\mathbb Zv\oplus\mathbb Zw\).
It is primitive in \(E_8\). Indeed, a vector \(av+bw\) in \(E_8\)
cannot have half-integral coordinates because its seventh and
eighth coordinates vanish. Its fifth coordinate forces
\(a\in\mathbb Z\), while its first coordinate allows only
\(b\in\tfrac12\mathbb Z\). The even coordinate-sum condition
\(4a+6b\in2\mathbb Z\) then forces \(b\in\mathbb Z\).

Therefore, with
\[
 K=L^\perp\cap E_8,
\]
both lattices have determinant72. Also \(K\subset B\):
orthogonality to \(w\) forces \(x_1+x_2+x_3=0\),
which rules out half-integral E8 coordinates, and equation(1)
then holds. Thus \(V_L\) lies pointwise in the intrinsic-alpha
fixed algebra. In this example
\[
 D_E=\operatorname{Com}(M(1)^6,E)=V_L
 =\operatorname{Com}(M(1)^6,B)=D_B.                 \tag{2}
\]
The distinction between the E8 and B commutants, which matters
for some other hosts, does not create an index-three ambiguity here.

## 2. The rank-six complement and a rootless lattice

The complement splits as an \(A_2\) on the first three coordinates
and a rank-four lattice in the last five. Write the latter as
\[
 (x_4,x_5,x_6,x_7,x_8)=(a,b,-2a-b,s,t),
 \qquad -a+s+t\equiv0\pmod2.
\]
Its norm is
\[
 5a^2+4ab+2b^2+s^2+t^2.
\]
A basis of the full \(K\) is
\[
\begin{split}
 &(1,-1,0,0,0,0,0,0),\quad(0,1,-1,0,0,0,0,0),\\
 &(0,0,0,1,0,-2,1,0),\quad(0,0,0,0,1,-1,0,0),\\
 &(0,0,0,0,0,0,1,1),\quad(0,0,0,0,0,0,1,-1).
\end{split}                                      \tag{3}
\]
Its determinant is72. Its norm-two roots form
\(A_2\oplus A_1^3\), with12 roots in total.

The maximal lattice \(V_K\) cannot simply be assumed to lie in
\(W\): it has root currents in addition to the six Heisenberg
currents. That would contradict the full weight-one dimension six.
Mason's completion supplies a rootless sublattice, not necessarily
all of \(K\).

There is an explicit allowed rootless choice:
\[
 f:K\to C_3,\qquad
 f(x)=x_2+2x_3+x_5+x_7\pmod3,\qquad M=\ker f.        \tag{4}
\]
On the \(A_2\) roots the three coordinate phases are \(0,1,2\).
On \(e_5-e_6\) and \(e_7\pm e_8\) the value is nonzero.
Thus \(f\) is nonzero on every root of \(K\), and
\[
 [K:M]=3,\qquad \det M=648,\qquad M\text{ is rootless}.           \tag{5}
\]
The exact certificate checks all12 roots, in addition to the
displayed argument.

Equation(5) is an existence statement for a candidate lattice
inside the hypothetical \(W\). It does not prove that the unknown
Haagerup operation fixes this particular \(M\).

## 3. A general bound on the actual radical lattice

Here the index bound can be established without classifying all
quantum operations of a lattice VOA. Let \(E_W:B\to W\) be the
vacuum-preserving expectation of the putative rank-two action,
with Pimsner–Popa lower bound \(I^{-1}\), where
\[
 I=1+d^2=(13+3\sqrt{13})/2<12.
\]
It fixes the entire rank-six Heisenberg algebra.

The expectation preserves \(V_K\). To see this, it intertwines
the Heisenberg action and the conformal grading. A lattice ground
state of charge \(\lambda\in K\) has the minimum energy
\(\lambda^2/2\) in that Heisenberg charge sector. There is no
positive-energy transverse state at that same minimum, and its
multiplicity is one. Hence the expectation acts by a scalar on
the ground state and on all its Heisenberg descendants.

Every unitary subVOA of \(V_K\) containing the full Heisenberg
algebra is \(V_{M'}\) for a sublattice \(M'\subset K\):
the Fock modules have distinct charges and occur with multiplicity
one, while the nonzero leading vertex products and Hermitian
conjugation make the retained charge set a subgroup.
The finite-index bound forces it to have full rank. Restricting
the same expectation therefore gives
\[
 [K:M']=[V_K:V_{M'}]\leq I<12,
 \qquad [K:M']\leq11.                              \tag{6}
\]
If the full \(W_1\) is six-dimensional then \(M'\) is rootless.

This conclusion does not require the restricted operation to
be proper. In particular it does not identify \(I\) with
\([K:M']\), and does not force \(I-1\) to be a group order.
The explicit index-three lattice (4) passes this new necessary
condition. The integrability agent independently checked the
minimal-energy charge argument, inherited expectation bound,
and subgroup/full-rank conclusion. The vacuum-preserving
conditional-expectation/subnet compatibility remains a premise.

## 4. The discriminant metric and the categorical candidate

The ambient \(D=V_L\) is pointed, with
\[
 A_L=L^*/L=C_6\times C_{12}.
\]
Its three-primary subgroup is generated by \(v/3,w/3\), with
\[
 q(a,b)=\frac{a^2+2b^2}{3}\pmod1.
\]
This is the hyperbolic \(C_3^2\) metric group,
equivalent to \(Z(\mathrm{Vec}_{C_3})\).
The two-primary complement \(\mathcal P_8\) has group
\(C_2\times C_4\), with generator weights \(3/4,3/8\).
Its topological central charge is two. Equivalently it is the
metric group of the rank-two lattice \(\operatorname{diag}(2,4)\).
Indeed,
\[
 u=(v+w)/3,\qquad t=(2v-w)/3
\]
have norms2 and4 and are orthogonal, giving an abstract
index-three overlattice of \(L\). This overlattice is not
contained in the chosen primitive E8 embedding.

Thus
\[
 \operatorname{Rep}D
 \simeq Z(\mathrm{Vec}_{C_3})\boxtimes\mathcal P_8.   \tag{7}
\]
The near-group category with group \(C_3^2\) and multiplicity nine
has global dimension \(9I\), and is Morita equivalent to
\(\mathrm{Hg}\boxtimes\mathrm{Vec}_{C_3}\).
Its existence is recorded in
[Evans–Gannon, Table2](https://arxiv.org/abs/1208.1500).
Tensoring it with the fusion category underlying
\(\mathcal P_8^{\rm rev}\) supplies the categorical central inclusion
of \((\operatorname{Rep}D)^{\rm rev}\) required for a proper
rank-two quotient. The predicted residual modular category is
\[
 \operatorname{Rep}D_0
 \simeq Z(\mathrm{Hg})\boxtimes\mathcal P_8,           \tag{8}
\]
with central charge two modulo eight and global dimension
\(72I^2\).

The reverse on the neutral central inclusion matters. Omitting
it would incorrectly give the conjugate pointed central charge
for \(D_0\).

For the rootless \(M\) in (4), the proposed conformal algebra
\(T=V_M\otimes D_0\) would have
\[
 [E:T]=[E:V_M\otimes D]\,[D:D_0]=216I.
\]
Hence a compatible \(W\) with \([E:W]=3I\) would require
\[
 [W:T]=72.                                         \tag{9}
\]
These are consistent categorical dimensions, not a constructed
local extension. One must still find an actual condensable
algebra with the required branching and weight-one space.
In particular, blindly extending \(V_M\) back to \(V_K\)
would reintroduce the forbidden root currents.

## 5. The compatible-embedding obstruction

Assume the specific modular category in (8), an actual local
inclusion \(D_0\subset D\) of index \(I\), and the required
\(W\subset B\subset E\). Let \(M'\) be the actual fixed radical
lattice, and put \(n=[K:M']\); it need not be the example with \(n=3\).
Then \(T'=V_{M'}\otimes D_0\) would satisfy
\[
 [W:T']=24n.                                      \tag{10}
\]

The nontrivial Haagerup-center dimensions are
\[
 1+3d,\quad 2+3d,\quad 3d,
\]
all with strictly positive coefficient of \(d\). Tensoring with
the pointed categories \(V_{M'}\) and \(\mathcal P_8\) does not
change these dimensions. Positivity and irrationality therefore
force every constituent of the rational-dimension algebra
\(W/T'\) to be pointed. There are eight possible residual
invertible objects, one for each object of \(\mathcal P_8\).

Let \(A\) be the connected local algebra for \(D_0\subset D\).
For an invertible residual object \(g\), its free induction has
\[
 \operatorname{End}_A(g\otimes A)
 =\operatorname{Hom}(g,g\otimes A)
 =\operatorname{Hom}(1,A)=\mathbb C,
 \qquad \operatorname{qdim}_A(g\otimes A)=1.
\]
Thus it is simple. If \(g\) appears in the restriction of an
ordinary \(D\)-module \(Y\), reciprocity forces
\(g\otimes A\simeq Y\), and the occurrence has multiplicity one.
In particular each of the eight \(g\)'s can occur in only one
ordinary \(D\)-module. Locality is derived from its appearance
in \(Y\); it is not assumed for every freely induced module.

Primitivity of the orthogonal \(K,L\) pair in the unimodular E8
lattice gives exactly \(n\) distinct \(V_{M'}\) branches for
each ordinary \(V_L\)-module in \(E\). Therefore the entire
pointed \(T'\)-part of \(E\) has dimension at most \(8n\).
It cannot contain a pointed algebra of dimension \(24n\):
\[
 \operatorname{qdim}_{T'} W=24n>8n
  \geq\operatorname{qdim}_{T'}(E_{\rm pointed}).       \tag{11}
 \]
This contradiction is independent of the choice of rootless
radical lattice.

The integrability agent independently checked the free-induction
endomorphism calculation, the locality qualification, multiplicity
one, and the primitive-lattice branch count. This excludes the
specific modular-category realization (8) in the displayed
embedding. It does not exclude every fusion category satisfying
the abstract stabilizer-nine condition, or every host0 embedding.

An abstract Lagrangian algebra of dimension \(24n\) in the pointed
factor can still exist, and the usual VOA extension theorem can
produce an abstract extension once an actual nice \(D_0\) exists.
The missing requirement is compatibility with \(W\subset B\);
the dimension argument proves that compatibility fails here.

## 6. The remaining realization problem

The unresolved host0 route must change the displayed ambient
embedding, the categorical realization, or both. A possible
alternative has nontrivial intrinsic alpha on \(D_E\), so that
\(D_B=D_E^\alpha\) is an index-three sublattice theory.
One must still supply:

- an actual unitary finite-index \(D_0\subset V_{\operatorname{diag}(6,12)}\)
  carrying the proper rank-two Haagerup quotient, with the
  representation category(8);
- a compatible local extension embedding in \(B\), with exactly
  six weight-one currents;
- an identification of an appropriate coset/full CFT with the
  physical H3 chain and its independent shift symmetry.

The fusion category and lattice data alone do not provide the
required VOA action, its operator products, or the continuum map.
The [ordinary-fixed-algebra obstruction](hi_cft_third_e8_pointed_hosts.md)
also shows that iterated ordinary finite-group orbifolds of the
ambient lattice cannot supply the desired fixed algebra.
