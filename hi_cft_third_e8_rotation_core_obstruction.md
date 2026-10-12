# Rotation cores force an ordinary finite-group lattice frame

This note strengthens two branches of the abelian E8 argument. It does not
assume that the residual Haagerup channel is proper. It uses the same
unitary finite-index VOA/conformal-net compatibility and vacuum-preserving
conditional expectation as the previous current-host arguments.

Let E=V_E8, let W be the putative fixed algebra with irrational index
[E:W]=3(13+3 sqrt(13))/2, and suppose W1 is six-dimensional and abelian.
The actual rank-six radical lattice V_M is contained in W. Its orthogonal
rank-two lattice commutant in E is V_L. Put D=Com(V_M,W), so D1=0.

The conclusions are:

- D cannot contain the 120-degree Heisenberg rotation fixed algebra H²^C3,
  for any binary lattice L.
- D cannot contain H²^SO(2), for any binary lattice L.

No parity or minimum-norm assumption is used in the first conclusion.
The second proof below does not need either assumption, although its
application from the low-weight classification has them.

## 1. A rotation-stable sublattice preserves the relevant expectation

First let R be a finite-order rotation which is rational on L tensor Q,
and assume H²^<R> is contained in D. Define

\[
 N=\bigcap_j R^j L.
\]

Then N is an even integral, R-stable finite-index sublattice of L.
It is a sublattice, not a possibly nonintegral sum of rotated lattices.

For nonzero real momentum p, its stabilizer under a rotation group is
trivial. Hence F_p restricts irreducibly to H²^<R>, and two such modules
are equivalent exactly on the same rotation orbit. This is the
finite-orbifold theorem of
[Dong--Ren--Yang, Theorem7.4 and Corollary7.5](https://arxiv.org/pdf/2302.09474).
The Heisenberg vacuum restriction is a direct sum of its distinct
rotation eigenspaces, disjoint from the nonzero-Fock orbits.

If p belongs to N, its entire rotation orbit belongs to N. Therefore
V_N, considered inside V_L, is a sum of complete isotypic components of
the H²^<R>-module V_L. It has no omitted copies in V_L outside V_N.
The vacuum-preserving orthogonal projection E_D onto D is a module map
for H²^<R> and thus preserves V_N. Consequently

\[
 E_D(V_N)=D_N:=D\cap V_N.
\tag{1}
\]

The expectation E from E onto W restricts first to V_L and then to V_N.
Its Pimsner--Popa lower bound restricts at each step. Thus D_N is a
finite-index unitary subalgebra of V_N. This is an actual preserved
expectation, not an assertion that arbitrary subfactor joins preserve
an index bound.

## 2. Compact quantum Galois produces an ordinary group fixed algebra

The lattice torus T_N has fixed algebra H². A finite-order lift of R,
together with this torus, generates a compact Lie group K of unitary
automorphisms of V_N, with

\[
 V_N^K=H²^{\langle R\rangle}\subset D_N\subset V_N.
\]

There is no need to choose a particular splitting of K into torus and
rotation factors. Unitary subalgebras are simple and orthogonally
complemented. The corrected compact Galois theorem therefore gives

\[
 D_N=V_N^G
\tag{2}
\]

for a closed subgroup G of K; see
[Dong--Mason, Theorem3(A)](https://arxiv.org/pdf/math/9804103).
The hypotheses cannot be dropped for arbitrary nonunitary intermediate
subalgebras.

The group G is finite. Otherwise compact Schur--Weyl decomposition
contains infinitely many distinct simple V_N^G components in V_N,
incompatible with the finite-index rational inclusion in (1).
On the net side the corresponding fixed inclusion has infinite index
for an infinite compact group. The finite-group orbifold is rational
within the unitary net/VOA bridge already assumed here.

## 3. Ordinary ambient lattice branching contradicts the E8 index

Only ordinary V_N modules appearing in ambient lattice branching are
needed. Every simple ordinary lattice module has dimension one.
When restricted to V_N^G, each simple constituent has dimension

\[
 [G:G_X]\dim(\pi),
\tag{3}
\]

an integer, where pi is a projective irreducible stabilizer
representation. Equation (3) is
[Dong--Ren--Xu, Theorem4.4, equation(4.3)](https://arxiv.org/pdf/1507.03306)
with the ordinary lattice quantum dimension equal to one.
No claim is made about dimensions of general twisted-sector modules;
they need not be integers.

Now V_M tensor V_N is a full-rank lattice subVOA of E8 and therefore has
finite ordinary lattice branching. Set

\[
 T=V_M\otimes D_N\subset W\subset E.
\]

Every simple T constituent appearing in E, and hence in W, has integer
dimension by (3), since the V_M factors are pointed. Thus both
qdim_T(E) and qdim_T(W) are positive integers. Index multiplicativity
gives

\[
 [E:W]=\operatorname{qdim}_T(E)/
       \operatorname{qdim}_T(W)\in\mathbb Q,
\]

contradicting the prescribed irrational index. This excludes every D
containing a rational finite-rotation Heisenberg core, without properness
of the restricted channel.

## 4. The C3 conclusion also covers noncommensurate rotations

Let R have order three. If a nonzero p and Rp both belong to L, they
span the rational plane and R²p=-p-Rp, so R is rational on L tensor Q.
Hence, if R is not rational, each nonzero C3 orbit meets L at most once.

In that case the finite-orbifold decomposition is multiplicity-free
on all charged Focks. A D containing H²^C3 either includes the entire
F_p or none. Inclusion plus unitary conjugation supplies F_-p, and the
ground-state OPE regenerates the nonzero current p(-1)1, violating D1=0.
The two nontrivial zero-charge eigenspaces also have currents. Thus
D=H²^C3, which has infinite index and infinitely many ordinary modules.
This is impossible in the finite-index setup.

The rational case was excluded by Sections1--3. The C3 conclusion is
therefore independent of the determinant squareclass of L.

## 5. The SO(2) conclusion reduces to a rational finite rotation

The direct neutral-bilinear interpolation in the
[SO(2) proof](hi_cft_third_heisenberg_SO2_obstruction.md) is independent of
the lattice determinant. It makes each nonzero F_p irreducible over
H²^SO(2), and separates these modules from the zero-charge Heisenberg
components using their lowest antisymmetric weight-three eigenvalue.
Consequently the zero-charge projection P_H preserves D.

Compact Galois then gives D intersect H² = H²^G for a closed
G contained in SO(2). A finite-index D has some nonzero charge support:
otherwise its character ratio to V_L vanishes. In a fixed charged
isotypic block its lowest vector is a finite shell combination
v=sum c_p e^p. The projected OPE with its unitary conjugate contains

\[
 \sum_p |c_p|^2
       \exp\left(\sum_{m\ge1}p(-m)z^m/m\right).
\tag{4}
\]

All coefficients of (4) lie in H²^G. Setting higher oscillator variables
to zero and using independence of finite exponential sums forces the
nonempty frequency support to be G-invariant.

A finite nonzero frequency set cannot be invariant under SO(2), so
G=C_n. Invariance under the full C_n, rather than just a subset of its
orbit, means some nonzero p and all its rotations belong to L.
For n at least three these span the plane, forcing the rotation to be
rational on L tensor Q. Equivalently its characteristic polynomial
has rational trace 2cos(2pi/n), so n is3,4, or6. The cases n=1,2 are
already rational rotations. Each possibility is excluded by
Sections1--3, because D contains H²^C_n.

This also explains why an irrational cyclic rotation cannot support a
finite-index charged extension: the positive exponential support
argument, not a guessed classification of all lattice subalgebras,
rules it out.

## Scope

The stable-sublattice isotypic argument, the restricted expectation,
compact Galois, and the ordinary-sector dimension argument passed an
independent read-only audit by the uniform agent. The positive-support
extension to SO(2) was independently checked by both the root and
uniform agents. The finite groups occurring here are subgroups of a
torus extended by a cyclic group, hence solvable; finite solvable
orbifold regularity from
[Carnahan--Miyamoto](https://arxiv.org/abs/1603.05645)
also supplies a VOA formulation of the finite group step, alongside
the stated net bridge.

The proof excludes the two specified Heisenberg cores in an abelian
six-current E8 fixed algebra with irrational full index. It leaves open
other residual subalgebras, including a lone Miura W3 core in the
squareclass-three branch. The expectation compatibility is an explicit
premise throughout. No assertion that the restriction of an extreme
ambient channel stays extreme is used.
