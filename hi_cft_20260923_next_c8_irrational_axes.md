# Exact obstruction to rational extensions of the two remaining stresses

23 September 2026. The certificate
`hi_cft_20260923_next_stress_current_spectra.json` replaces the proposed
PF17 and diagonal-coset interpretations of the last two stresses by an
exact negative result. This note independently audits the producer and
the mathematical implication; it does not rerun the computation.

Let q and r denote the mutually commuting PCT-real Virasoro vectors in
`hi_cft_20260923_proof_remaining_axes.json`, with central charges
32/19 and 182/95 respectively. They lie in the constructed U and hence
in \(B=V_{E_6\oplus A_2}\).

**Theorem.** Neither q nor r is the conformal vector of a strongly
rational vertex subalgebra of B. In particular, q cannot extend inside
B to \(K(\mathfrak{sl}_2,17)\), and r cannot extend there to the
strongly rational diagonal SU(2) coset at levels (13,4;17).

## Exact input

The zero mode of a weight-two stress is its mode 1. The producer
constructs q1 and r1 on the actual full 86-dimensional current space
B1, using the eight Heisenberg currents and 78 lattice roots. It splits
this space by the two retained Cartan charges, asserts that every block
is invariant, and computes each characteristic polynomial over the
exact field \(\mathbb Q(\sqrt{13},\sqrt{-3})\).

For q1 the block of Cartan weight (0,2), of dimension seven, has
characteristic polynomial

\[
 \frac{(19t-11)(19t-4)^2(19t-3)(57t-5)
       (361t^2-266t+9)}{2681615217}.
\]

Thus q1 has eigenvalues

\[
 \boxed{\frac{7+2\sqrt{10}}{19},\qquad
        \frac{7-2\sqrt{10}}{19}}.
\]

For r1 the block of Cartan weight (0,6), of dimension three, has
characteristic polynomial

\[
 \frac{(95t-17)(361t^2-247t+16)}{34295}.
\]

Thus r1 has eigenvalues

\[
 \boxed{\frac{13+\sqrt{105}}{38},\qquad
        \frac{13-\sqrt{105}}{38}}.
\]

The discriminants are \(76^2\cdot10\) and \(19^2\cdot105\),
respectively, so no rational-number recognition or tolerance is
involved. The same calculation on the identified PF13 stress is a
control: all its characteristic factors are linear over the rationals.

The characteristic-polynomial routine uses the exact recurrence
\(C_k=MB_{k-1}\), \(a_k=-\operatorname{tr}(C_k)/k\),
\(B_k=C_k+a_kI\), beginning with \(B_0=I\). It also asserts
\(B_n=0\). This is the usual Faddeev–LeVerrier recurrence in
characteristic zero. The mode engine is asked only for target grade
one, so this test neither truncates a candidate generated space nor
depends on its weight-three or weight-four ranks.

## Proof of the obstruction

Suppose A is a strongly rational vertex subalgebra of B with conformal
vector q. Restricting B's vertex operators makes B a weak A-module.
This restriction is legitimate even though q differs from the ambient
conformal vector: the Jacobi and truncation axioms for a weak module
are inherited from B.

Since A is of CFT type, rational and C2-cofinite, it is regular, so B
is an algebraic direct sum of irreducible ordinary A-modules. This is
[Abe–Buhl–Dong, Rationality, Regularity, and C2-cofiniteness](https://arxiv.org/abs/math/0204021).
Every such module has q1-spectrum \(h+\mathbb Z_{\geq0}\), with
\(h\in\mathbb Q\), by the conformal-weight rationality theorem of
[Dong–Li–Mason, Modular invariance of trace functions in orbifold theory](https://arxiv.org/abs/q-alg/9703016).
Consequently every eigenvalue of q1 on B must be rational. The displayed
quadratic factor contradicts this. The proof for r is identical.

The argument does not require finite multiplicity of B as an A-module,
an a priori conformal grading of B by A, or rationality of U. It uses
regularity specifically to handle the restriction as a weak module.

## Scope and consequence

This result rules out the two particular rational-frame components
suggested by their central charges. It also rules out every alternative
strongly rational extension **with either of these exact conformal
vectors** inside B. The Virasoro vectors themselves remain valid.

It does not rule out a different rational conformal frame in U, a
rational extension of the **sum** q+r, or rationality of U with its
ambient stress. Strongly rational VOAs can contain Virasoro subalgebras
whose representations have irrational weights. Nor does it invalidate
the existing C2-cofiniteness proof, which uses the separately identified
PF13, Potts and affine subalgebras and their conjugates.

The broader lesson for this calculation is concrete: before a costly
primary-field or OPE identification for a candidate rational stress,
test its exact zero-mode spectrum on B1. One irrational eigenvalue is
already a complete obstruction to a strongly rational extension of
that stress in the ambient VOA.

## Auxiliary check on the discarded full-frame guess

There is an independent conditional dimension-field obstruction to
the full guess
\(T\otimes\mathrm{PF}_{13}\otimes\mathrm{PF}_{17}\otimes
\mathrm{GKO}(13,4;17)\) being a conformal frame of a Haagerup-double
realization. Parafermion module dimensions are
\(\sin((j+1)\pi/(k+2))/\sin(\pi/(k+2))\), as proved by
[Dong–Wang](https://arxiv.org/abs/1411.7429). The diagonal-coset
dimensions are products of the corresponding affine dimensions; the
order-two label identification has no fixed points here because 13
and 17 are odd. See [Lin, Sections 4–5](https://arxiv.org/html/1910.03945).

Together with \(\operatorname{Rep}T\simeq\mathrm{Fib}\boxtimes
\mathcal C(\mathbb Z_{13},3j^2/13)\), all these dimensions lie in
\(F=\mathbb Q(\zeta_{1140})\). Any finite local extension has global
dimension \(\operatorname{Dim}(F\text{-frame})/d^2\), where d is the
dimension of its algebra object, so its global dimension still lies in
this number field. The dimension formula is the standard local-module
formula in [Davydov–Mueger–Nikshych–Ostrik](https://arxiv.org/html/1009.2117).
But the Haagerup double has dimension

\[
 \left(3+3\left(\frac{3+\sqrt{13}}2\right)^2\right)^2
   =\frac{1287+351\sqrt{13}}2.
\]

This is outside F: 13 is unramified in the cyclotomic field of conductor
1140, while \(\mathbb Q(\sqrt{13})\) has discriminant 13. The integer
factor 13 in the dimension of the pointed lattice factor does not
introduce \(\sqrt{13}\) into the module-dimension field. This auxiliary
argument is conditional on the full frame identifications; the exact
current-spectrum obstruction above directly disproves them for the
specific fields under study.
