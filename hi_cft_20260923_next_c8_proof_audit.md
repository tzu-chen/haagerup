# Independent audit of the c=8 proof boundary

23 September 2026. This note reviews the preceding construction without
rerunning its numerical or exact producers. It is a mathematical and
source-level audit, not an independent recomputation certificate.

The object is the unitary conformal subVOA

\[
 U=\langle A_{1,1}\otimes A_{1,39},\omega_B,u\rangle
 \subset B=V_{E_6\oplus A_2}.
\]

The exact generators, PCT operation and finite-span certificates are in
`hi_cft_20260923_c8_construction_report.md`. The subsequent report claims
an identified copy of \(K(\mathfrak{sl}_2,13)\), and consequently
\(C_2\)-cofiniteness of the actual generated U. The qualifications about
properness and rationality in that report are necessary.

## 1. The parafermion identification has the right finite proof target

Write \(a=W^3\), \(b=a_1a\), \(d=a_1b\). Inspection of the producer and
saved logs confirms that the stated gate list covers every potentially
nonzero singular coefficient in the pairs \((a,a),(a,b),(a,d)\):

* The recursive second-order poles defining b and d are definitions.
* The remaining upper poles are exactly the sixteen assertions listed
  in `hi_cft_20260923_proof_pf13_upper_poles.json`. The original log
  records fifteen completed assertions; the continuation records the
  sixteenth. No unfinished calculation is counted as a zero residual.
* The \(a_0b\) relation is independently calculated in the lattice.
* The \(a_1d\) decoupling polynomial is independently calculated and
  compared with the parafermion formula after changing generators.
* The \(a_0d\) expression follows algebraically from the other checked
  coefficients and self-skew symmetry. It is not inferred merely from
  central charge or the W(2,3) coupling.

The iterate identities in the identification note have the correct
signs. In particular,

\[
(a_1a)_n s=a_1(a_ns)-a_0(a_{n+1}s)
                 +a_{n+1}(a_0s)-a_n(a_1s).
\]

This gives the remaining generator pairs by the noncommutative Wick
formula, retaining its integral terms. The reductions must be understood
in increasing total conformal degree, not by pretending normal products
are commutative. In this application the decoupling polynomial removes
the potentially new weight-six generator. A common graded universal
algebra with these closed OPEs therefore maps onto the two simple
algebras. Its degree-zero space is one dimensional, so its simple graded
quotient is unique. Additional null relations do not invalidate this
argument. This is consistent with the degenerate nonlinear-conformal-
algebra discussion in [Linshaw, Section 3.1](https://arxiv.org/html/1710.02275).

The PCT-stable primary line, reality of the stress and ambient
translation identity are essential to viewing the generated lattice
subalgebra as a simple unitary VOA with this conformal grading. They are
explicitly included in the gate files. No structural gap was found in
this finite-presentation route. An independent implementation of the
mode calculations would strengthen reproducibility but is not a missing
mathematical hypothesis of the stated argument.

## 2. The positive-stress argument proves finiteness, not semisimplicity

Suppose a unitary CFT-type VOA V has
\(\omega_V=\sum_{i=1}^N c_i e_i\), with every \(c_i>0\), where each
\(e_i\) is the real quasiprimary stress of a regular vertex subalgebra.
The stresses need not commute. For
\(v=(v_n)\) in the maximal weak module in the graded completion,
regularity makes \((e_i)_1\) locally finite on v. Its action on every
finite ambient grade is Hermitian. A polynomial annihilating v for this
operator gives a finite real set of possible eigenvalues on all v_n;
let its maximum be M_i. Consequently

\[
n\|v_n\|^2
 =\sum_i c_i\langle v_n,(e_i)_1v_n\rangle
 \leq\left(\sum_i c_iM_i\right)\|v_n\|^2.
\]

Thus v has bounded grade support. The completion criterion gives
\(C_2\)-cofiniteness. This is precisely the mechanism in
[Dong–Wang, proof of Theorem 3.1](https://arxiv.org/html/1005.1709).

For the present U the compact affine-current group acts by unitary
automorphisms of U. Its orbit of a weight-two vector lies in a finite
dimensional real vector space. The Haar average is in the convex hull
of this compact orbit and hence is an actual finite convex combination.
The saved positive averaged-stress identity therefore has the form
required by the preceding argument. No joint diagonalization of the
different stresses is assumed or needed.

Regularity of these subalgebras controls weak modules under restriction.
It does not give invariant positive inner products on every U-module.
Using it to claim complete unitarity or rationality would add an
unproved step.

## 3. A small strengthening: finite branching for every lattice sector

Conditional only on the established \(C_2\)-cofiniteness of U, every
irreducible ordinary B-module restricts to a **finite direct sum of
irreducible unitary ordinary U-modules**.

Proof. Lattice B-modules have invariant positive inner products,
finite-dimensional conformal grades and spectra bounded below. A
graded U-submodule has a graded invariant orthogonal complement,
because U is PCT-stable and the adjoints of its modes are again linear
combinations of its modes. Taking the lowest nonzero grade and an
irreducible invariant part there, then proceeding to orthogonal
complements, decomposes the restriction into irreducible ordinary
unitary modules. There are only finitely many irreducible U-module
types by \(C_2\)-cofiniteness. For a fixed type its multiplicity is
bounded by the dimension of the B-module grade at its fixed lowest
weight. Thus there are only finitely many summands. This applies to
all nine discriminant sectors of \(V_{E_6\oplus A_2}\).

This statement does not classify the summands or show that every
U-sector occurs in these restrictions. In an extension problem,
nonlocal induced sectors can fail to come from ordinary modules of
the extension; orbifolds already illustrate that obstruction.

## 4. Rationality descent remains a separate theorem to prove

The latest inspected version of
[McRae, On rationality for C2-cofinite vertex operator algebras](https://arxiv.org/html/2108.01898)
is v3, 22 January 2026. Its introduction explicitly states that descent
of strong rationality along finite direct-sum branching is still an
open general problem. It cannot be used to close the present argument.

[McRae, On semisimplicity of module categories for finite non-zero index
vertex operator subalgebras](https://arxiv.org/html/2103.07657)
does give a descent criterion. Besides strong rationality of B and
\(C_2\)-cofiniteness of U, it requires rigidity of the U-module tensor
category, nonzero categorical dimension of B, and a splitting onto U.
Here the orthogonal projection supplies the U-module splitting.
Rigidity and categorical dimension are not supplied by that projection
or by finite branching. Unitarity of the known restrictions does not
establish these conditions for all generalized U-modules.

Two concrete sufficient paths are available:

1. Identify a strongly rational conformal frame contained in U and
   then its unitary finite extension. **Update from the continuation:**
   the proposed PF17 and diagonal SU(2) coset route through the exact
   stresses of charges 32/19 and 182/95 is now excluded. Their zero
   modes have irrational eigenvalues on B1, which rules out every
   strongly rational extension with those particular stresses. See
   `hi_cft_20260923_next_c8_irrational_axes.md`. A different frame or a
   rational extension of their sum remains possible.
2. Determine the finite-dimensional Zhu algebra A(U) and prove it
   semisimple. McRae's Main Theorem 3 then proves rationality. A
   faithful finite-dimensional *-representation of A(U) would suffice,
   but the zero-mode action on the 80 current complement is not yet a
   representation of A(U): that requires proving it is an actual
   lowest-weight U-space first.

## 5. Why the current complement is not yet a properness proof

Let b1 be the 80-dimensional complement to the six retained currents
in B1. Exact zero-mode irreducibility gives the useful dichotomy
\(U=B\) or \(U_1=K_1\). On b1 the known generators have no modes
that lower grade to the vacuum. This does not yet make b1 the top
space of a U-module.

The obstacle is explicit. If a,b are weight-two generators, their
simple-pole state \(a_0b\) has weight three. Its lowering modes are
commutators involving a mode acting on a state already raised by
another mode. The original annihilation statement about b1 does not
control those raised states. Continuing this argument requires an
all-weight invariant module or a closed strong-generator presentation.
The exact finite span at weight three and the numerical span at weight
four do not provide that presentation. \(C_2\)-cofiniteness says a finite
strong-generating set exists, but supplies neither its explicit weight
bound nor the missing annihilation relations.

An all-weight orthogonal projection commuting with every mode of the
specified generators, fixing the vacuum and killing b1, would prove
properness immediately. Equivalently one can construct an invariant
positive-energy U-submodule generated from b1 with no vacuum. Finite
branching alone does not distinguish these alternatives: U=B itself
already has all the established finiteness properties.

No numerical job was launched for this audit. The permanent one-job,
6 GiB address-space, 8 GiB RSS, 32 GiB host-reserve and two-thread rules
remain in force; the September 15 memory exception is expired.
