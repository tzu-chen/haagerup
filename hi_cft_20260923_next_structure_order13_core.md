# An actual order-thirteen rational core inside U

23 September 2026. Put A=T tensor K(sl2,13), with conformal vector
omega_A=omega_T+z and central charge 22/5. The exact certificate
`hi_cft_20260923_next_structure_core_extension.json` proves that U
contains an order-thirteen simple-current extension A_L of A.

The producer ran under the permanent safe launcher with a 2 GiB
address cap. It took 6.72 seconds and used 40060 KiB peak RSS. All
arithmetic was in Q(sqrt(13),sqrt(-3)); no floating spectral test was
used. Its certificate stores all relevant sparse vectors and source
hashes.

## Exact fields that force the extension

Write s=omega_B-omega_T-z=q+r. The producer checked this identity
against both independently stored residual stresses and checked the
c=18/5 Virasoro identity. Its kernel in the certified 120-dimensional
S2 has dimension 25. The known A_2 has dimension 15. Among the ten
additional vectors are six one-dimensional joint eigenspaces with

\[
 s_1v=0,\quad z_1v=\frac{12}{13}v,\quad
 (\omega_T)_1v=\frac{14}{13}v,\quad p_1v=\frac23v,
\]

at Cartan weights

\[
 (\pm1,\pm5),\qquad (0,\pm8).
\]

Each vector is explicitly in S2, hence in U. These six states are the
complete top characters of the two conjugate simple-current sectors
with T charge j=5 and j=-5.

Indeed, the H charge modulo 13 identifies the T pointed charge j. Its
Fibonacci label must be 1: the tau sector at j=5 has lowest weight
31/65, whose difference from 14/13 is not an integer. In the ALY
parafermion labeling 0<=b<i<=13, the actual lowest weight is

\[
 \frac{i(13-i)}{390}+\frac{b(i-b)}{13}.
\]

The only modules with lowest weight 12/13 are (i,b)=(13,1),(13,12),
the two inverse parafermion simple currents. Since 12/13<1, this
energy cannot be a positive-level descendant of another module.
The formula, one-dimensional parafermion tops, and simple-current
fusion are reviewed in
[Arakawa–Lam–Yamada, Sections 2.4 and 6](https://arxiv.org/html/1701.06229).

The four other extra S2 states have z energy 22/13 and T energy 4/13,
at Cartan weights (±1,±3). That energy alone does not distinguish the
PF13 simple current from its i=10 noninvertible sector. They are not
needed to establish the order-thirteen extension.

## Locality fixes a single charge line and multiplicity one

The charge convention here is j=H mod13. In this convention the
pointed parts of Rep(T) and Rep(PF13) have quadratic forms

\[
 q_T(j)=-j^2/13,\qquad q_{PF}(k)=-k^2/13\pmod1.
\]

The earlier convention q_T(j_old)=3j_old^2/13 is equivalent under
j=6j_old. PF charge reversal k -> -k remains a harmless labeling
choice. The witnessed generator has charge (j,k)=(5,1) or (5,-1).
Both have order 13 and integral conformal spin.

For completeness, consider D=ker_U(s_1). Unitarity and positivity of
the commuting Virasoro stress s identify this kernel with its vacuum
sector. It is a unitary VOA with conformal vector omega_A. A is regular,
so D is an algebraic direct sum of ordinary A-modules. Because its
omega_A grading is the ambient grading, finite-dimensional graded
pieces and the finite list of A irreducibles make this a finite
extension. Its weight-zero space is one-dimensional.

In a connected unitary extension, invertible simple constituents occur
with multiplicity at most one and their support is a subgroup. One
can see this directly from the invariant pairing and associativity:
a nonzero invertible constituent J pairs nontrivially with J*, their
product has a nonzero vacuum coefficient, and the resulting inverse
forces multiplication by J to carry every supported invertible line
isomorphically to the next. The vacuum line is one-dimensional.
Equivalently, this is the pointed part of the connected commutative
separable algebra object supplied by the VOA extension correspondence.

The subgroup has trivial twist because D is integer graded. Hence its
support is isotropic for -(j^2+k^2)/13. The two maximal isotropic
subgroups are the lines k=5j and k=-5j. They intersect only at zero.
The witnessed nonzero current forces one full line L, and both sign
choices cannot coexist: they would generate all Z13 squared, including
nonintegral-spin sectors. Thus a witnessed spectral vector cannot hide
a mixture of both PF charge choices in D.

The sum of the thirteen invertible A constituents on this actual line
is therefore a vertex subalgebra

\[
 A_L=\bigoplus_{(j,k)\in L} T_{1,j}\otimes PF_{0,k}\subset U.
\]

It is PCT stable, each constituent occurs once, and multiplication
between constituent lines is nonzero. This proves the actual embedding,
not just existence of an abstract extension. Reversing PF charge if
necessary, we may label its line k=-5j. The usual simple-current
extension theorem makes A_L strongly rational; see
[ALY, Theorem 2.4](https://arxiv.org/html/1701.06229).

## Category and low grades

The PF13 category splits as SO(3)_13 tensor its pointed Z13 factor.
Condensing L removes the hyperbolic pointed Z13 squared factor, giving

\[
 \operatorname{Rep}(A_L)\simeq
       \mathrm{Fib}\boxtimes\mathrm{SO}(3)_{13}.
\]

The thirteen added simple-current sectors have lowest weights
0 at j=0 and, for |j|=1,...,6, respectively 4,3,2,4,2,3. Thus
(A_L)_1=A_1 has dimension four, while (A_L)_2 has dimension 25.
The certified zero-s-energy S2 space is exactly (A_L)_2 by dimension.
This does not assert that the full kernel D has no further sectors.

The next note `hi_cft_20260923_next_structure_order13_top_bound.md`
uses this actual core to prove h<=17/10<2 for every simple U-module.
The existence of A_L and its category do not identify Rep(U).
