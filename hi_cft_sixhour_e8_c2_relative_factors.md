# Relative Ising/Potts factors in the remaining exact-two branches

The proper-current construction gives a test for an additional chiral
spin-two field. It does not, from the observed epsilon dimension and its
nonzero cubic coupling alone, exclude these exact-c=2 branches.

A subsequent [categorical obstruction](hi_cft_kA2_hypergroup_obstruction.md)
does exclude a specific stronger completion: the residual ambient
K(A2,2) cannot carry the proper rank-two Haagerup hypergroup action with
the stated rational fusion-category realization. The conditional factor
and sewing identities below do not establish that completion. A
nonproper restricted operation, a different fixed subalgebra, or a
different continuum realization remains outside that obstruction.
The [host600 ambient commutant](hi_cft_e8_host600_commutant.md) has also
been identified as an Ising–rank-one-lattice extension; its Ising-times-C3
fusion ring gives a [parallel proper-action obstruction](hi_cft_ising_c3_hypergroup_audit.md).
Index-field arguments separately exclude finite ordinary group-fixed
residual algebras in [379](hi_cft_e8_ordinary_fixed_obstruction.md) and
[600](hi_cft_e8_host600_ordinary_fixed.md). These do not exclude
nonproper operations with nongroup fixed algebras or the eight other
full-current hosts in the necessary exact-two union.

This note concerns the conditional E8 construction, not an established
identification of the H3 chain. Let W be the proposed unitary Haagerup-fixed
charge-eight VOA inside E8 level one, let H be its full current-generated
subalgebra, and let A be a charge-six current denominator. Set

\[
 C=\operatorname{Com}(A,W),\qquad
 R=\operatorname{Com}(A,H),\qquad D=\operatorname{Com}(H,W).
\]

Then R and D commute conformally inside C, with
\(T_C=T_R+T_D\). This does not assert that C is their tensor product.
The host placements and their scope are recorded in
[the current-denominator audit](hi_cft_sixhour_e8_c2_current_audit.md) and
[the exact host rows](hi_cft_sixhour_e8_c2_current_rows.json).
The four host379 ambient current cosets have now also been identified
as the same lattice VOA \(V_{\sqrt2 A_2}\) in
[a separate proof](hi_cft_e8_c2_ambient_lattice.md). That proof keeps
ambient local-module spectra separate from a possible smaller fixed VOA.

| Current host | c(H) | c(R) | c(D) |
|---|---:|---:|---:|
| 600: A1,1 squared times A1,4 times B2,1 | 13/2 | 1/2 | 3/2 |
| 379: A1,4 times G2,1 times two Heisenberg currents | 34/5 | 4/5 | 6/5 |

R belongs to the Haagerup-fixed algebra by construction. To call its fields
jointly Haagerup- and intrinsic-shift-invariant, an additional premise is
needed: the intrinsic order-three shift preserves R as a conformal
subalgebra. A shift lift preserving H and A is sufficient. An arbitrary
automorphism of C need not preserve a selected conformal subalgebra.

There is a useful alternative test. If the complete chiral weight-two
space has dimension two, a unitary order-three symmetry fixes its total
stress and must act trivially on the one-dimensional real orthogonal
complement. It then fixes T_R. For relative Ising or Potts, the kernel
of the complementary L0 contains no proper integer-graded extension of
R, so fixing T_R also preserves R. Conversely, if shift moves T_R, its
nontrivial real order-three orbit needs two dimensions in addition to
the invariant total stress. There must then be at least three chiral
weight-two states. The extra fields can have intrinsic shift charges
plus/minus one and appear around shifted lattice momenta; the present
zero-shift p2 window cannot exclude this alternative. This argument
assumes shift acts as a unitary chiral-algebra automorphism.

## 1. The relative algebras

For host600, a nontrivial unitary c=1/2 conformal algebra contains the Ising
Virasoro VOA. Its only nonvacuum irreducible lowest weights are 1/16 and 1/2.
Neither can occur in an integer-graded bosonic extension. Thus R is the
Ising VOA. This uses the unitary minimal-model spectrum and fusion rules;
the general minimal-model and VOA module framework is reviewed in
[Dong–Lin, Unitary vertex operator algebras](https://arxiv.org/abs/1308.2361).

For host379, the actual simultaneous embeddings sharpen R from a possible
c=4/5 Virasoro algebra to the full Potts algebra
\(K(A_1,3)=L(4/5,0)\oplus L(4/5,3)\). The four denominator placements are:

| E8 denominator row | Denominator inside host379, after removing its external A1,4 and two external Heisenberg currents |
|---:|---|
| 4 | a Cartan of G2,1 |
| 97 | A1,1 and the Cartan of its A1,3 commutant |
| 197 | diagonal A1,4 inside A1,1 times A1,3 |
| 285 | the long-root A2,1 inside G2,1 |

Here is why the external A1,4 factor is indeed removed. The internal
index-four A1 in G2 is the diagonal of the index-one and index-three A1
factors. Its adjoint branching contains no singlet, so its Lie centralizer
in G2 is zero. Using it alone in row4 leaves centralizer rank only three,
too small for the four required abelian directions. In row97 it leaves no
commuting level-one A1. In row197 the two commuting level-four A1 factors
must be the external factor and this internal diagonal. The A2 of row285
lies in G2 and has no G2 Lie centralizer, forcing the level-four A1 to be
external. The required abelian directions then fill the remaining Cartan
centralizer; their orthonormal basis does not change the commutant.

The four cosets agree as follows.

* The short-root A1 in G2 at level one has induced level three. Its
  parafermion algebra embeds in K(G2,1). Both have charge 4/5; positivity
  makes the difference of their conformal vectors vanish. The six Potts
  module weights are 0, 2/5, 1/15 twice, and 2/3 twice, so there is no
  nonvacuum integer-graded extension. Hence K(G2,1)=K(A1,3).
* Under the conformal A1,1 times A1,3 subalgebra, the G2,1 vacuum decomposes
  as (0,0) plus (1,3), using affine highest-weight labels. Selecting the
  A1,1 vacuum removes the latter branch. Removing the remaining Cartan
  gives K(A1,3).
* The diagonal GKO coset of the vacuum branch is M(5,6). The extra (1,3)
  branch supplies the (r,s)=(4,1) module, of weight three, and produces
  precisely its Potts extension.
* The nonvacuum A2,1 modules carry weights outside the A2 root lattice and
  have no zero Cartan charge. Thus the Cartan commutant in G2,1 equals its
  A2,1 commutant, which is again Potts.

The short-root parafermion inclusion is the result of
[Dong–Wang, Section4](https://arxiv.org/html/0909.3872).
The six Potts modules and its weight-three extension are described in
[Feingold–Milas, Section2](https://people.math.binghamton.edu/alex/3PottsCEJMfinal.pdf).
The G2/SU3 branching is also given in
[Yamaguchi, Section2.3](https://arxiv.org/pdf/hep-th/0112004).
The conformal embeddings used here are consistent with the primary
embedding table already cited in
[the 72/35 construction note](hi_cft_sixhour_e8_72over35.md).
The host379 identification above was independently checked by the
CFT-constraints agent on September15; no new numerical calculation is
used in this argument.

## 2. A forced extra spin-two field

Write c=cR+cD=2 and normalize the total stress state as
\(\widehat T=\sqrt{2/c}\,T_C\). The orthogonal combination

\[
 X=\frac{c_D T_R-c_R T_D}{\sqrt{c\,c_Rc_D/2}}
\]

has unit two-point coefficient, zero overlap with the total stress, and
is a Virasoro primary of weights (2,0). The central terms cancel in its
OPE with T_C; L1 annihilates both stress states. Its conjugate chirality
exists as well. Under the shift-retention premise, X is jointly invariant.
Thus these branches require at least two chiral states of weights (2,0),
not merely a second descendant in the total vacuum module.

Host379 also supplies the Potts weight-three primary. An order-three
automorphism preserving Potts fixes it: that algebra is generated by its
stress and its one-dimensional real weight-three primary space, on which
a unitary automorphism acts by a sign. This is a further invariant
spin-three test, conditional on the same retention premise.

The energy-density Fourier source O2 applied to the vacuum principally
creates the total stress. Its overlap with X vanishes at the fixed point.
Consequently a nearly saturated O2 spectral weight in one state does not
exclude the extra X. Its energy degeneracy, topological label, or a
different OPE source must be examined.

## 3. What epsilon and its cubic coupling imply

Assume epsilon is a nondegenerate Hermitian scalar with
\(h_\epsilon=\bar h_\epsilon\simeq0.13\), and that the retained relative
VOA acts on the full local CFT. Nondegeneracy here concerns the complete
relevant left/right weight space, not an incomplete numerical selection
of eigenvectors. Its state then has definite relative module labels;
the positive commuting D energy excludes relative modules whose lowest
weight already exceeds h_epsilon.

For Ising, the only possible relative labels are the vacuum and sigma.
Since sigma times sigma has no sigma channel, any sigma label on either
chirality forces the epsilon self-cubic to vanish. A nonzero cubic
therefore forces epsilon into the relative vacuum on both sides. It
remains possible for D, of charge 3/2, to supply its observed dimension.

For Potts, only the vacuum and the two sigma modules of weight 1/15 fit
below h_epsilon. A sigma self-cubic is allowed, so the cubic alone does
not settle this case. Instead use Hermiticity and nondegeneracy. The two
sigma modules are contragredient and distinct; sigma times sigma does
not contain the vacuum. A state with a definite sigma label therefore
has zero self two-point conformal block and cannot be a nonzero
Hermitian field by itself. A Hermitian linear combination with sigma
dagger needs both independent equal-weight states in the Hilbert space.
Nondegeneracy rules that out, including when the maximal VOA extends
R times D: its restriction to rational R still resolves those two
distinct modules. Under this premise epsilon again has the relative
vacuum label. The module and fusion data follow from
[Ai–Dong–Jiao–Ren](https://arxiv.org/html/1412.8154).

This argument cannot be replaced by the claim that a single real
numerical eigenvector proves nondegeneracy. Nor does it apply if the
intrinsic symmetry projects the two relative modules in a way that
removes the assumed retained Potts chiral algebra.

For comparison, retaining only Virasoro M(5,6) would leave relative
weights 0,1/40,1/15,1/8 below approximately0.13. The h=1/8 field is
(r,s)=(1,2), and the h=1/40 field is (2,2); their self-triples vanish by
minimal-model fusion parity. The h=1/15 field remains an allowed
self-triple. The full Potts identification is therefore material.

## 4. A fixed epsilon–extra-stress coupling and a sewing test

For epsilon in the relative vacuum, the usual stress Ward identity gives

\[
 \frac{C_{\epsilon\epsilon X}}
      {C_{\epsilon\epsilon\widehat T}}
 =-\sqrt{\frac{c_R}{c_D}}
 =\begin{cases}-1/\sqrt3,&\text{host600},\\
 -\sqrt{2/3},&\text{host379}.
 \end{cases}
\]

Signs depend on the choice of phase for X; the squared ratio is invariant.
The formula follows directly from hR=0 and hD=h_epsilon and needs no
knowledge of the residual theory D.

There is a useful pants version that avoids fitting h_epsilon. Put
\(a_j=A_{00j}/A_{000}\), \(b_j=A_{\epsilon\epsilon j}/A_{000}\), and
\(E=A_{\epsilon\epsilon0}/A_{000}\), with normalized external states.
For the same geometry and outgoing chirality,

\[
 a_X=0,\qquad
 b_X=-\sqrt{c_R/c_D}\,(b_T-Ea_T). \tag{1}
\]

The subtraction removes the outgoing stress Schwarzian. Indeed its
remaining plane Ward contribution is
\(E\,e^{2H(x)}\Delta_\epsilon/\sqrt{2c}\), while a primary X transforms
with the same outgoing derivative factor and the OPE coefficient above.
Equation(1) is a leading continuum sewing identity, not an exact lattice
relation. General branch corrections, state leakage, and a different
continuum sewing map remain possible. It also requires a common
conformal cylinder Hamiltonian; independently propagating factors with
unequal velocities would change how lattice states realize this premise.

There is a controlled strengthening. If the junction functional factorizes
between R and D, the R insertion sees the same vacuum external states for
both the vacuum pair and the epsilon pair. Consequently its connected
amplitude vanishes. The exact algebraic relation in that factorized
functional is

\[
 b_X-Ea_X=-\sqrt{c_R/c_D}\,(b_T-Ea_T). \tag{2}
\]

This statement allows arbitrary separate junction changes in R and D.
In particular, a leading epsilon branch in its relative-vacuum ground
channel has the form identity_R times epsilon_D and preserves(2).
Thus this slowly decaying branch need not be removed by fitting its
coefficient. A sum of coupled R/D branch insertions need not factorize;
mixed descendants, bulk coupling, and imperfect external-state
identification are not controlled by this observation. The relation and
the normalization were independently checked by the strange-correlator
agent. The helper saves b−Ea for every mode, including X candidates whose
finite-size vacuum overlap is nonzero.

Within a clean two-dimensional T/X span, and with a aligned with the
canonical total stress, the ratio of the squared orthogonal and parallel
components of b−Ea relative to a is cR/cD.
This version tolerates unitary mixing of those two states. Adding unrelated
finite-energy eigenstates to that span is not justified by the identity.

Explicitly, write z=b−Ea and use the positive Hermitian inner product of
normalized outgoing states. Then

\[
 r=\frac{\|z-a(a^\dagger z)/\|a\|^2\|^2}
 {|a^\dagger z|^2/\|a\|^2}=\frac{c_R}{c-c_R},
 \qquad c=c_R(1+1/r). \tag{3}
\]

This does not depend on the choice of orthonormal basis in that two-state
space. Different factor velocities can split its lattice energies without
invalidating the equal-time factorized overlap identity, provided both
states are identified and their leading vacuum-sewing direction is the
canonical total stress. Nonuniversal leg collars can affect the two
factors differently, and finite a_X can rotate that direction. Thus an
explicit pair must be supplied, and a small finite-ring value of(3) is not
an identified central charge.

In particular, the factorized-junction strengthening of(2) does not by
itself strengthen(3). In the orthonormal factor-stress basis,
factorization gives z_R=0 and z_D unrestricted, whereas separate vacuum
junction corrections allow arbitrary a_R,a_D. Direct projection then
gives r=|a_R|²/|a_D|². This equals c_R/c_D only with the additional
total-stress alignment condition. Thus independent factor corrections
can preserve the physical X/T connected relation while biasing the
vacuum-direction estimator. Agreement of a with another lattice probe
such as O2/gap is a useful consistency check, not a proof that either has
reached the physical total-stress direction.

The separate standard-library reader
[hi_cft_e8_extra_stress_pairs.py](hi_cft_e8_extra_stress_pairs.py) evaluates
(3) for user-specified pairs only. In the existing L15 topology report,
the invariant Yrho eigenvalue d occurs at indices2,5,33 of the saved40
p2 modes. Index2 is the selected total-stress candidate and index5 is
only0.0732196091 higher in energy; index5 is therefore a possible partner
to test, not an established additional stress.

[hi_cft_e8_extra_stress_sewing.py](hi_cft_e8_extra_stress_sewing.py) prepares
this measurement from existing caches. The old overlap script computed
all40 epsilon-pair amplitudes at L15 but saved only the selected T
component; all40 vacuum amplitudes were saved. The new helper constructs
two representative-space sources once and streams one eigenvector column
at a time. It requires agreement with every saved vacuum amplitude and
with the old selected epsilon amplitude. It never expands the L15 basis
and does not solve a new eigenproblem. Its outputs explicitly retain
alpha-neutral versus Haagerup-invariant and finite-state-identification
distinctions.

## 5. What is not forced

Retaining an Ising chiral subalgebra does not force a standalone Ising
sigma bulk field of dimension1/8. For example the bosonic even algebra
of four free Majoranas, SO(4) level one, extends Ising times SO(3) level
one by the product of their fermion modules. This integral-weight
extension confines sigma times the other vacuum; the spinor instead
pairs the Ising sigma with the SO(3) spinor and has chiral weight1/4.
This is a direct simple-current locality counterexample to inferring
standalone relative-factor fields merely from chiral retention.

A full tensor-product local CFT is a stronger assumption and does contain
the standalone factor fields. A unique self-conjugate scalar is fixed
by an odd ordinary symmetry that preserves the factor, but its
Haagerup-vacuum label still cannot be inferred merely from the existence
of the factor's vacuum VOA. Thus the absence of additional relevant
jointly invariant scalars is not, without those extra premises, an
exclusion of these E8 branches.

Finally, the ambient commutant in E8 can retain additional algebras and
modules which are removed from the Haagerup-fixed commutant in W.
Ambient module-weight tables cannot silently be imposed on C. The
established positive consequence here is the extra stress sector and
its conditional coupling test, not a determination of c or of D.

## 6. The D5 charge65/31 branch and the72/35 distinction

The same test applies to the definite ambient coset
\(\operatorname{Com}(A_{1,60},D_{5,1})\) in
[the D5 principal-coset audit](hi_cft_sixhour_d5_principal_coset.md).
The principal A1 acts on the ten real fermions as spin4 plus a singlet.
The nine-dimensional real spin4 representation lies in SO9 and has
index \(4\cdot5\cdot9/3=60\), independently giving the level60
embedding in B4,1. The singlet Majorana has its own Ising stress.
The level-one orthogonal algebras' fermion realization is described in
[Lahtinen–Ardonne](https://arxiv.org/html/1504.07044).

More explicitly, the even ten-fermion algebra restricts to the even
nine-fermion algebra times Ising, with an additional odd-times-odd
summand. Taking the A1 commutant retains the two commuting even stress
algebras, whether or not the odd-times-odd summand produces a further
extension. Therefore

\[
 c_R=\frac12,\qquad
 c_D=\frac92-\frac{3\cdot60}{62}=\frac{99}{62},\qquad
 c=\frac{65}{31},\qquad r=\frac{31}{99}. \tag{4}
\]

The last ratio needs the same unique-Hermitian-epsilon and nonzero-cubic
premises used for Ising above. An inherited Haagerup action and shift
preserving this Ising factor are additional physical premises, not supplied
by the ambient fermion realization. Equation(3) with cR=1/2 then compares
31/99 for this branch against1/3 for exact two.

The raw nine-fermion volume has weight9/2 and is a finite-dimensional A1
singlet. Multiplication by the singlet fermion gives total weight five,
suggesting an odd-times-odd extension field. It is not by itself an
affine-singlet proof: a positive current mode can contract two occupied
fermions and act nontrivially. An actual coset field requires an
affine-highest projection or a separately resolved branching coefficient.
The stress-factor and ratio conclusions do not depend on this suggestion.

At charge72/35 there is a different scope point. The ambient construction
in [the72/35 note](hi_cft_sixhour_e8_72over35.md) retains tricritical
Potts times K(A2,2). Inside its current host H379, however, the external
factor is only A1,4. The relative current coset is therefore initially
Virasoro M(6,7)=A1,1 times A1,4 over diagonal A1,5. Its weight-five
tricritical-Potts extension comes from the ambient A2,1 module outside
H and is not automatically retained in the Haagerup-fixed W.

If the extended tricritical-Potts factor is retained and epsilon is in its
vacuum module, then cR=6/7, cD=6/5 and r=5/7. With only Virasoro M(6,7),
the low relative weights allowed below h_epsilon approximately0.13 are
0,1/56,1/21,5/56. Fusion forbids the self-cubics of1/56 and5/56, but
the self-dual1/21 module has an allowed self-cubic. Thus the previous
epsilon premises alone do not force hR=0 in this Virasoro-only case.

For a known nonzero relative weight hR, the more general Ward ratio is

\[
 \frac{C_{\epsilon\epsilon X}}{C_{\epsilon\epsilon\widehat T}}
 =\frac{c\,h_R-c_R h_\epsilon}
 {\sqrt{c_Rc_D}\,h_\epsilon}.
\]

For the72/35 Virasoro alternative hR=1/21, its squared ratio is
\(r=(5/7)[1-8/(35\Delta_\epsilon)]^2\), rather than5/7. It is about
0.0104 at Delta_epsilon=0.26. This illustrates why the relative module
label is an essential part of an OPE-based central-charge inference.

## 7. Executed small-ring diagnostics and their current limitation

The parent's coordinated runs passed the literal3+3 and3+6 controls and
the original-kernel6+6 control. The6+9 production reproduced every saved
vacuum amplitude within8.73e-15, with measured peak resident memory
0.293GiB. The original amplitude kernel's epsilon entries agree as well.
These checks validate the numerical contraction, not the conformal
interpretation of the chosen states.

The explicit candidates are the first two Haagerup-invariant p2 states
at each length, fixed using the independent topology data. The resulting
pair diagnostics are:

| Input lengths | Parent pair indices | r | Conditional c, assuming relative Potts vacuum |
|---|---|---:|---:|
| 3+6 | 4,8 | 0.6787476382 | 1.9786413020 |
| 6+6 | 5,7 | 0.6355818120 | 2.0586892589 |
| 6+9 | 2,5 | 0.6097375281 | 2.1120399567 |
| 3+12 | 2,5 | 0.5840897154 | 2.1696526045 |

The raw amplitudes are saved in the corresponding
[3+6](hi_cft_e8_extra_stress_sewing_3plus6.json),
[6+6](hi_cft_e8_extra_stress_sewing_6plus6.json),
[6+9](hi_cft_e8_extra_stress_sewing_6plus9.json), and
[3+12](hi_cft_e8_extra_stress_sewing_3plus12.json) reports.
The L15 explicit-pair outputs are
[6+9](hi_cft_e8_extra_stress_pairs_6plus9.json) and
[3+12](hi_cft_e8_extra_stress_pairs_3plus12.json).

There is a material same-parent partition dependence: the last two rows
differ by about0.058 in the conditional c. The first three rows also use
different shapes x=1/3,1/2,2/5 and cannot be treated as a fixed-shape
extrapolation. The value near2.11 is therefore a conditional diagnostic,
not a new central-charge determination.

Although the partner carries only0.3–0.4percent of the pair's vacuum
sewing norm, its interference changes the inferred r substantially.
The individual connected partner/T squared ratios are about0.541,0.487,
0.467 for the first three rows; these are different from the
basis-invariant ratios above. Retaining phases and the full pair is
necessary. A separate streamed comparison of vacuum sewing with the
complex O2/gap vector is prepared in
[hi_cft_e8_extra_stress_direction.py](hi_cft_e8_extra_stress_direction.py).
Division by each excitation gap is essential when the factor velocities
differ. At leading order the two vectors agree up to a global phase
and the known factor B(x); matching their component magnitudes alone
would not establish this direction test.

The executed
[complex O2/gap comparison](hi_cft_e8_extra_stress_direction_N15.json)
passes all40 source-weight checks within1.39e-16 and uses0.217GiB peak
resident memory. In the explicit pair2,5, direction infidelities are
1.08e-5 for6+9 and5.31e-6 for3+12. The best proportionality magnitudes,
divided by their predicted B, are0.89014 and0.88478. The direction is
therefore well supported by two independent sources, while an approximately
11percent amplitude correction remains. Using O2/gap instead of a to
define the total-stress direction gives conditional Potts estimates
2.12998050 and2.18280618, respectively. The same-parent geometry dependence
remains. All40-mode figures in that report are diagnostics, not estimates
from a40-dimensional stress space.

There is a separate absolute-normalization check. In a clean pair define
\(c_{\mathrm{vac}}=8\|a\|^2/B^2\). Combining this with r would infer
\(c_R=c_{\mathrm{vac}}r/(1+r)\). The results for3+6,6+6,6+9 are:

| Parent length | Pair vacuum Ward value | Inferred relative charge |
|---:|---:|---:|
| 9 | 1.54645009 | 0.62525738 |
| 12 | 1.78693122 | 0.69439570 |
| 15 | 1.91125264 | 0.72394564 |

The inferred relative charge moves toward Potts4/5, but atL15 it is still
about9.5percent below it. Thus the ratio and the absolute Ward amplitude
have not reached a common conformal normalization. In particular, the
uncorrected raw-O2 direction happens to produce2.09997688 for6+9; selecting
that appealing number after observing it would be unjustified. Its
velocity-dependent interpretation and the alternative direction choices
must remain visible.

An extra factor stress also changes the interpretation of the earlier
three-stress cumulant failure. For independently normalized geometric
stress insertions whose mixtures on the three legs are
\(v_i=(v_{iR},v_{iD})\), the Ward cumulant yields

\[
 c_{\mathrm{mix}}=
 \frac{(\sum_s c_s v_{1s}v_{2s})
       (\sum_s c_s v_{1s}v_{3s})
       (\sum_s c_s v_{2s}v_{3s})}
      {(\sum_s c_s v_{1s}v_{2s}v_{3s})^2}.
\]

It equals c for the canonical total stress on every leg, but depends on
all three mixtures in general; sign-changing pair contractions can even
make it negative. Thus an energy eigenstate containing X is not
automatically a Virasoro stress suitable for the one-stress formula.
This observation is not a quantitative explanation of the earlier H3
failure: those triples use the poorly separated incomingL6 states, and
the modest mixing now observed atL9–15 has not been shown to reproduce
their cumulants. A factorized candidate needs its full stress space,
not only the earlier span of one T and one antiholomorphic T.
