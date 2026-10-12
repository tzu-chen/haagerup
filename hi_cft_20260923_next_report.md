# Haagerup identification: six-hour continuation

Research window: 2026-09-23 04:31:06–10:31:06 UTC. This is a living
record, not a claim that the identification problem is solved. The root
coordinates one research computation at a time under the permanent safe
launcher. The expired September 15 memory exception is not used.

## Current proof boundary

**Latest consolidated mathematical result:** the explicit U is strongly
rational, and either U=B or it has the Haagerup index, standard modular
data, and the unique gamma=0 full character vector. All rank-four
alternatives and higher rank-six multiplicities have now been excluded.
Using the cited exhaustive computer-assisted classification of small
pivotal fusion categories also gives Rep(U)=Z(H3) in the proper branch;
the classification logs were not independently replayed. The full
dependency chain is in `hi_cft_20260923_next_conditional_identification.md`.
**U!=B remains unproved.** The chronological updates below record the
intermediate proof boundaries and are superseded by this statement.

**Computational update, 09:05 UTC:** the finite-prime normal weight-four
span closed at6007, and singular products supplied three independent
extra directions of Cartan weights(0,2),(0,0),(0,-2). The tested union
has rank6010. Thus the proposed weight-three strong-generation route
has not passed. The revised route adds an exact weight-four right-sl2
triplet and tests output weights through five. These modular ranks are
lower bounds, not characteristic-zero normal-span upper bounds; the
full exact containment identities are still required. The first633
singular tests in the source-bound continuation supplied no direction
beyond6010. A separate integer-matrix checker is continuing the full
3220-target membership test with the same distinction between modular
evidence and exact proof.

**Update, 09:28 UTC:** the additional weight-four triplet is now built
exactly over Q(sqrt(13),sqrt(-3)). All18 current identities and6 Virasoro
lowering controls passed. All90 A_nP4 checks with output weights1,2,3
also passed exactly, in163.27 seconds at0.267GiB sampled RSS. The30
weight-four A1P4 targets passed finite-prime containment; that is not
an exact containment certificate. The native exact solver has passed
its arithmetic controls and the first three full weight-four identities;
a serial bulk calculation is now checking the2898 necessary A0P3
relations. The first weight-five normal-span pilot retained493 independent
columns and2255/2901 processed tasks at its600-second bound, with none
of its three selected targets yet contained. Its incomplete checkpoint
does not prove failure of characteristic-zero closure. A fresh containment
check at09:35 found that all three selected targets already lie in that
saved493-column finite-prime span: the earlier zero count was stale
because the pilot rechecked only after a100-column rank increase. The
new checkpoint records3/3 containments and is frozen for exact lifting.
The exact lifting subsequently passed all three identities at ranks82,161,250
in111.73 seconds at0.649GiB sampled RSS. Complete sparse residuals vanished,
so these are characteristic-zero containments for the u-family. They do not
imply the other weight-two generator families by a weak-generation shortcut;
an independent audit found that proposed shortcut circular.
The serial exact weight-four run has meanwhile verified1088 of its2898
relations without a failed identity; the remaining relations are pending.

The length15 internal-alpha-twist scalar run also passed its complete
seam, Hermiticity and smaller-size regression controls in19.68 seconds
at1.040GiB sampled RSS. The lowest scalar has descendant-normalized
dimension1.016196734; the lowest spin-one candidate is1.138352505.
These extend the finite-size diagnostic, not a continuum identification.

The explicit unitary conformal subalgebra
U=<A1,1 x A1,39, omega_B, u> of B=V_(E6+A2) has central charge eight.
Prior certificates identify its rational core T (central charge 14/5),
its PF13 subalgebra (central charge 8/5), and a positive decomposition
of its conformal vector into stresses of regular subalgebras. The last
identity proves C2-cofiniteness. These arguments survived an independent
source and mathematical audit in this window. No independent recomputation
of every prior OPE was claimed.

**Update, 05:04 UTC:** a new argument now proves strong rationality of U.
The positive-stress identity proves that the vacuum is projective in
the finite category of generalized modules. Grothendieck–Verdier duality
then gives a split evaluation onto the vacuum for every nonzero object.
Finite abelian category structure and right-exact fusion give exponential
endomorphism growth. The Etingof–Penneys rigidity theorem applies; rigidity
and projectivity of the tensor unit imply semisimplicity. Two independent
mathematical/source audits agree on this argument. This uses the already
certified positive-stress and C2-cofiniteness inputs.

Properness U != B remains unproved. Exact branching and the equivalence
Rep(U)=Z(H3) now follow conditionally as stated above. Neither the finite spans
1,6,120,956,6010 nor finite branching by itself proves those statements.
The physical chain's exact c=2 continuum identification also remains open.

**Update, 05:44 UTC:** an actual order-thirteen simple-current core
A_L of central charge 22/5 is now established inside U. Its complete
fourteen-module top table sharpens the universal lowest-weight bound
to h<=17/10<2. An independent exact arithmetic checker verified the
table and the nonnegative dual inequality. Consequently the precise
all-weight fork is now B=U or B=U plus a single irreducible module X
with lowest weight one and an 80-dimensional top. Properness is still
unproved, and no Haagerup index or categorical identification follows
from this fork alone.

**Update, 06:10 UTC:** all four mixed lattice sectors have exact
irreducible 81-dimensional tops under certified U fields. Together
with h<2 this proves that their full restrictions to U are simple.
Conditional on properness, the holomorphic E8 extension therefore
reduces the possible fusion category to rank four or six. Rank six
has the Haagerup-shaped quadratic fusion rule with an undetermined
integer multiplicity m>=1. The target is m=1; this has not been proved.
The rank-four near-group alternatives m=0 and m=2 are excluded, while
m=3 and m=6 remain. The ordinary-group obstruction for m=2 uses the
minimum dimension of A4-fixed currents in E8, not a numerical fit.

The core A_L admits no proper integer-graded conformal extension and
is its own double commutant in the ambient lattice theories.

**Update, 06:42 UTC:** the full ambient residual commutants are now
identified at all weights, using an independently audited E8 lattice
two-neighbor and the uniqueness of the commuting affine pair:

    Com(A_L,V(E8)) = Com(A1,13,F4,1 tensor A1,1),
    C_B := Com(A_L,B)
         = Com(A1,13,A2,1 tensor A2,2 tensor A1,1).

The diagonal A1 in the second line has levels 4+8+1. The E8 residual
has thirteen weight-two fields; its order-three fixed algebra C_B has
five. Thus the earlier five-versus-thirteen comparison distinguishes
these two ambient commutants; it does not exclude the F4 description
of the E8 commutant. An actual regular conformal frame, followed by
McRae's coset theorem, proves both residual cosets strongly rational.
Mirror duality then determines

    Rep(C_B) = Fib^rev tensor SO(3)_13^rev tensor P(Z3 squared),

with 126 simple modules. These are results about the ambient residual
cosets, not an identification of Rep(U). The remaining properness
question is equivalent to whether Com(A_L,U) is proper in C_B.

**Update, 07:00 UTC:** a new conditional character result controls
the full weight-two space. Starting with the exact 80-dimensional
orthogonal current complement, certified U-mode words have rank1250
in B2 over a good split prime. An independent checker verifies the
rank, rational starting projection, source hashes and word references.
If U is proper these words lie in X2; since dim B2=1370 and U already
contains the120-dimensional S2, this forces U2=S2 and dim X2=1250.
The separate residual-current map has rank3 and kernel exactly
span(q,r), so the proper residual C_U has dim(C_U)2=2.
Neither conditional result chooses between U=B and U proper.

**Update, 07:24 UTC:** four standard ribbon-category alternatives now
fail the six-current character test: both orientations of the familiar
Z3+3 and Z3+6 centers. Harmonic-theta polar cancellation gives, respectively,
dim U1=15+A+10B, 14+42A, 8+A, and 5+12P, with nonnegative integral
top multiplicities. None equals six. The calculation uses actual modular
matrices and the exact identity chi_B=chi_U+chi_X. This does not eliminate
every categorification with these fusion rules: the available C*-category
classification and the needed general unitarity/exhaustion statements
have not been bridged. Higher multiplicity in the rank-six case also remains.

A second, direct proof of C2-cofiniteness uses orthogonal energy bounds
for the regular subalgebras in the positive stress identity. It supplies
the conservative bound (U/C2(U))_n=0 for n>16748. Independent audit agrees
with the module spanning argument. This bounds possible strong generators,
not excursions of words in the original weak generators. In fact the
frozen exact grade-three calculation already shows that currents and S2
have strong span of dimension634, while the certified S3 has dimension956:
at least322 additional strong-generator classes occur at weight three.

At the conformal-net level, finite-index descent identifies a completely
rational residual subnet and preserves the ambient/residual inclusion
index. The Henriques--Tener reverse module construction, together with
regularity of U, supplies an ordinary unitary U-module for each irreducible
net sector. A tensor/braiding comparison has not been established, so
these statements do not identify the net index with the VOA quantum
dimension or close the categorical unitarity gap.

## New results in this window

**Update, 08:34 UTC:** an independently audited strong-generation lemma
reduces an all-weight properness certificate to exact singular-product
closure through weight four. The322 weight-three generator classes have
provenance in A0S2 plus normal descendants. The iterate identity and a
filtered Wick induction then reduce their pairwise products to products
with the weight-two generators. Virasoro commutators further reduce the
new exact burden to A0P3, together with the lower S2 closure controls.
This is a sufficient criterion; it has not yet been satisfied. A bounded
finite-prime pilot is constructing the complete normal weight-four span
and testing these products. Modular containment alone will not certify
characteristic-zero containment. An exact GMP field adapter passed1294
field-oracle checks and32 lattice-mode comparisons, providing a faster
arithmetic path for the remaining exact relations.

**Update, 08:39 UTC:** all3970 exact lower-closure and quasiprimary
identities passed in77.875 seconds at0.229GiB sampled group RSS. This
includes every charged and neutral A0/A1 product against S2, the current
controls and the Virasoro prerequisite. Source-bound exact linear
relations are saved in `hi_cft_20260923_next_structure_lower_closure.sqlite`.
The new native FLINT K-linear solver separately passed100 regular-
representation controls, eight exact solve/residual controls and singular
refusal; it has not yet certified a weight-four identity. The modular
weight-four pilot reached normal rank5149 before its ten-minute alarm,
with no singular tests yet run. A separately authenticated continuation
skips the known invariant descendant prefix and retains all resource caps.

For c=2, the corrected N9/N12 internal-alpha-twist calculation and the
larger N12 lowering-target calculation passed their controls. The lowest
twisted momentum-one candidate has stress-normalized dimension1.27179577
at N9 and1.17971932 at N12. Its lowering spectral weight is not yet a
controlled continuum current test. A generic Narain interpretation with
the stated nontrivial Z3 action on both current planes would also require
low scalar companions across all three module charges. The observed
neutral and charged scalar minima are widely separated at these sizes;
this is finite-size tension, not an all-size exclusion. The exact local
clock-parent rotation does not supply a global circuit or a proof of
phase continuity to the physical projector chain.

**Further conditional comparison with2512.08225:** the actual maximal
plane lattice L has Gram[[2,3],[3,24]] and determinant39. Its commutant
C6=Com(V_L,U) is strongly rational by the lattice-coset theorem, with
Rep(C6)=P39^rev tensor Rep(U). In the proper branch it is current-free
and has exactly seven weight-two fields. Thus the earlier exact axis
certificates exhaust (C6)2 and exclude charges1,2,4,5 there. The full
U does not tensor-factor into strongly rational c2 and c6 VOAs.

The ambient complementary rank-six lattice is explicitly identified
in `hi_cft_20260923_next_c6_lattice.md`: determinant39, root system
A2 squared plus A1, an index-six extension of
A2 squared plus A1 plus the norm78 rank-one lattice. Extension-algebra
transitivity carries the conditional Haagerup algebraic defect category
to this c6 lattice extension, with the physical realization hypotheses
stated separately. Ordinary current gauging transparent to the candidate
Haagerup action cannot remove central charge6: the fixed current algebra
has Sugawara charge158/41, so such a quotient has charge at least170/41.
These results sharpen the paper's c6 proposal and constrain a c2 route;
they do not identify the physical chain.

**Update, 07:53 UTC:** the rank-six indicator argument now excludes
every multiplicity m>=2 without assuming C* unitarizability. In the
proper rank-six branch, m=1, the index is (13+3 sqrt(13))/2, and the
center has the standard twelve-object Haagerup S,T data. This uses
the spherical untwisted modular-data theorem in arXiv:2609.25185;
it does not infer braided-category uniqueness from S,T alone.
The rank-four m=3 branch is also fully excluded: a new independently
audited center-induction argument forces its standard modular data,
so both earlier harmonic-theta character obstructions apply without
a C* hypothesis. The m=6 exclusion subsequently passed independent
audit as well: Galois symmetry gives the impossible coefficient4/3
in the balanced induction pattern; the other pattern has a forced
weighted character projection obeying the earlier theta obstruction.
Thus all rank-four alternatives are excluded. Properness implies the
Haagerup index and modular data, without additional rank assumptions.

A separate source-bound modular rank certificate and independent
replay now establish dim X3=10630, hence dim U3=956, conditional on
properness. The production run completed in215.09 seconds at0.300GiB
sampled group RSS; replay took19.93 seconds at0.112GiB. This certifies
linear independence and the saved word provenance, not an independent
reimplementation of every lattice mode. Exact residual kernel calculation
then gives dim(C_U)3=2, both translations of q,r; there is no residual
weight-three primary. Properness itself remains open.

For c=2, an exact local rotation relates the physical monomer--dimer
projector to a three-color clock projector plus its dimer sector.
The source-corrected v3 algebra checker passed, and a separate internal
alpha spatial-twist pilot at N=6,9 passed all seam, translation,
Hermiticity, module-coefficient and saved-spectrum controls. These
internal twists are distinct from the N mod3 translation-twist sectors
in the earlier numerical literature. The pilot supplies finite-size
data, not a continuum or current identification.

* Exact characteristic polynomials of the candidate commuting stresses
  q (c=32/19) and r (c=182/95) on B1 have irrational roots. Examples are
  (7 +/- 2 sqrt(10))/19 for q and (13 +/- sqrt(105))/38 for r. Consequently
  neither particular stress can be the conformal vector of a strongly
  rational subalgebra of B. This excludes the PF17 and diagonal SU(2)
  coset identifications suggested by their central charges. It does not
  exclude rationality of U or of an extension with stress q+r.
* The remaining c=18/5 commutant cannot be K(sl3,7): its exact q stress
  has a central charge absent from the complete idempotent list of the
  three-dimensional K(sl3,7) Griess algebra.
* The first bound proved that every irreducible ordinary U-module has lowest weight between zero
  and 938/169 < 6, and only U itself has lowest weight zero. This uses
  restriction to regular subalgebras, traces on the U-top, and the actual
  26 module tops of T, plus an explicit nonnegative linear-inequality
  certificate respecting complete left/right sl2 characters. Thus all
  irreducible summands of B restricted to U start in integer grades
  0 through 5. This does not justify extending
  a truncated commuting projection to all grades. The later A_L
  argument improves this bound to 17/10, as recorded above.
* An exact seven-dimensional Cartan commutant inside the certified S2
  is closed under the weight-two product. Its idempotent equations with
  central charge two have unit Groebner ideal over Q(sqrt(13),sqrt(-3)).
  There is no complex c=2 axis in this finite slice. The separate c=1
  calculation also gives a unit ideal. Together with the exact Heisenberg
  direct-sum splitting, this proves uniqueness of the PCT-real c=2 stress
  in the constructed ten-dimensional Cartan-zero quasiprimary slice.
  It is the rank-two toroidal stress, with four known currents. This is
  not a classification of all U2.
* Finite-index full-current-gluing interfaces of Narain theories have
  dimensions sqrt(N), N integral. No finite direct sum of these can
  have Haagerup dimension (3+sqrt(13))/2, by normalized field trace.
  This excludes this class of torus defects at all moduli; it does not
  exclude defects that break the full current algebra.
* The exact kernel of the remaining c=18/5 stress on S2 has dimension
  25. The known T tensor PF13 contributes 15 states; ten are extra.
  All six predicted j=+/-5 order-13 simple-current top states occur,
  with PF13 weight 12/13 and the required Potts weight 2/3. The
  all-weight extension is now proved. Locality forces a single
  isotropic order-thirteen charge line and multiplicity one. Its
  representation category is Fib tensor SO(3)_13.
* For the categorical difference-form R-matrix ansatz with
  R'(0)=(-P_rho)R(0), invertibility and the braid equation's first jet
  force R(0) to be scalar. A four-equation elementary certificate was
  independently checked in 0.65 seconds. This reduces that specific
  nonregular ansatz to the already excluded regular one; it does not
  exclude general Lax operators, staggering or enlarged auxiliary spaces.
* The seven-dimensional axis algebra admits a rational Peirce tensor
  after an invertible rescaling over the algebraic closure. Its two
  nontrivial normalization invariants are 195/4 and 45/2. This preserves
  the complex-axis exclusion problem. A smaller elimination now yields
  compact certificates for both central charges one and two. An
  independent arithmetic-only checker verified the source tensor,
  changes of basis, four even branches and the 116-node odd-branch
  certificate for each charge. The earlier oversized proof-DAG
  attempts remain unsuccessful and are superseded by these certificates.
* The unique c=4/5 axis of the five-dimensional ambient residual
  algebra satisfies the complete Virasoro OPE and has weight-two
  spectrum 0^3,(2/5)^1,2^1. It is outside the certified 120-dimensional
  span. This does not yet put it outside U. An independent full E8
  calculation gives residual sector dimensions 5+4+4=13.
* A precise proposed shortcut to properness is false. There is an
  explicit positive even rank-four lattice whose PCT-closed weight-two
  generating slice contains its stress and is closed under all positive
  products, while longer words generate four previously absent currents.
  Consequently even exact low-weight closure needs a separate argument
  controlling excursions to higher weights. See the counterexample note.
* The categorical lattice factory mapping has been checked exactly for
  all channel and flavor faces. The Morita-equivalent factory partition
  function differs from the rho model by the explicit normalization
  3^(N_square-N_Hcell). The positive two-condensate interpolation is
  proportional to t0 P_1+t1 I/d; the physical -P_rho tangent is outside
  this two-dimensional span. This is a microscopic mapping, not a
  continuum or integrability identification.
* The known Haagerup action on a noncommutative torus does not directly
  supply a c=2 stress tensor. Its rho correspondence has rank d and
  Chern number one. A lift with the canonical differential calculus and
  fusion-compatible bimodule connections would require 2d=3, contradicting
  d=(3+sqrt(13))/2. This excludes that specified geometric lift, not all
  possible noncommutative-torus CFT constructions.
* The actual H3 rho Hamiltonian has an explicit three-color
  monomer--dimer representation with local block sizes1,3,3,10.
  Exact arithmetic checked all local recouplings/projectors,15552
  covariance identities, and30740 channel transitions across all
  twist/charge sectors at lengths3--5. The accompanying analytical
  bijection applies at every length. Dimer conversion is nonzero;
  omitting it does not give an exact qutrit reduction. This supplies
  a new concrete continuum starting model, not a CFT identification.

## Paper comparison

[Albert–Honda–Kaidi–Zheng, arXiv:2512.08225v2](https://arxiv.org/html/2512.08225v2)
explicitly assumes existence of the c=8 Z(H3) theory in Section II,
footnote 4. Its gauging construction is conditional on that existence.
Our finite-span dimensions match the gamma=0 character branch; weights
two and three are now proved complete conditional on properness.
The separate modular argument now proves the full character conditional
on properness; finite-span agreement alone would not do so. The target
extension index (13+3 sqrt(13))/2 is derived in the proper branch;
properness remains a separate, unproved step.
Section III proposes asymmetric quotient routes toward c=2 and c=6;
it does not construct those continuum theories. The numerical bootstrap
kinks are evidence rather than identification theorems.

The fuller comparison, including the recent rationality literature, is
in `hi_cft_20260923_next_paper_comparison.md`.

## Reproducible records

* `hi_cft_20260923_next_c8_proof_audit.md`
* `hi_cft_20260923_next_c8_irrational_axes.md`
* `hi_cft_20260923_next_stress_current_spectra.py` and `.json`
* `hi_cft_20260923_next_structure_sl3_exclusion.md`
* `hi_cft_20260923_next_structure_top_bound.md`
* `hi_cft_20260923_next_structure_top_bound_sharp.md`
* `hi_cft_20260923_next_structure_vacuum_projective.md`
* `hi_cft_20260923_next_structure_rationality.md`
* `hi_cft_20260923_next_structure_order13_core.md`
* `hi_cft_20260923_next_structure_order13_top_bound.md`
* `hi_cft_20260923_next_structure_order13_top_check.py` and `.json`
* `hi_cft_20260923_next_structure_independent_audit.md`
* `hi_cft_20260923_next_structure_core_maximality.md`
* `hi_cft_20260923_next_structure_rank46.md`
* `hi_cft_20260923_next_81top_all.json`
* `hi_cft_20260923_next_residual_ambient2.json`
* `hi_cft_20260923_next_structure_residual_tensor.json`
* `hi_cft_20260923_next_structure_f4_coset.md`
* `hi_cft_20260923_next_neighbor_independent_audit.md`
* `hi_cft_20260923_next_structure_affine_pair.md`
* `hi_cft_20260923_next_structure_residual_identification.md`
* `hi_cft_20260923_next_structure_residual_category.md`
* `hi_cft_20260923_next_residual_e8_ambient2.json`
* `hi_cft_20260923_next_structure_residual_potts_verify.json`
* `hi_cft_20260923_next_low_weight_closure_counterexample.md`
* `hi_cft_20260923_next_c2_factory_refresh.md`
* `hi_cft_20260923_next_c2_nctorus.md`
* `hi_cft_20260923_next_structure_residual_current_kernel.json`
* `hi_cft_20260923_next_x2_conditional_rank.json`
* `hi_cft_20260923_next_x2_replay.json`
* `hi_cft_20260923_next_c2_monomer_dimer.md` and `.json`
* `hi_cft_20260923_next_c2_toroidal_obstruction.md`
* `hi_cft_20260923_next_c2_exact_algebra.py` and `.json`
* `hi_cft_20260923_next_c2_groebner.py` and `_c2.json`
* `hi_cft_20260923_next_c2_slice_theorem.md`
* `hi_cft_20260923_next_c2_reduced_exclusion_c1_checked.json`
* `hi_cft_20260923_next_c2_reduced_exclusion_c2_checked.json`

The exact, restartable grade-three/four producer with word provenance is
`hi_cft_20260923_next_grade4_exact.py`. Its grade-three phase completed
in 377.54 seconds at sampled peak group RSS 0.197 GiB, recovering every
Cartan multiplicity of the exact 956-dimensional span and saving 224508
sparse terms across grades one through three. The grade-four pilot
stopped safely at 998456 saved sparse terms after retaining 836 vectors,
using 0.718 GiB sampled group RSS. A disk-backed block design is now
used; the original producer and its checkpoint remain preserved.
The disk-backed pilot resumed at rank 836 and reached rank 2396 in
180 seconds, with sampled peak group RSS 0.361 GiB. Its SQLite store
and decoded-block LRU keep the exact span out of live memory. A bounded
900-second continuation finished at rank 3079 and 2944938 saved sparse
terms, with sampled peak group RSS 0.373 GiB under a 3 GiB address
limit. It stopped at the requested time boundary and saved its cursor.
Its resource estimate
and bounded commands are in `hi_cft_20260923_next_grade4_resource_review.md`.
Even a successful exact dimension 6010 remains a finite-span result.
A later continuation saved rank3393 and3512512 sparse terms after
904.33seconds, at0.364GiB sampled peak group RSS. It stopped cleanly
and the checkpoint remains reusable. Small structural calculations
were prioritized thereafter.

## Closing certificate status: 10:17 UTC

The current consolidated result is in
[the six-hour summary](hi_cft_20260923_six_hour_result.md). It supersedes
earlier provisional status statements: the actual candidate U is strongly
rational, and properness would force the Haagerup modular data and unique
gamma=0 character. The stronger ribbon-center identification also uses the
explicitly recorded external pivotal-classification theorem. **Properness
is still unproved.** The separate physical unitarity/net hypotheses remain
as stated in the final dependency audit.

The final weight-four continuation retained 2,145 of 2,898 exact identities:
2,072 full sparse residual checks and 73 exact zero targets, with zero
failures. Its new output directory is
`hi_cft_20260923_next_h4_integer_bulk_v2`. The 600.046-second run closed
cleanly at sampled peak group RSS 1.034 GiB. There are 753 unproved
weight-four identities. Three weight-five identities for the u-family are
exactly certified; the remaining independent highest-channel count is 21.
The thirty prime-only positive-mode diagnostics are consequences of the
two remaining zero-mode gates once those gates pass, not a third required
independent gate.

The length-15 internal-alpha-twist scalar run also completed with exact
sector/seam conventions, Hermiticity controls and lower-size regressions.
Its lowest dimension in the saved scalar-descendant normalization is
1.0161967340662672; the length-15 spin-one candidate is 1.1383525049.
These are finite-size estimates, not identified continuum dimensions.
The exact minimal-frame obstruction and the separately qualified Z6
orbifold tests are summarized in
[the c=2 status](hi_cft_20260923_next_c2_final_status.md).

The final source audit of 2512.08225v2 confirms that Section II footnote 4
assumes the c=8 realization, and Section III proposes c=2,6 asymmetric
quotient directions without identifying those CFTs. Our explicit c=6
commutant advances one such direction, conditionally on properness for
its Haagerup interpretation, but does not identify the physical c≈2 chain.

Remaining bounded computation and its resource review are recorded in
[the closing-run note](hi_cft_20260923_next_closing_runs.md). No computation
is authorized beyond the 10:31:06 UTC deadline.

## Final update: 10:30:31 UTC

One additional independent weight-five channel passed its exact full
sparse residual: operator 3 with P4_plus, projected to weight (0,14),
rank 69. The run completed in 70.128 seconds with sampled peak group
RSS 0.274 GiB and independently audited artifacts. The final grade-five
count is therefore **4 of 24**, with **20 remaining**. The next channel
(0,12) passed its prime projection at rank 90, but its exact continuation
reached the 135-second limit before certification. That run closed with
exit 0 and peak sampled group RSS 0.343 GiB; its checkpoint is preserved.
All numerical jobs were closed before the six-hour deadline.

The final analytical addition is
[the rational-orbifold obstruction](hi_cft_20260923_next_c2_weak_integral_orbifold.md):
under its explicit rationality, positivity and chiral-preservation
hypotheses, the finite rational-CFT defect category is weakly integral,
whereas the Haagerup noninvertible object's squared dimension is not an
integer. It does not exclude defects breaking that chiral algebra or
identify the physical chain. Neither requested CFT has been
unconditionally identified. The consolidated summary states the final
positive results, external dependencies and outstanding proof gates.
