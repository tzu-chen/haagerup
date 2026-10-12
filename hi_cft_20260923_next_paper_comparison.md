# Comparison with arXiv:2512.08225 and the current construction

Literature checked 23 September 2026. This note is a reading and algebra
task; no numerical job was launched. The permanent resource limits apply;
the September 15 memory exception has expired.

**Latest consolidated result:** the local construction now has the exact
fork U=B or a strongly rational Haagerup-center realization with the
gamma=0 full character vector. The categorical-equivalence step uses
the externally reported exhaustive computer-assisted classification
audited in `hi_cft_20260923_next_hi_classification_audit.md`; the index,
modular data and character arguments do not need that classification.
The unresolved existence step is properness U!=B. See
`hi_cft_20260923_next_conditional_identification.md` for the consolidated
theorem and its dependencies. The dated updates below record earlier
stages of the argument and are superseded by this statement.

The finite strong-generation proof is still incomplete. The normal
weight-four span has finite-prime rank6007, with a further right-sl2
triplet giving6010. The triplet now has an exact characteristic-zero
construction and passed its current and Virasoro controls. Full exact
singular-product containment is still required to prove properness;
no finite-prime containment is being promoted to an exact identity.

A concrete conditional c=6 construction now sharpens the paper's
asymmetric-quotient proposal. The saturated plane lattice L has
Gram[[2,3],[3,24]], determinant39, and V_L lies in U. Its actual commutant
C6=Com(V_L,U) is strongly rational, with
Rep(C6)=P39^rev tensor Rep(U). The verified lattice double-commutant
hypothesis permits use of the
[lattice-coset theorem, Section4.3](https://arxiv.org/html/1611.00305#S4.SS3).
The ambient perpendicular lattice N is explicitly the index-six extension
of A2+A2+A1+<78> by (omega,omega,alpha/2,u/6). Its Gram matrix and E8
embedding are in [the lattice identification](hi_cft_20260923_next_c6_lattice.md).
This lattice identification does not depend on properness. Transitivity
of extension algebras transports the same conditional Haagerup algebraic
defect category to C6 subset V_N; the physical defect interpretation
retains the complete-unitarity and VOA/conformal-net realization
hypotheses stated in [the coset audit](hi_cft_20260923_next_structure_c6_coset_audit.md).

In the proper branch C6 has no currents and exactly seven weight-two
fields. Their exact idempotent equations exclude Virasoro stresses of
charges1,2,4,5. Also, ordinary current gauging transparent to the candidate
action can remove at most158/41, leaving c>=170/41>2. These results
constrain specified c=2 quotient routes; they do not exclude all
asymmetric quotients or identify the chain's continuum theory.

**Update during this window:** strong rationality of U is now proved
from its positive regular-stress identity, projectivity of the vacuum,
and Etingof–Penneys Theorem 1.1 (arXiv:2412.17681v3). See
`hi_cft_20260923_next_structure_rationality.md`. The older rationality
gap described below records the starting point. Properness, the
Haagerup categorical identification and the c=2 continuum theory remain
separate open steps.

**Update, 06:42 UTC:** the ambient c=18/5 residuals are now identified
at all weights and proved strongly rational:
Com(A_L,V(E8)) is the (F4,1 tensor A1,1)/A1,13 coset;
Com(A_L,B) is the (A2,1 tensor A2,2 tensor A1,1)/A1,13 coset,
with diagonal levels 4+8+1. The latter has category
Fib^rev tensor SO(3)_13^rev tensor P(Z3 squared). This closes the
ambient residual identification gap discussed historically below.
It does not yet construct a rational frame inside Com(A_L,U), or
prove U is proper. See the residual identification and category notes.
The sharp universal top bound h<=17/10 proves the all-weight fork
B=U or B=U plus one simple module with an 80-dimensional top.
Conditional on the proper branch, the E8 boundary category has rank
four or six. Two rank-four cases remain; in rank six the fusion
rule has Haagerup form with an undetermined multiplicity m>=1.
Neither the index nor m=1 is established.

**Update, 07:57 UTC:** further categorical arguments remove the rank-four
alternatives without C* unitarizability assumptions. Center induction
forces the m=3 modular data; for m=6, Galois symmetry excludes the
balanced induction pattern by a nonintegral Verlinde coefficient,
and indicator moments force a universal three-dimensional character
projection in the other pattern. The independently audited harmonic-theta
bounds contradict six currents in both orientations. In rank six,
an independently audited root-of-unity indicator argument forces m=1.
Thus properness implies the Haagerup fusion rule, extension index
(13+3 sqrt(13))/2, and standard twelve-object S,T data. Properness remains
unproved; modular-data equality alone is not braided-category equivalence.
The conditional weight-two and weight-three dimensions are now fully
certified as120 and956, using lower bounds on the complementary module.

The explicit subVOA is

\[
 U=\langle A_{1,1}\otimes A_{1,39},\omega_B,u\rangle
 \subset B=V_{E_6\oplus A_2}\subset V_{E_8},
\]

with the three-term field u in the
[construction report](hi_cft_20260923_c8_construction_report.md).
The [preceding proof report](hi_cft_20260923_proof_report.md) claims an
exact parafermion identification, a positive stress decomposition,
and C2-cofiniteness for this actual generated U. This note uses those
local results as its starting point; it does not independently rerun
their certificates. Properness and Haagerup identification remain open
at this starting point.

## What the requested paper establishes

[Albert–Honda–Kaidi–Zheng, arXiv:2512.08225v2](https://arxiv.org/html/2512.08225v2)
was submitted December 9, 2025, revised February 19, 2026, and published
as [Physical Review Letters 136, 091603](https://journals.aps.org/prl/abstract/10.1103/6tzz-tvp7)
on March 2, 2026. The arXiv version history lists no later revision.

Section II, footnote 4, explicitly assumes existence of the c=8
Haagerup-center theory. Under that premise, its character identities
and categorical gaugings connect this theory, E8 level one, and
E6 level one times A2 level one. E8 Haagerup symmetry is consequently
conditional. Its Fibonacci example instead begins with an established
conformal embedding. Section III suggests asymmetric quotients leading
to c=2,6; it does not construct them. Appendix C gives finite numerical
bootstrap bounds, with derivative cutoff 21, spin cutoff |s|≤8 and
precision 320. The neutral-scalar kinks are near (c,Δ)=(2,2),(6,2),
and the charged-sector kink near (2,2/3). These are bound features,
not a determined spectrum. Appendix D's additional Haagerup symmetries
inherit the same existence assumption. The cited sequel with Hirasaki
remains listed as forthcoming; this search found no public version.

## Comparison with the local object

The local construction addresses the missing existence premise, rather
than an already proved identification. The following are logically
different objects and claims:

| Object | Established local meaning | Additional statement needed |
| --- | --- | --- |
| V(E8) | Holomorphic lattice VOA, c=8 | Actual Haagerup categorical action |
| B=V(E6⊕A2) | Rational ambient lattice VOA, c=8 | The particular noninvertible symmetry selecting U |
| U | Explicit unitary strongly rational conformal subVOA, c=8; properness conditionally forces the Haagerup category and full character | U≠B |
| Diagonal full CFT built from a rational U | Available once the relevant rationality and representation data are established | Identification of its defect category and relation to a chosen gauging |
| The H3 rho-projector chain | A separate microscopic Hamiltonian with numerical continuum evidence | Controlled continuum identification and its full defect action |

In particular, the c=8 construction is not an identification of the
approximately-c=2 continuum limit. The local spaces of dimensions 120
and 956 are exact finite generated spans. They are now proved to be the
complete homogeneous components of U conditional on properness. The full
conditional character theorem now also forces dimension6010 at weight four;
the old direct computation of that span remains numerical. Neither positive stress decomposition nor
C2-cofiniteness rules out U=B: B has both finiteness and unitarity too.

The local irreducible-current argument does give a useful exact fork:

\[
 U=B\quad\hbox{or}\quad U_1=(A_{1,1}\oplus A_{1,39})_1.
\]

In the proper case, the latter has dimension six and the certified
80-dimensional complementary current space generates an irreducible
U-module. The subsequently proved bound h<2 now shows that all of B
is the sum of just the vacuum module and that module in the proper
branch. It does not decide which branch occurs.

The exact rational core T has c=14/5 and four currents. Thus it cannot
be G2 level one, whose weight-one Lie algebra has dimension 14. Equal
central charges do not turn the local lattice–Potts core into the
known Fibonacci conformal embedding.

## The later hypergroup result and exact targets

[Gannon–Rayhaun, arXiv:2606.05279v1, Section 4.3](https://arxiv.org/html/2606.05279v1#S4.SS3)
is dated June 3, 2026. It also assumes the sought strongly rational
Haagerup realization. Its reformulation places the fixed algebra of a
suitable rank-two hypergroup action inside B. Writing

\[
 d=\frac{3+\sqrt{13}}2,\qquad
 w=d^2=\frac{11+3\sqrt{13}}2,
\]

the normalized nonidentity operation obeys

\[
 a\star a=\frac1w\,1+\frac{w-1}{w}\,a.
\]

The corresponding conditional extension has B=U⊕X and dim(X)=w;
its relative line category is the near-group category with nine
invertible objects and one object of dimension 3d. These are useful
construction targets, not consequences of the current finite spans.

The following numerical invariants follow algebraically if that
extension and its categorical hypotheses have actually been proved:

\[
 s:=\dim_U(B)=1+w=\frac{13+3\sqrt{13}}2,
 \qquad \dim_U(V_{E_8})=3s,
\]
\[
 \operatorname{Dim}\operatorname{Rep}(U)
 =\operatorname{Dim}\operatorname{Rep}(B)s^2
 =9s^2
 =\bigl(3+3d^2\bigr)^2.
\]

The first factor of 3 comes from the actual index-three lattice
extension B⊂V(E8); the factor 9 is the order of the discriminant group
of E6⊕A2. In the Haagerup scenario the 80-dimensional current top
belongs to X, but its ordinary vector-space dimension does not determine
its categorical dimension w. A measured rank or trace at a single
grade therefore cannot supply this index.

There is a particularly easy false positive to avoid. Let P be any
orthogonal projection onto a subspace, and define

\[
 a=P-\frac1w(1-P).
\]

Direct multiplication using P²=P yields

\[
 a^2=\frac1w I+\frac{w-1}{w}a.
\]

This identity works for every P. Even an all-weight projection onto U
would therefore satisfy the displayed hypergroup polynomial after
rescaling, regardless of whether U is the Haagerup algebra. The missing
content is a genuine symmetry action, with the required positivity,
locality and coherent junction data, or an equivalent certified
finite-index extension. An arbitrary spectral projector does not
establish any of those properties.

## Earlier routes and later literature

The following rational-frame and Zhu-algebra routes describe alternatives
considered at the start of the window. Strong rationality is now proved
by the projective-vacuum argument above; the remaining existence gap is
properness. The suggested individual residual stresses have since been
excluded as stresses of strongly rational subalgebras by their irrational
weight spectra. Full ambient residual cosets were identified separately.

The strongest concrete route available from the local starting point
is to identify a rational conformal frame and determine branching in
that frame. The already identified T and K(sl2,13) leave c=18/5.
The additional exact commuting stresses of charges 32/19 and 182/95
are potential starting fields, but their rational extensions have not
been identified. Completing such a frame would replace uncontrolled
all-weight generation with a finite extension problem in known module
categories. One must then prove the actual extension contains exactly
the claimed summands and compare its categorical data.

An independent rationality route is available through the Zhu algebra.
[McRae, arXiv:2108.01898v3, Main Theorem 3](https://arxiv.org/html/2108.01898v3#S1.SS2)
(January 22, 2026; Cambridge Journal of Mathematics 14 (2026)) proves
rationality for an N-graded simple self-contragredient C2-cofinite VOA
whose Zhu algebra is semisimple. Thus an exact finite Zhu presentation
with a semisimplicity certificate would remove the rationality gap.
The known irreducible action on an 80-dimensional current top only
supplies one representation of that algebra; it does not prove the
whole Zhu algebra semisimple.

Finite branching of B over U does not by itself substitute for such
a theorem. The applicable descent framework in
[McRae, arXiv:2103.07657](https://arxiv.org/abs/2103.07657)
has rigidity and nonzero categorical-dimension conditions. They must
be checked before importing rationality from B.

For the final categorical comparison there is now concrete exact
reference data:
[Mäurer–Thiel–Vercleyen, arXiv:2601.20012v1](https://arxiv.org/abs/2601.20012)
(January 27, 2026) computes F-symbols, R-symbols and pivotal
coefficients for Z(H3). This can support an exact gauge-equivalence
comparison once U's intertwiners and modules are constructed. Matching
the modular matrices alone is weaker than matching the braided
category. These data do not themselves construct a VOA.

The newer
[Jeong–Sohn, arXiv:2608.11946v1](https://arxiv.org/abs/2608.11946)
(August 12, 2026) concerns nonunitary boundary RCFTs and generalized
Haagerup–Izumi modular data, in part up to Galois conjugation. It supplies
no demonstrated identification with this unitary U or with the Hermitian
rho-projector chain. The search found no later unitary construction that
discharges the present properness or categorical gaps.

The newly submitted
[Gannon–Schopieray–Yadav, arXiv:2609.25185](https://arxiv.org/html/2609.25185)
(September 21, 2026) proves a center modular-data theorem for spherical,
untwisted cyclic Haagerup–Izumi categories. Its Haagerup–Izumi definition
already assumes multiplicity one. Thus its theorem applies after m=1
is established; it does not exclude the present m>=2 alternatives,
construct the c=8 VOA, or determine the c=2 continuum. For order three,
the prime discriminant thirteen makes its metric-group conclusion
especially concrete. Matching those modular data would still need
the appropriate categorical identification argument.

## Exact obstructions to naive c=2 deductions

A c=2 full CFT with Haagerup defects is a different target from a c=2
chiral VOA whose entire representation category is Z(H3). For a unitary
strongly rational chiral VOA the multiplicative central charge is
exp(2πic/8). A Drinfeld center has multiplicative central charge 1;
see [Ng–Schopieray–Wang, Higher Gauss sums of modular categories](https://arxiv.org/abs/1812.11234).
Consequently the latter chiral target at c=2 is impossible:

\[
 \exp(2\pi i\,2/8)=i\ne1.
\]

There is no contradiction for a nonchiral CFT with cL=cR=2 carrying
Haagerup line defects. Its chiral representation category need not be
the Drinfeld center of that defect category.

Finite topological gauging leaves the stress-tensor central charge
unchanged. Thus even a completed c=8 gauging square does not on its own
produce c=2. A reduction of central charge requires an explicit coset,
factor, or other conformal construction with the missing c=6 accounted
for, followed by proof that the desired defect action survives.

The obvious ambient factor is not such a proof. If U is proper, its
six currents prevent E6 level one, with 78 currents, from embedding
as a conformally compatible subVOA of U. Therefore the notation
Com(E6 level one,U) cannot define a c=2 coset in this candidate.
Com(E6 level one,B)=A2 level one is of course an existing c=2 VOA,
but the fact that B factors does not show that the hypothetical
Haagerup action on B preserves either factor. Any use of that route
must construct the action and prove that restriction property.

For the lattice chain, a proposed c=2 theory additionally needs its
sector-resolved dimensions, multiplicities, current content and
continuum defect action checked against the chain. A bootstrap upper
bound does not identify its lightest scalar or eliminate finite-size
drift. The literature comparison therefore strengthens the precise
construction targets, while leaving both requested identifications
unproved at the start of this continuation.

The exact monomer–dimer and local clock-parent identities developed in
this window are microscopic statements, not continuum identifications.
Internal-alpha-twist spectra now extend to length15. Their drift and
lowering spectral weights do not yet establish chiral currents. The
specific natural quantum-charge assignment in a hexagonal T2/Z6 orbifold
also conflicts with the measured candidate OPE selection rule; this is
a narrow assignment test, not an exclusion of every torus orbifold.
See [the c=2 status note](hi_cft_20260923_next_c2_final_status.md).

## Final comparison audit, 23 September 2026, 10:18 UTC

The opening consolidated statement and the
[six-hour result](hi_cft_20260923_six_hour_result.md) take precedence over
the historical updates. Strong rationality is proved. Conditional on
U!=B, the rank-four alternatives and every higher rank-six multiplicity
have been excluded, and the index, standard Haagerup modular data and
full gamma=0 character vector follow. In particular, the phrase
"present m>=2 alternatives" in the later-literature discussion no longer
describes the local result. The categorical equivalence additionally
uses the externally reported exhaustive pivotal-category classification,
with the dependency distinguished in the final theorem. There is no
remaining independent rationality or multiplicity gap. Properness remains
unproved; the incomplete finite-generation certificate cannot decide it.

The source comparison remains conditional in exactly this respect:
[2512.08225v2, Section II, footnote 4](https://arxiv.org/html/2512.08225v2#S2)
assumes existence of the c=8 theory; its character identities and gauging
analysis do not prove that assumption. The local proper branch selects
gamma=0 in its equation (12), but unresolved properness means that the
paper's existence premise has not yet been discharged.
[Section III](https://arxiv.org/html/2512.08225v2#S3) proposes asymmetric
quotients at c=2,6 and supplies bootstrap evidence, without identifying
either quotient.

The actual strongly rational commutant C6=Com(V_L,U), its representation
category P39^rev tensor Rep(U), and the explicit determinant-39 ambient
lattice provide a new local c=6 construction beyond that proposal. The
Haagerup algebraic defect category on the extension C6 subset V_N remains
conditional on the proper branch and categorical classification; the
physical unitary-defect interpretation retains the additional hypotheses
in the coset audit. This is neither a c=2 factorization nor an identification
of the rho-projector chain. Thus neither requested CFT has been
unconditionally identified at this audit.
