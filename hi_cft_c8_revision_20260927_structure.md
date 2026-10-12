# Structure revision and dependency audit — 27 September 2026

This audit covers `hi_cft_c8_manuscript_structure.tex`. Reading, algebra,
primary-source verification, and lightweight editing were performed by the
structure agent. All computations and Lean checks were reserved to the root
agent under the permanent resource policy. No numerical job, build, or Lean
invocation was started by this agent.

## Main outcome

The structure fragment now prints the substantive arguments leading from
actual embedded regular factors to strong rationality, the sharp universal
top bound, the rank-four/rank-six reduction, exclusion of the alternative
rings, the Haagerup modular data, and the complete character vector. The
former R3 and R4 missing-proof boxes are replaced by mathematical proofs.
R1 and R2 remain precise, limited certificate boundaries rather than vague
cautions about an entire section.

The model-specific assumptions are collected in
`cert:structural-inputs`: actual Potts and parafermion fields and their
polynomial OPEs, membership/PCT/translation, the positive conformal-vector
identity, the lattice–Potts core and spectral witnesses, and the eighty- and
81-dimensional top actions. These are distinct from finite strong closure.
The eighty-current record is `hi_cft_20260923_proof_current_module_v2.json`;
the mixed-top record is `hi_cft_20260923_next_81top_all.json`. The latter
proves irreducibility, not mutual equivalence of all four restrictions.

## New or substantially expanded deductions

1. **Regularity.** Grading-compatible inclusions are defined without confusing
   their stress tensors with the ambient stress tensor. Compact averages are
   reduced to finite positive sums by convexity. The C2 argument uses ordinary
   module C2 quotients, regular restriction, and spectral theory on each
   finite-dimensional ambient grade. An orthogonal decomposition of the whole
   weak restricted module is unnecessary. Highest-space, vacuum-like-vector,
   and projective-vacuum arguments are printed in full. Individual energy
   operators are diagonalizable on a lowest space; simultaneous diagonalization
   or a positive inner product on arbitrary VOA modules is not assumed.

2. **Rigidity without circular semisimplicity.** The finite braided
   Grothendieck–Verdier category has an exponential bound on endomorphism
   dimensions of tensor powers, using a projective generator and right
   exactness. A projective simple unit splits the nonzero duality evaluation.
   Etingof–Penneys Theorem 1.1 then supplies rigidity; exact duality implies
   every object is projective. The independent analytic-agent review confirmed
   the hypotheses against version 3 of that primary source.

3. **Parafermion proof transport.** The finite-audit agent's proposition is
   integrated as `prop:pf13-finite-reconstruction`. It proves full generator
   OPE closure by the acyclic schedule A6 → bb → A7 → bd → B6 → A8 → B7 → dd.
   The two simple poles and the weight-six decoupling polynomial are explicit
   required inputs. A diagonal generated subalgebra in the product of the two
   target VOAs has one-dimensional weight zero and a unique maximal proper
   graded ideal. This proves equality of the simple quotients without assuming
   free generation or that a proposed relation list generates all null fields.
   The proof is specifically for the canonical self-row and linear upper ab
   poles. It does not assert a more general unproved reconstruction theorem.

4. **Core and sharp top bound.** The order-thirteen spectral witness and the
   pointed-support/multiplicity-one argument are printed. Actual lowest-weight
   charge minimizations, all minimizing charge labels, the fourteen top
   dimensions and traces, the Sugawara trace conversion, and the two complete
   sl2-character inequalities are explicit. The resulting nonnegative
   certificate proves h ≤ 17/10 for every simple U-module, without assuming
   its unitarizability. The charge cutoff is justified rather than empirical.

5. **An unnecessary stabilizer hypothesis removed.** New
   `lem:no-sign-extension` excludes the invertibility of X in B = U ⊕ X.
   Invertibility would produce an index-two grading and a sign involution of
   B with fixed currents sl2 ⊕ sl2. Every finite-order automorphism of E6 ⊕ A2
   has fixed rank at least 4 + 1 = 5, by conjugacy to a toral times diagram
   automorphism, contradicting fixed rank two. This proves the needed absence
   of a sign extension, not the stronger Aut(B/U) = 1. All structural rank
   exclusions now use the weaker proved fact. The analytic agent adopted it
   in the net-side argument too.

6. **Rank four.** Larson Theorem 1.1 supplies m in {0,2,3,6}; a C*-only
   classification is not being invoked. The m = 2 holomorphic extension and
   E8 Lie fixed-point calculation are expanded. For m = 3, induction moments
   and actual extension branching determine the required modular data. For
   m = 6, the balanced case has a signed-Galois/Verlinde obstruction; the
   unbalanced case has a weighted three-component character projection.
   Four harmonic-theta calculations now give the incompatible current-count
   formulas explicitly. No complete rank-nine or arbitrary near-group-center
   classification is substituted for these calculations.

7. **Rank six.** The ring derivation, formal-codegree induction multiplicities,
   third-indicator input, and two twist moments are printed. The elementary
   prime-factor bound and the conductor-40 cyclotomic orbit bound are proved,
   including the indispensable second-moment-in-Q(sqrt(10)) condition and
   its equality case. The surviving six residual twists are derived from
   conductor-13/26 orbit equality and linear independence, giving six distinct
   nonresidue thirteenth roots and second indicator +1.

8. **Characters and further actual branching.** Finite image plus the absence
   of invariant constants proves uniqueness from principal parts. The two
   Evans–Gannon columns and dim U1 = 6 force the complete vector, not merely
   its displayed low coefficients. New `cor:unmixed-lattice-restrictions`
   identifies the (0,±1) restrictions with c1 and the (±1,0) restrictions
   with c2: their next possible top weights exceed the final 15/13 bound.
   This removes the need for further finite-top irreducibility calculations
   for those four sectors.

## Independent exact arithmetic and bounded formalization

`c8_revision_20260927/check_top_bound.py` reconstructs the fourteen core tops
from the printed charge formulas using only standard-library `Fraction` and
finite charge enumeration. It does not import the old checker or saved table.
It verifies minimizing labels, actual charges, dimensions, traces, charge
symmetry, the sl2 inequalities, and the nonnegative 17/10 certificate.
The root agent reports PASS in `c8_revision_20260927/top_bound_replay.json`.

`lean/HaagerupIzumi/CFT/TopBound.lean` formalizes the weighted fourteen-variable
nonnegative certificate and its consequence 10 W_scaled ≤ 17·4680 D from
nonnegative multiplicities and the two character inequalities. It does not
formalize the VOA embeddings or assert the top table as a theorem. The root
reports Lean PASS, no `sorry` or new axioms, with the standard `propext`,
`Classical.choice`, and `Quot.sound` axioms. Its peak RSS was 1.652 GiB.

## Primary-source scope checks

The regularity proofs were checked against Abe–Buhl–Dong Proposition 5.2,
McRae's finite category discussion, and Etingof–Penneys Theorem 1.1. The
convolution argument uses Bischoff–Jones Lemma 3.1 and Corollary 3.4. The
fixed-rank argument uses Reeder–Levy–Yu–Gross §5.2. Rank-four classification
uses Larson Theorem 1.1; the formal-codegree and indicator formulas use
Ostrik Theorems 2.5/2.13 and Ng–Schauenburg Theorem 4.1. Signed Galois and
finite-image claims use Dong–Lin–Ng Theorems I and II. The Gannon–Schopieray–
Yadav citation is specifically the spherical untwisted HI modular-data
statement, Theorem A(2)/5.1; it is not a general abstract-category
classification. Complete bibliographic snippets were supplied to root in
`c8_revision_20260927/structure_bibitems.tex`.

The proof organization follows genuine mathematical papers: hypotheses
before consequences, finite input separated from all-weight implications,
and modular data separated from tensor equivalence. The primary guides
included Abe–Buhl–Dong, Etingof–Penneys, Larson, and Evans–Gannon.

## Optional algebraic classification route — explicit additional input

`prop:optional-algebraic-identification` is separate from the main modular
and character proof. It assumes the exhaustive four-entry pivotal
HI(Z3) classification reported in Vercleyen's thesis, §4.4 and Table 9.1
(printed p.171). Gauge equivalence in §4.1.8 uses complex nonzero scalars
and ring automorphisms. The algorithm uses exact algebraic operations;
§4.4.1 says the full notebooks and decision logs are available on request.
These logs have not been independently audited or replayed here.

Evans–Gannon Theorem 3(ii) constructs four inequivalent cases, but only
classifies its endomorphism realizations; it does not alone exhaust all
abstract categorifications. Combining those four examples with the extra
exhaustion assumption gives the two positive categories H2/H3 and two
negative-dimensional Galois conjugates. The fusion ring has a unique pivotal
structure: a tensor automorphism of the identity has t_rho^2 = t_1 = t_rho,
then t_(a rho) = t_a = 1. The negative examples cannot be repivotalized to
become positive. Grossman–Snyder Theorem 1.4 makes H2 and H3 Morita equivalent.
The center equivalence preserves the unique positive spherical structures,
hence is ribbon. This establishes abstract unitarizability only under the
additional classification input; it does not prove positivity of canonical
VOA fusion pairings and does not discharge analytic A1.

Primary sources for this optional route:
- https://mural.maynoothuniversity.ie/id/eprint/18958/1/phd.pdf
- https://arxiv.org/html/1506.03546 (Theorem 3(ii), introduction, §7.1)
- https://arxiv.org/html/1102.2631v2 (Theorem 1.4)

## Remaining boundaries

The exact embedded-field identities and finite top actions in
`cert:structural-inputs` must be authenticated as actual lattice identities;
printing their consequences does not independently replay all producers.
The optional abstract classification has its own unreplayed external
exhaustion dependency. Complete unitarity of U, canonical fusion-pairing
positivity, and analytic transport remain governed by the analytic section.
No conclusion here identifies a braided category from S and T alone.
