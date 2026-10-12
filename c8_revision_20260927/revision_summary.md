# c=8 manuscript revision — 27 September 2026

The draft grew from 25 to 55 pages, with 43 numbered primary references.
Its original sources and PDF are preserved in `baseline/`. The intermediate
54-page version before the A1 proof is preserved in `pre_annulus_resolution/`.

The major changes are:

- A complete filtered-Wick/recursive strong-generation proof and corrected
  ordering of the Virasoro/current bootstrap before Gate5.
- Explicit lattice/PCT/current conventions and a new direct low-character
  corollary; minimal generation is now a declared, replayed input.
- A terminating parafermion OPE reconstruction and simple-quotient
  uniqueness argument, with the exact field premises stated separately.
- Full positive-stress rationality deductions, the 14-top calculation,
  branching, rank exclusions, conductor 40 equality case and character
  uniqueness.
- A Lie-theoretic no-sign-extension argument replacing the unnecessary
  full pointwise automorphism calculation.
- Detailed proofs of A2/A3, giving the Haagerup conformal-net realization,
  diagonal full net theory, and selected H3 holomorphic net extension.
- A pairwise proof of A1: localized lifts and a common diffeomorphism
  lift give the required annulus actions; round factorization, sewing,
  reflection and holomorphy establish the complete insertion identity.
  This supplies complete VOA unitarity and the selected V(E8) extension.
- Two Lean modules, twelve scoped arithmetic/provenance replays, and a
  supplemented input ledger recovering omitted source dependencies.

All three analytic review obligations A1–A3 now have explicit arguments.
The A1 proof combines the recent annulus integration and reconstruction
theorems with Tener’s precise paired-action definition; it does not assume
that abstract net isomorphism identifies the concrete annulus systems.
The original embedded boundary category remains H2 or H3, and the selected
holomorphic net extension is not asserted to be the E8 net.

See the main PDF, the revised review register, and the finite/structure/
analytic audit notes for the exact dependencies. Internal reviews and
limited Lean checks are not external expert certification of the draft.
