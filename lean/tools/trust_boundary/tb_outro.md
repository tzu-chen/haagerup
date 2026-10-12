
## 8. Points a reviewer should check

1. **Assumed conclusions.**  Two hypotheses supply a conclusion directly rather than a premise of
   an argument: `hν` (ProofMapConcrete.lean:461) supplies `ν₃(a) = 1` for the boundary category
   (the only content of the node `untwistedPointed` used downstream, by `L_rankSixMoments` and
   `E_izumi`), and `NetInputs.untwisted` (ProofMapConcreteNetCount.lean:100) supplies the
   conjunct `ν₃(a) = 1` of `NetHI`.  Both are conditional on the proved node `UntwistedNode`
   (free-induction equivalence, and the monoidal equivalence of the `H/B`-module category with the
   untwisted `Vec_{ℤ/3}`, `untwisted_vec_equivalence_of_separable`), but the tensor embedding into
   `𝓕` and the Frobenius–Schur indicator are not formalized: neither `𝓕` nor `ν₃` is part of the
   categorical model.
2. **Concrete content concluded by external arrows.**  `E_dmno` concludes the positive dimension
   character of `𝓕` with `∑ d_i² = 3s`, `d_X = s - 1`; `E_cklw529` concludes `dim U₀ = 1`;
   `L_reconstruction` (open) concludes that `recon` is injective with unitarizable values.
3. **Unmodelled predicates.**  `Unitarizable`, `SignData.XInvertible`, `SignData.toral`,
   `StressData.factorNonneg`, and the opaque nodes of Section 2 are propositions whose meaning is
   fixed only by their docstrings and the inputs that mention them.
4. **Unlinked models.**  `U` appears as `D.U u` (properness, over an arbitrary field `k`) and as
   `St.U` (regularity, over `ℂ` with a positive form); these are not identified in Lean.  `𝒞`
   (`Rep(U)`) is linked to `St.U` only through `hunit`; `Cr` (`Rep(B)`) is not linked to `A`;
   `B` and `Bn` are independent `BoundaryData`; `ι`, `κ` are not linked to `Simp`.  `Simp` is
   linked to `Label` by `LI` (conditional on `modularData`).
5. **Lattice model.**  The entries proved for `latticeD`/`latticeDP` hold modulo the single
   hypothesis `FLMBorcherds` (the Borcherds identity for the Fock-model modes, FLM Theorem
   8.10.2), and are discharged together in `lattice_proof_map` (ProofMapLattice.lean).  There the
   PCT node is no longer opaque: it is *defined* as "`θ_g` is mode-compatible, `θ_g S₂ = S₂` and
   `θ_g U = U`" (`pctNodes`); all three conjuncts are proved (`pctModeCompatible`,
   Lattice/PCTModes.lean; `certPCT_latticeD`; `pctV_mem_U_lattice`).  `E_cklw529` still carries Dong–Lin unitarity (the transported form is positive definite
   with PCT operator `θ_g`) and CKLW Prop. 5.29 itself; a reviewer should check that this is the
   reading of `certPCT` the manuscript uses (lines 1975–1992, 2604).  `S₃` (dimension 956) is not
   yet exported from the lattice data, so 7 `LowerCertificate` fields, Gates 4/5 and the
   nilpotence statements remain certificate inputs (`LatticeClosureInputs`).  The other models
   of item 4 (`St.U`, `𝒞`, `Cr`, `B`, `Bn`) are not instantiated at the lattice VOA.
6. **Open manuscript lemmas.**  `L_rational`, `L_reconstruction`, `L_annulus`,
   `L_boundaryUnitary` are not made concrete: their nodes involve module categories, nets and
   unitary structures that are not modelled.
