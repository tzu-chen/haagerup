module

public import HaagerupIzumi.C8All

@[expose] public section

/-!
# Axiom audit of the headline results of the c=8 formalization

Each line below must report a subset of `[propext, Classical.choice, Quot.sound]`.
-/

-- Properness (Appendices A–E)
#print axioms HaagerupIzumi.C8.BorcherdsVertexAlgebra.toVertexAlgebra
#print axioms HaagerupIzumi.C8.VertexAlgebra.recursive_strong_generation
#print axioms HaagerupIzumi.C8.LowerCertificate.gate4
#print axioms HaagerupIzumi.C8.LowerCertificate.gate5
#print axioms HaagerupIzumi.C8.prop_mainproper
#print axioms HaagerupIzumi.C8.prop_mainproper_proper
#print axioms HaagerupIzumi.C8.S₂_le_U_of_closure
#print axioms HaagerupIzumi.C8.prop_mainproper_of_charges
#print axioms HaagerupIzumi.C8.LatticeNilpotence.prop_mainproper_of_lattice
#print axioms HaagerupIzumi.C8.cor_initial_grades_of_certificates
#print axioms HaagerupIzumi.C8.ProofMap.properness_arrows
-- Regularity (Appendix F)
#print axioms HaagerupIzumi.C8.PositiveStress.average_identity_finite
#print axioms HaagerupIzumi.C8.finiteDimensional_quotient_of_positive_identity
#print axioms HaagerupIzumi.C8.eq_zero_of_isNilpotent_sum
#print axioms HaagerupIzumi.C8.VacuumLike.vacuumLike_module_map
#print axioms HaagerupIzumi.C8.Diagonal.diagonal_reconstruction
-- Branching, fusion rings, number theory (Appendix G)
#print axioms HaagerupIzumi.C8.CoreTops.universal_top_bound
#print axioms HaagerupIzumi.C8.Fusion.rank6_ring
#print axioms HaagerupIzumi.C8.Fusion.aut_invertible
#print axioms HaagerupIzumi.C8.Fusion.e8_A4_invariants_ge
#print axioms HaagerupIzumi.C8.Fusion.m6_balanced_impossible
#print axioms HaagerupIzumi.C8.Fusion.nearGroup_length
#print axioms HaagerupIzumi.C8.Fusion.rank6_center_count
#print axioms HaagerupIzumi.C8.Theta.m3First_table
#print axioms HaagerupIzumi.C8.Theta.m3Reverse_table
#print axioms HaagerupIzumi.C8.Theta.m6First_table
#print axioms HaagerupIzumi.C8.Theta.m6Reverse_table
#print axioms HaagerupIzumi.C8.Theta.near_group_formulas_ne_six
#print axioms HaagerupIzumi.C8.CubeRootTwists.rank6_twists
#print axioms HaagerupIzumi.C8.RankSixMoments.indicator_moments
#print axioms HaagerupIzumi.C8.NearGroupMoments.neargroup_moments
#print axioms HaagerupIzumi.C8.ModularLinearAlgebra.m6_projection
#print axioms HaagerupIzumi.C8.NumberTheory.squareclass_bound
#print axioms HaagerupIzumi.C8.NumberTheory.multiplicity_eq_one
#print axioms HaagerupIzumi.C8.NumberTheory.periodN_eq
#print axioms HaagerupIzumi.C8.NumberTheory.six_residual_twists
-- Characters (Appendix H)
#print axioms HaagerupIzumi.C8.Characters.pole_iff
#print axioms HaagerupIzumi.C8.pole_cancellation
#print axioms HaagerupIzumi.C8.CharacterUniqueness.character_vector_unique
#print axioms HaagerupIzumi.C8.CharacterUniqueness.character_vector_unique_of_qexp
#print axioms HaagerupIzumi.C8.CharacterUniqueness.haagerup_character_unique
#print axioms HaagerupIzumi.C8.CompatibleTop.compatible_top_of_directSum
#print axioms HaagerupIzumi.C8.CompatibleTop.isNonnegDiagonalizable_of_compatible
#print axioms HaagerupIzumi.C8.CompatibleTop.compatible_top_sum
#print axioms HaagerupIzumi.C8.CompatibleTop.commutator_step
#print axioms HaagerupIzumi.C8.CompatibleTop.vacuum_top_step
#print axioms HaagerupIzumi.C8.VacuumLike.vacuumLike_section
#print axioms HaagerupIzumi.C8.Branching.e6_diagram_automorphisms
#print axioms HaagerupIzumi.C8.Weights.free_induction_hom_count
-- Analytic comparison (Appendix I)
#print axioms HaagerupIzumi.C8.graphReduction
#print axioms HaagerupIzumi.C8.analytic_inverse_domain
#print axioms HaagerupIzumi.C8.net_eq_of_haagDuality
#print axioms HaagerupIzumi.C8.AnalyticContinuation.continuation
-- Lattice data
#print axioms HaagerupIzumi.C8.Lattice.form_self_pos
#print axioms HaagerupIzumi.C8.Lattice.det_gram
#print axioms HaagerupIzumi.C8.Sl2.singletProjector_apply
-- Added after review
#print axioms HaagerupIzumi.C8.CoreTops.lowest_weight_le_of_trace
#print axioms HaagerupIzumi.C8.CubeRootTwists.eq_one_of_weighted_sum
#print axioms HaagerupIzumi.C8.RankFour.rank_four_excluded
#print axioms HaagerupIzumi.C8.RankFour.nearGroup_m0_impossible
#print axioms HaagerupIzumi.C8.PF13.pf13_reconstruction
-- Added 1 October 2026 (evening): cited statements in place of pre-evaluated hypotheses
#print axioms HaagerupIzumi.C8.VacuumProjective.L0_commutator
#print axioms HaagerupIzumi.C8.VacuumProjective.module_commutator_step
#print axioms HaagerupIzumi.C8.VacuumProjective.exists_vacuum_preimage
#print axioms HaagerupIzumi.C8.VacuumProjective.act_mem_maxGenEigenspace
#print axioms HaagerupIzumi.C8.VacuumProjective.omega_vacuumLike_section
#print axioms HaagerupIzumi.C8.VacuumProjective.maxGenEigenspace_eq_bot_of_filtration
#print axioms HaagerupIzumi.C8.VacuumProjective.lowering_mode_eq_zero
#print axioms HaagerupIzumi.C8.Fusion.m6_balanced_impossible_of_modular
#print axioms HaagerupIzumi.C8.TwistTraces.indicator_moments_of_trace
#print axioms HaagerupIzumi.C8.TwistTraces.neargroup_moments_of_trace
#print axioms HaagerupIzumi.C8.TwistTraces.neargroup_moments_gen
#print axioms HaagerupIzumi.C8.CenterDimension.rank6_length_of_center
#print axioms HaagerupIzumi.C8.CenterDimension.nearGroup_length_of_center
-- W4 (1 October 2026): Galois averaging; lem:conductor40 and the orbit step of lem:six-residual-twists
#print axioms HaagerupIzumi.C8.NumberTheory.conductor40Bound
#print axioms HaagerupIzumi.C8.NumberTheory.nonresidueOrbitStep
#print axioms HaagerupIzumi.C8.NumberTheory.six_residual_twists_proved
#print axioms HaagerupIzumi.C8.NumberTheory.multiplicity_eq_one_of_larson
#print axioms HaagerupIzumi.C8.NumberTheory.rank6_multiplicity_one_and_twists_of_larson
#print axioms HaagerupIzumi.C8.NumberTheory.larsonRootCount
#print axioms HaagerupIzumi.C8.NumberTheory.multiplicity_eq_one_unconditional
#print axioms HaagerupIzumi.C8.NumberTheory.rank6_multiplicity_one_and_twists_unconditional
#print axioms HaagerupIzumi.C8.NumberTheory.six_residual_twists_literal
-- W5 (1 October 2026): PF13 Wick claims A₆, A₇, A₈, B₇; unconditional prop:pf13-finite-reconstruction
#print axioms HaagerupIzumi.C8.PF13Wick.Data.claims
#print axioms HaagerupIzumi.C8.PF13Wick.Data.all_pairs
#print axioms HaagerupIzumi.C8.PF13Wick.pf13_reconstruction'
#print axioms HaagerupIzumi.C8.PF13Wick.pf13_reconstruction_of_rows
-- W1 (1 October 2026): computable Fock model of V_{E6+A2}, cross-checked against the Python engine
#print axioms HaagerupIzumi.C8.LatticeVOA.toFock_mode
#print axioms HaagerupIzumi.C8.LatticeVOA.norm_eq_two_iff
#print axioms HaagerupIzumi.C8.LatticeVOA.certDimensions_model
#print axioms HaagerupIzumi.C8.LatticeVOA.left_sl2
#print axioms HaagerupIzumi.C8.LatticeVOA.right_sl2
#print axioms HaagerupIzumi.C8.LatticeVOA.left_right_commute
#print axioms HaagerupIzumi.C8.LatticeVOA.central_charge
-- W2(c): the lattice VOA from the single hypothesis FLMInput (Borcherds identity, L(0), L(-1))
#print axioms HaagerupIzumi.C8.LatticeVOA.latticeVOA
#print axioms HaagerupIzumi.C8.LatticeVOA.certDimensions_lattice
-- W8 categorical: monoidal automorphisms of the identity on the rank-six ring
#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.monoidalAut_eq_refl
#print axioms HaagerupIzumi.C8.Fusion.IsHIRing.monoidalIso_eq
-- W7 (1 October 2026): 17 of the 30 L_ arrows proved for concrete nodes
#print axioms HaagerupIzumi.C8.ProofMap.boundary_arrows
#print axioms HaagerupIzumi.C8.ProofMap.character_arrows
#print axioms HaagerupIzumi.C8.ProofMap.pf13_arrow
#print axioms HaagerupIzumi.C8.ProofMap.regularity_arrows
#print axioms HaagerupIzumi.C8.ProofMap.topBound_arrow
#print axioms HaagerupIzumi.C8.ProofMap.stronglyUnitary_arrow
#print axioms HaagerupIzumi.C8.ProofMap.inputs_of_concrete
#print axioms HaagerupIzumi.C8.ProofMap.concrete_proof_map
-- W6 phase 1 (1 October 2026): multi-dimensional Poisson summation, lattice theta transformations
#print axioms HaagerupIzumi.C8.Theta.tsum_eq_tsum_fourierPi
#print axioms HaagerupIzumi.C8.Theta.latticeTheta_S
#print axioms HaagerupIzumi.C8.Theta.latticeTheta_T
#print axioms HaagerupIzumi.C8.Theta.latticeThetaQ_S
#print axioms HaagerupIzumi.C8.Theta.mdifferentiable_latticeThetaQ
#print axioms HaagerupIzumi.C8.Theta.covariant_of_S_T
-- W8 categorical: free-module adjunction; free induction on the three simples of L₋ (L_untwisted)
#print axioms HaagerupIzumi.C8.RightMod.freeAdjunction
#print axioms HaagerupIzumi.C8.RightMod.finrank_hom_free
#print axioms HaagerupIzumi.C8.RightMod.freeMap_bijective_Lminus
#print axioms HaagerupIzumi.C8.RightMod.retractFree
#print axioms HaagerupIzumi.C8.RightMod.freeTensorIso
-- Whole-proof skeleton
#print axioms HaagerupIzumi.C8.ProofMap.thm_main_net
#print axioms HaagerupIzumi.C8.ProofMap.thm_claim_main
