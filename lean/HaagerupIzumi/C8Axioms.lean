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
-- Whole-proof skeleton
#print axioms HaagerupIzumi.C8.ProofMap.thm_main_net
#print axioms HaagerupIzumi.C8.ProofMap.thm_claim_main
