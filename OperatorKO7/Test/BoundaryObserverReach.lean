import OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation
import OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation
import OperatorKO7.Meta.BoundaryObserver.InstrumentComposition
import OperatorKO7.Meta.BoundaryObserver.BurdenTail
import OperatorKO7.Meta.BoundaryObserver.BurdenGibbs
import OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit
import OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction
import OperatorKO7.Meta.BoundaryObserver.ObserverRepair
import OperatorKO7.Meta.BoundaryObserver.DynamicStopping
import OperatorKO7.Meta.BoundaryObserver.InstrumentLoss
import OperatorKO7.Meta.BoundaryObserver.StochasticGraph
import OperatorKO7.Meta.BoundaryObserver.GaussianTotals
import OperatorKO7.Meta.BoundaryObserver.ObservationLimits
import OperatorKO7.Meta.BoundaryObserver.DiagonalObservation
import OperatorKO7.Meta.BoundaryObserver.TupleInvariants
import OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation
import OperatorKO7.Meta.BoundaryObserver.MergedPair
import OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest
import OperatorKO7.Meta.BoundaryObserver.PairInvariants
import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
import OperatorKO7.Meta.BoundaryObserver.BitDivision
import OperatorKO7.Meta.BoundaryObserver.NoReturn
import OperatorKO7.Meta.BoundaryObserver.KernelCases
import OperatorKO7.Meta.BoundaryObserver.Instances.KernelCases
import OperatorKO7.Meta.BoundaryObserver.SharedRecordPair
import OperatorKO7.Meta.BoundaryObserver.FourTestTables
import OperatorKO7.Meta.BoundaryObserver.ObserverRealization
import OperatorKO7.Meta.BoundaryObserver.NoisyResolution
import OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice

/-!
Reach and axiom gate for the imported Observation Principle modules.
Every explicit public declaration has a `#check @` and a `#print axioms`.
The controls test empty transcripts, absent signal, noiseless readings, and odd/even majorities.

Proof graph: `Audit/ledgers/operational-inexpressibility/TWO-VOIDS-PROOF-GRAPH.md`, node M8.
-/

#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.Determines
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.IsMergedPair
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.boundary
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.isMergedPair_bool_const
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.isMergedPair_void_occurrences
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.determines_iff_no_collision
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.determines_iff_invariant
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.same_record_iff_orbit
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.determines_id_iff_injective
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.transGen_least_kernel
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.apart_irrefl_symm_cotrans
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.apartness_is_kernel_complement
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.boundary_eq_empty_iff_injective
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_tests_through_record
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_separating_tests
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.swap_invariant_relation_iff
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.distinct_swap_invariant
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.distinct_not_from_invariant_tests
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_side_symbol
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_restriction
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_no_comparison_decoder
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_comparison_decoder
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.test_const_of_subsingleton
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.two_points_of_separating_test
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.unit_occurrences
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.no_invariant_choice
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.no_orientation_of_exchange
#check @OperatorKO7.Meta.BoundaryObserver.PairInvariants.pair_orbit_iff
#check @OperatorKO7.Meta.BoundaryObserver.PairInvariants.pair_invariant_iff
#check @OperatorKO7.Meta.BoundaryObserver.PairInvariants.exists_stabilizer_matching_finsets
#check @OperatorKO7.Meta.BoundaryObserver.PairInvariants.finset_orbit_iff
#check @OperatorKO7.Meta.BoundaryObserver.PairInvariants.point_stabilizer_transitive
#check @OperatorKO7.Meta.BoundaryObserver.PairInvariants.point_stabilizer_invariant_iff
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.content_place_injective
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.content_place_join
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.content_class_meets_place_class
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.occurrence_trichotomy
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.exists_place_coordinate_iff
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.PlaceCoord
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.placeCoord_const_id
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.placeCoord_pair_bijective
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.stabilizer_symm_bijOn_class
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.placeCoord_smul_mem
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.placeCoord_free
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.placeCoord_transitive
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.labelling_member_bijective
#check @OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.labelling_member_equivariant
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_eq_H
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.negMulLog_half
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_uniform
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.negMulLog_add_le
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.log_eq_binEntropy_add
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.selfTest_one_bit_iff
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.readingJoint
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.readingJoint_same
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.readingJoint_diff
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.readingJoint_marginal_reading
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.readingJoint_marginal_label
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_const_half
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_readingJoint
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.reading_condEntropy
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.reading_mutualInfo
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.reading_independent_iff
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.reading_exact_iff
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.one_sub_binEntropy_expansion
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.repeat_same_kernel
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.readingsJoint
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.sum_prod_bool
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.sum_negMulLog_prod_bool
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.readingWeight_sum
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.readingWeight_entropy
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.readingsJoint_marginal_label
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_readingsJoint
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.readings_mutualInfo_le
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.minority_weight_sq_le
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.majority_error_le
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.fiber_card_sum
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.condEntropy_uniform
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.condEntropy_uniform_eq_log_card_iff
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.condEntropy_uniform_eq_zero_iff
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.licenseStabilizer_eq_top_iff
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.licenseStabilizer_eq_bot_iff
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.invariant_law_uniform
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_eq_log_card_iff
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.pair_system_log_card
#check @OperatorKO7.Meta.BoundaryObserver.BitDivision.pair_condEntropy_one_bit
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.left_inverse_iff_injective
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.exists_inverting_record_iff
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.recordChoice
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.recordChoice_idempotent
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.exists_record_section
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.injective_idempotent_eq_id
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.infinite_seq_of_return
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.no_return_of_no_infinite_seq
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.step_not_undone_of_no_infinite_seq
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.succ_no_return_and_infinite
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.return_iff_infinite_seq_of_finite
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.stepCtxFull_no_infinite_seq
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.stepCtxFull_not_undone
#check @OperatorKO7.Meta.BoundaryObserver.NoReturn.step_not_undone
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqRefl_fires_iff
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqDiff_fires
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_root_reducts
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes_pos
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes_eq_one_iff
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.frame_pair_to_frame
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.empty_frame_normal
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.empty_frame_ne_blank
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.double_frame_normal
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_step_closed
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_reducts
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_normal_forms
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.guarded_diff_only_distinct
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.guarded_diff_fires_on_distinct
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.numeral
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.spine
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.descend
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.frameCopy
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.spine_ctx_step
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.spine_app
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.unroll_steps
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.descend_spine_add
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.descend_spine
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.frameCopy_spine
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.O
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.O_zero
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.O_succ
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.O_unroll
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.counter_test_not_determined
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.counter_merged_pair
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.observed_test_separates_iff
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.observed_test_adjacent_iff
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.step_copies_merged_pair
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.self_step_infinite_seq
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.formula_ne_not
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.godel_merged_pair
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.godel_side_symbol_iff
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.godel_restriction
#check @OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairJoint
#check @OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairPostRecord
#check @OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairJoint_eq_shared_flip
#check @OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairJoint_not_product
#check @OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairPostRecord_product
#check @OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairJoint_mixture
#check @OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.perm_bool_eq
#check @OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairJoint_from_labellings
#check @OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.indicator_sum_bool
#check @OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.left_marginal_setting_free
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.Table
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.corr
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.score
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.CycleIneq
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.HasObserver
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.HasVectors
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.refused0
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.refused1
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.disagree
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.boolSign
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.boolSign_sq
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.boolSign_mul
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.zeroTable_hasObserver
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.cycle_parity
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.disagree_cycle
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.observer_cycleIneq
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.observer_abs_score_le_two
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.score_eq_refused
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.one_symbol_two_bits
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.observer_refused_ge_half
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.norm_vec2
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.inner_vec2
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.norm_vec3
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.inner_vec3
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.observer_hasVectors
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.arccos_inner_triangle
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.arccos_inner_four_cycle
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.exists_third_vector
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.hasVectors_iff_angle_cycle
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_quadratic
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_kept_refused
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_abs_excess_le
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_refused_ge
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_abs_score_le
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.one_sub_binEntropy_le_sq
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_bits_le_one
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.extremeTable
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.inv_sqrt_two_sq
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.extremeTable_hasVectors
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.extremeTable_score
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.extremeTable_refused
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.extremeTable_not_observer
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.cornerTable
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.cornerTable_score
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.cornerTable_not_vectors
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.kept_refused_identity
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.kept_refused_eq_amplitude
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.labelMat
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.swapMat
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.labelMat_mul_self
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.swapMat_mul_self
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.label_swap_anticommute
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.label_swap_trace
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.unit_combination_mul_self
#check @OperatorKO7.Meta.BoundaryObserver.FourTestTables.hasVectors_iff_psd_completion

#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.Determines
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.IsMergedPair
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.boundary
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.isMergedPair_bool_const
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.isMergedPair_void_occurrences
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.determines_iff_no_collision
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.determines_iff_invariant
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.same_record_iff_orbit
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.determines_id_iff_injective
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.transGen_least_kernel
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.apart_irrefl_symm_cotrans
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.apartness_is_kernel_complement
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.boundary_eq_empty_iff_injective
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_tests_through_record
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_separating_tests
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.swap_invariant_relation_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.distinct_swap_invariant
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.distinct_not_from_invariant_tests
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_side_symbol
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_restriction
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_no_comparison_decoder
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.mergedPair_comparison_decoder
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.test_const_of_subsingleton
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.two_points_of_separating_test
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.unit_occurrences
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.no_invariant_choice
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.no_orientation_of_exchange
#print axioms OperatorKO7.Meta.BoundaryObserver.PairInvariants.pair_orbit_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.PairInvariants.pair_invariant_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.PairInvariants.exists_stabilizer_matching_finsets
#print axioms OperatorKO7.Meta.BoundaryObserver.PairInvariants.finset_orbit_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.PairInvariants.point_stabilizer_transitive
#print axioms OperatorKO7.Meta.BoundaryObserver.PairInvariants.point_stabilizer_invariant_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.content_place_injective
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.content_place_join
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.content_class_meets_place_class
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.occurrence_trichotomy
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.exists_place_coordinate_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.PlaceCoord
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.placeCoord_const_id
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.placeCoord_pair_bijective
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.stabilizer_symm_bijOn_class
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.placeCoord_smul_mem
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.placeCoord_free
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.placeCoord_transitive
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.labelling_member_bijective
#print axioms OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates.labelling_member_equivariant
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_eq_H
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.negMulLog_half
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_uniform
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.negMulLog_add_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.log_eq_binEntropy_add
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.selfTest_one_bit_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.readingJoint
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.readingJoint_same
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.readingJoint_diff
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.readingJoint_marginal_reading
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.readingJoint_marginal_label
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_const_half
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_readingJoint
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.reading_condEntropy
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.reading_mutualInfo
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.reading_independent_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.reading_exact_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.one_sub_binEntropy_expansion
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.repeat_same_kernel
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.readingsJoint
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.sum_prod_bool
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.sum_negMulLog_prod_bool
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.readingWeight_sum
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.readingWeight_entropy
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.readingsJoint_marginal_label
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_readingsJoint
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.readings_mutualInfo_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.minority_weight_sq_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.majority_error_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.fiber_card_sum
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.condEntropy_uniform
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.condEntropy_uniform_eq_log_card_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.condEntropy_uniform_eq_zero_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.licenseStabilizer_eq_top_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.licenseStabilizer_eq_bot_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.invariant_law_uniform
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.entropy_eq_log_card_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.pair_system_log_card
#print axioms OperatorKO7.Meta.BoundaryObserver.BitDivision.pair_condEntropy_one_bit
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.left_inverse_iff_injective
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.exists_inverting_record_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.recordChoice
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.recordChoice_idempotent
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.exists_record_section
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.injective_idempotent_eq_id
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.infinite_seq_of_return
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.no_return_of_no_infinite_seq
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.step_not_undone_of_no_infinite_seq
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.succ_no_return_and_infinite
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.return_iff_infinite_seq_of_finite
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.stepCtxFull_no_infinite_seq
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.stepCtxFull_not_undone
#print axioms OperatorKO7.Meta.BoundaryObserver.NoReturn.step_not_undone
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqRefl_fires_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqDiff_fires
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_root_reducts
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes_eq_one_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.frame_pair_to_frame
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.empty_frame_normal
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.empty_frame_ne_blank
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.double_frame_normal
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_step_closed
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_reducts
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_normal_forms
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.guarded_diff_only_distinct
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.guarded_diff_fires_on_distinct
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.numeral
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.spine
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.descend
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.frameCopy
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.spine_ctx_step
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.spine_app
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.unroll_steps
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.descend_spine_add
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.descend_spine
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.frameCopy_spine
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.O
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.O_zero
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.O_succ
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.O_unroll
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.counter_test_not_determined
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.counter_merged_pair
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.observed_test_separates_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.observed_test_adjacent_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.step_copies_merged_pair
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.self_step_infinite_seq
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.formula_ne_not
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.godel_merged_pair
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.godel_side_symbol_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.godel_restriction
#print axioms OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairJoint
#print axioms OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairPostRecord
#print axioms OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairJoint_eq_shared_flip
#print axioms OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairJoint_not_product
#print axioms OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairPostRecord_product
#print axioms OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairJoint_mixture
#print axioms OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.perm_bool_eq
#print axioms OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.pairJoint_from_labellings
#print axioms OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.indicator_sum_bool
#print axioms OperatorKO7.Meta.BoundaryObserver.SharedRecordPair.left_marginal_setting_free
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.Table
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.corr
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.score
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.CycleIneq
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.HasObserver
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.HasVectors
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.refused0
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.refused1
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.disagree
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.boolSign
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.boolSign_sq
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.boolSign_mul
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.zeroTable_hasObserver
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.cycle_parity
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.disagree_cycle
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.observer_cycleIneq
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.observer_abs_score_le_two
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.score_eq_refused
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.one_symbol_two_bits
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.observer_refused_ge_half
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.norm_vec2
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.inner_vec2
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.norm_vec3
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.inner_vec3
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.observer_hasVectors
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.arccos_inner_triangle
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.arccos_inner_four_cycle
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.exists_third_vector
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.hasVectors_iff_angle_cycle
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_quadratic
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_kept_refused
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_abs_excess_le
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_refused_ge
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_abs_score_le
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.one_sub_binEntropy_le_sq
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.vectors_bits_le_one
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.extremeTable
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.inv_sqrt_two_sq
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.extremeTable_hasVectors
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.extremeTable_score
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.extremeTable_refused
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.extremeTable_not_observer
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.cornerTable
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.cornerTable_score
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.cornerTable_not_vectors
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.kept_refused_identity
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.kept_refused_eq_amplitude
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.labelMat
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.swapMat
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.labelMat_mul_self
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.swapMat_mul_self
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.label_swap_anticommute
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.label_swap_trace
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.unit_combination_mul_self
#print axioms OperatorKO7.Meta.BoundaryObserver.FourTestTables.hasVectors_iff_psd_completion

-- M10: finite observer construction, including the Fine converse.
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.hasObserver_of_fintype
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.sum_glue_left
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.sum_glue_right
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.binaryRow
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.binaryMass
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.binaryRow_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.binaryRow_sum
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.cycle_common_rate
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.observer_of_cycle
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.hasObserver_iff_cycle
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.hasObserver_of_fintype
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.sum_glue_left
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.sum_glue_right
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.binaryRow
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.binaryMass
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.binaryRow_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.binaryRow_sum
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.cycle_common_rate
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.observer_of_cycle
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.hasObserver_iff_cycle

-- M11: exact finite recovery versus reliable majority decoding.
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.readingsJoint_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.readingsJoint_pos
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.decoderError
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.decoderError_eq_sum
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.readingsJoint_lower
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.decoderError_lower
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.decoderError_pos
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.no_finite_exact_decoder
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.decoderError_zero_signal
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.majorityDecoder
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.majority_wrong_iff
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.majority_decoder_error_le
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.arbitrarily_reliable_majority
#check @OperatorKO7.Meta.BoundaryObserver.NoisyResolution.finite_exact_vs_reliable
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.readingsJoint_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.readingsJoint_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.decoderError
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.decoderError_eq_sum
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.readingsJoint_lower
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.decoderError_lower
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.decoderError_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.no_finite_exact_decoder
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.decoderError_zero_signal
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.majorityDecoder
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.majority_wrong_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.majority_decoder_error_le
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.arbitrarily_reliable_majority
#print axioms OperatorKO7.Meta.BoundaryObserver.NoisyResolution.finite_exact_vs_reliable

section NoisyControls
open OperatorKO7.Meta.BoundaryObserver.BitDivision
open OperatorKO7.Meta.BoundaryObserver.NoisyResolution
example (ε : ℝ) (b : Bool) : readingsJoint 0 ε b (fun i => Fin.elim0 i) = 1 / 2 := by
  simp [readingsJoint]
example : decoderError 0 0 (fun _ => true) = 1 / 2 := decoderError_zero_signal 0 _
example : readingsJoint 1 (1 / 2) false (fun _ => true) = 0 := by
  norm_num [readingsJoint]
example : majorityDecoder 2 ![true, false] = false := by decide
example : majorityDecoder 3 ![true, false, true] = true := by decide
example : ∀ N decode, 0 < decoderError N (1 / 4) decode :=
  fun N decode => decoderError_pos N (1 / 4) (by norm_num) (by norm_num) decode
end NoisyControls

-- V4: one record alphabet for comparison and repeat depth.
#check @OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.comparison_iff_repeatDepth
#check @OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.rank_channel_supports_comparison
#check @OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.comparison_channel_card_lower
#check @OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.repeatDepth_channel_of_capacity
#check @OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.comparison_channel_exists_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.comparison_and_recurrence_same_alphabets
#check @OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.comparison_minimum_eq_recurrence
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.comparison_iff_repeatDepth
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.rank_channel_supports_comparison
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.comparison_channel_card_lower
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.repeatDepth_channel_of_capacity
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.comparison_channel_exists_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.comparison_and_recurrence_same_alphabets
#print axioms OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice.comparison_minimum_eq_recurrence

section ComparisonControls
open OperatorKO7.Meta.OperationalInexpressibility.RepeatDepthLicense
open OperatorKO7.Meta.OperationalInexpressibility.ComparisonRecurrencePrice
open OperatorKO7.Meta.DistinctionBoundary.ObservationalDiagonalFork
example : maxFiberCard (constantObserver 2) = 2 := maxFiberCard_constantObserver 2
example : maxFiberCard (fun i : Fin 3 => decide (i = 2)) = 2 := by decide
example : ∃ r : Fin 0 → Fin 0, ∃ decoder,
    ObservedDecoderCorrect (fun i => (constantObserver 0 i, r i)) decoder := by
  apply (comparison_channel_exists_iff (constantObserver 0) 0).mpr
  simp
example : ¬ (∃ r : Fin 3 → Fin 1, ∃ decoder,
    ObservedDecoderCorrect (fun i => (decide (i = (2 : Fin 3)), r i)) decoder) := by
  rw [comparison_channel_exists_iff]
  decide
end ComparisonControls

-- Checked source declarations: ObserverRealization.
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.Realizable
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.Realizable
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.realizable_iff_mem_convexHull
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.realizable_iff_mem_convexHull
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.reportScore
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.reportScore
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.functional_eq_reportScore
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.functional_eq_reportScore
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.score_le_of_realizable
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.score_le_of_realizable
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.not_realizable_iff_separating_score
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.not_realizable_iff_separating_score
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.common_law_or_certificate
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.common_law_or_certificate
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.separating_score_repair_bound
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.separating_score_repair_bound
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.contextVector
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.contextVector
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.context_realizable_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.context_realizable_iff
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.context_law_or_certificate
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.context_law_or_certificate
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.realizable_of_hidden
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.realizable_of_hidden
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.realizable_iff_reindex
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.realizable_iff_reindex
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.realizable_vertex
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.realizable_vertex
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangleReport
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangleReport
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangle_score_le
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangle_score_le
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangle_not_realizable
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangle_not_realizable
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangle_repair_lower
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangle_repair_lower
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangle_optimal_repair
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRealization.triangle_optimal_repair

-- Checked source declarations: AdmissibleObservation.
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.run
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.run
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureRecord
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureRecord
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.FutureEq
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.FutureEq
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.run_append
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.run_append
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureEq_observation
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureEq_observation
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureEq_step
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureEq_step
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.relation_le_futureEq
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.relation_le_futureEq
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureEq_greatest
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureEq_greatest
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureSetoid
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureSetoid
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.MinimalState
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.MinimalState
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalRecord
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalRecord
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalRead
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalRead
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalStep
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalStep
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalRecord_eq_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalRecord_eq_iff
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalRead_record
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalRead_record
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalStep_record
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimalStep_record
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.monitor_kernel_le_futureEq
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.monitor_kernel_le_futureEq
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimal_observer_universal
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimal_observer_universal
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimal_factor_surjective
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimal_factor_surjective
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureEq_eq_current_of_compatible
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureEq_eq_current_of_compatible
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.no_continuous_discrete_repair
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.no_continuous_discrete_repair
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.square_sign_injective
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.square_sign_injective
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.square_no_continuous_discrete_label
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.square_no_continuous_discrete_label
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.Experiment
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.Experiment
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.evaluate
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.evaluate
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.evaluate_eq_of_futureEq
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.evaluate_eq_of_futureEq
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.wordExperiment
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.wordExperiment
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.evaluate_word
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.evaluate_word
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureEq_iff_all_adaptive
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.futureEq_iff_all_adaptive
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.not_futureEq_iff_word
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.not_futureEq_iff_word
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.resolving_event_requires_new_distinction
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.resolving_event_requires_new_distinction
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimal_factor_commutes
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.minimal_factor_commutes
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.no_new_distinction_of_closed_record
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.no_new_distinction_of_closed_record
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.distinguishing_word_has_boundary_event
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.distinguishing_word_has_boundary_event
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.adaptive_resolution_has_boundary_event
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.adaptive_resolution_has_boundary_event
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.no_adaptive_solver_of_collision
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.no_adaptive_solver_of_collision
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.DestructiveState
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.DestructiveState
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructiveRead
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructiveRead
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructiveStep
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructiveStep
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructive_initials_distinguishable
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructive_initials_distinguishable
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.two_other_indices
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.two_other_indices
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructive_no_single_run_identifier
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructive_no_single_run_identifier
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.trialRecord
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.trialRecord
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.independent_trials_identify
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.independent_trials_identify
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructive_minimal_record_injective
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructive_minimal_record_injective

-- Checked source declarations: TupleInvariants.
#check @OperatorKO7.Meta.BoundaryObserver.TupleInvariants.match_finite_tuple
#print axioms OperatorKO7.Meta.BoundaryObserver.TupleInvariants.match_finite_tuple
#check @OperatorKO7.Meta.BoundaryObserver.TupleInvariants.tuple_orbit_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.TupleInvariants.tuple_orbit_iff
#check @OperatorKO7.Meta.BoundaryObserver.TupleInvariants.tuple_invariant_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.TupleInvariants.tuple_invariant_iff
#check @OperatorKO7.Meta.BoundaryObserver.TupleInvariants.independent_invariant_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.TupleInvariants.independent_invariant_iff
#check @OperatorKO7.Meta.BoundaryObserver.TupleInvariants.shared_reference_is_necessary
#print axioms OperatorKO7.Meta.BoundaryObserver.TupleInvariants.shared_reference_is_necessary
#check @OperatorKO7.Meta.BoundaryObserver.TupleInvariants.empty_tuple_orbit
#print axioms OperatorKO7.Meta.BoundaryObserver.TupleInvariants.empty_tuple_orbit

-- Checked source declarations: DiagonalObservation.
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.Represented
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.Represented
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.diagonal
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.diagonal
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.diagonal_not_represented
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.diagonal_not_represented
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.evaluator_not_surjective
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.evaluator_not_surjective
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.boolean_diagonal_missing
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.boolean_diagonal_missing
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.quotation_fails_at_diagonal
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.quotation_fails_at_diagonal
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.no_internal_self_evaluator
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.no_internal_self_evaluator
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.no_internal_boolean_self_evaluator
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.no_internal_boolean_self_evaluator
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.no_complete_same_carrier_observer
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.no_complete_same_carrier_observer
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.externalRead
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.externalRead
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.externalRead_complete
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.externalRead_complete
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.no_total_quote_back
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.no_total_quote_back
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.fixed_pair_separator
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.fixed_pair_separator
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.pair_separation_not_uniform_truth
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.pair_separation_not_uniform_truth
#check @OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.constant_language_has_self_evaluator
#print axioms OperatorKO7.Meta.BoundaryObserver.DiagonalObservation.constant_language_has_self_evaluator

-- Checked source declarations: ObservationLimits.
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.tagged_cardinality
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.tagged_cardinality
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.independent_cardinality
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.independent_cardinality
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.independent_larger_than_tagged
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.independent_larger_than_tagged
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.tagged_independent_small_cases
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.tagged_independent_small_cases
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.coherentState
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.coherentState
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.mixedState
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.mixedState
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.coherentState_posSemidef
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.coherentState_posSemidef
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.mixedState_posSemidef
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.mixedState_posSemidef
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.state_traces
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.state_traces
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.same_label_probabilities
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.same_label_probabilities
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.both_exchange_invariant
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.both_exchange_invariant
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.swap_distinguishes_states
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.swap_distinguishes_states
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.symmetry_does_not_determine_coherence
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.symmetry_does_not_determine_coherence
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.no_return_without_information_loss
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.no_return_without_information_loss
#check @OperatorKO7.Meta.BoundaryObserver.ObservationLimits.erasure_with_zero_assigned_cost
#print axioms OperatorKO7.Meta.BoundaryObserver.ObservationLimits.erasure_with_zero_assigned_cost

-- Checked source declarations: GaussianTotals.
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.axisLinear
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.axisLinear
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.varianceParameter
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.varianceParameter
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum_isGaussian
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum_isGaussian
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.axis_projection
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.axis_projection
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum_projection
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum_projection
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.varianceParameter_coe
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.varianceParameter_coe
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum_mean
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum_mean
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum_variance
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum_variance
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum_covariance
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussianSum_covariance
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.covarianceMatrix
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.covarianceMatrix
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.covarianceMatrix_posSemidef
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.covarianceMatrix_posSemidef
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.matrixLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.matrixLaw
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.matrixLaw_isGaussian
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.matrixLaw_isGaussian
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.matrixLaw_mean
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.matrixLaw_mean
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.matrixLaw_covariance
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.matrixLaw_covariance
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.psd_iff_gaussian_covariance
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.psd_iff_gaussian_covariance
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.HasGaussianTotals
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.HasGaussianTotals
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.hasVectors_iff_gaussianTotals
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.hasVectors_iff_gaussianTotals
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.common_moments_imply_vectors
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.common_moments_imply_vectors
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.linear_report_coordinates
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.linear_report_coordinates
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.linear_mean_coordinates
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.linear_mean_coordinates
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.linear_variance_coordinates
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.linear_variance_coordinates
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussian_eq_of_moments
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussian_eq_of_moments
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.selectCoordinates
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.selectCoordinates
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.selected_covariance
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.selected_covariance
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.selected_mean
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.selected_mean
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pairNormal
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pairNormal
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pairNormal_isGaussian
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pairNormal_isGaussian
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pairNormal_mean
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pairNormal_mean
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pairNormal_covariance
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pairNormal_covariance
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussian_pair_marginal
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.gaussian_pair_marginal
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pair_marginal_memLp
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pair_marginal_memLp
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pair_marginal_covariance
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.pair_marginal_covariance
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.HasPairMarginals
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.HasPairMarginals
#check @OperatorKO7.Meta.BoundaryObserver.GaussianTotals.hasVectors_iff_pairMarginals
#print axioms OperatorKO7.Meta.BoundaryObserver.GaussianTotals.hasVectors_iff_pairMarginals

#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.executedTrace
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.executedTrace

#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.actual_resolution_has_boundary_event
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.actual_resolution_has_boundary_event

#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.executedTrace_eq_of_futureEq
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.executedTrace_eq_of_futureEq

-- M14c: finite independent experiments, sharp trial count, and destructive-run obstruction.
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.no_identifier_of_first_step_collision
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.no_identifier_of_first_step_collision
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.equalityTrials
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.equalityTrials
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.equalityTrials_eq_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.equalityTrials_eq_iff
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.equalityTrials_injective_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.equalityTrials_injective_iff
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.equalityTrials_injective_iff_card
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.equalityTrials_injective_iff_card
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.equalityTrials_erase_identifies
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.equalityTrials_erase_identifies
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.trialRecord_eq_equalityTrial
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.trialRecord_eq_equalityTrial
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructive_independent_trial_threshold
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.destructive_independent_trial_threshold
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.finite_separating_tests
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.finite_separating_tests
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.finite_independent_bank_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.finite_independent_bank_iff
#check @OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.finite_behavioral_record_realization
#print axioms OperatorKO7.Meta.BoundaryObserver.AdmissibleObservation.finite_behavioral_record_realization

-- BEGIN Observation extensions

-- StochasticGraph
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.Channel
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.Channel
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.conflictGraph
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.conflictGraph
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.Decodes
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.Decodes
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.decoder_iff_coloring
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.decoder_iff_coloring
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.colorable_iff_decoder
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.colorable_iff_decoder
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.chromaticNumber_le_iff_decoder
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.chromaticNumber_le_iff_decoder
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.deterministic
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.deterministic
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.deterministic_graph
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.deterministic_graph
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.common_output_decoder_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.common_output_decoder_iff
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.repeated
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.repeated
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.repeated_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.repeated_pos
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.full_support_repetition_decoder_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.full_support_repetition_decoder_iff
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycleChannel
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycleChannel
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycleAdjacent
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycleAdjacent
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycleAdjacentDecidable
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycleAdjacentDecidable
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_positive
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_positive
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_graph
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_graph
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_output_support
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_output_support
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_no_two_colors
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_no_two_colors
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_three_colors
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_three_colors
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_no_binary_decoder
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_no_binary_decoder
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_ternary_decoder
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.cycle_ternary_decoder
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.repeatedChannel
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.repeatedChannel
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.readingsInformation
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.readingsInformation
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.readingsInformation_le_quadratic
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.readingsInformation_le_quadratic
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.information_target_cost
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.information_target_cost
#check @OperatorKO7.Meta.BoundaryObserver.StochasticGraph.bounded_budget_fails_near_zero
#print axioms OperatorKO7.Meta.BoundaryObserver.StochasticGraph.bounded_budget_fails_near_zero
-- InstrumentLoss
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.Instrument
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.Instrument
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.joint
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.joint
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.Recoverable
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.Recoverable
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.recoverable_iff_joint_injective
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.recoverable_iff_joint_injective
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.compose
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.compose
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.joint_compose_eq_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.joint_compose_eq_iff
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.joint_collision_persists
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.joint_collision_persists
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.compose_injective
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.compose_injective
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.first_injective_of_composite
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.first_injective_of_composite
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.compose_recoverable
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.compose_recoverable
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.silentKeep
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.silentKeep
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.silentErase
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.silentErase
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.readAndErase
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.readAndErase
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.equal_records_different_recovery
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.equal_records_different_recovery
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.retained_record_recovers_reset
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.retained_record_recovers_reset
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.StochasticInstrument
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.StochasticInstrument
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.outcomeLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.outcomeLaw
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.stateLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.stateLaw
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.outcomeLaw_normalized
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.outcomeLaw_normalized
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.stateLaw_normalized
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.stateLaw_normalized
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.randomRead
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.randomRead
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.randomRead_outcome
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.randomRead_outcome
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.randomRead_state
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.randomRead_state
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.same_outcome_different_state
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.same_outcome_different_state
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.StochasticRecoverable
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.StochasticRecoverable
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.randomRead_keep_recovers
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.randomRead_keep_recovers
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.randomRead_erase_not_recovers
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentLoss.randomRead_erase_not_recovers
-- DynamicStopping
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.returnAt
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.returnAt
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.value
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.value
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.stop_le_value
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.stop_le_value
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.return_le_value
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.return_le_value
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.value_attained
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.value_attained
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.horizon_monotone
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.horizon_monotone
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.stop_optimal_of_step_bound
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.stop_optimal_of_step_bound
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.stop_optimal_of_preserved_payoff
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.stop_optimal_of_preserved_payoff
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.continue_improves_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.continue_improves_iff
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.delayedStep
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.delayedStep
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.delayedRead
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.delayedRead
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.delayedPay
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.delayedPay
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.delayedCost
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.delayedCost
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.delayedPay_is_optimal
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.delayedPay_is_optimal
#check @OperatorKO7.Meta.BoundaryObserver.DynamicStopping.zero_current_gain_does_not_force_stop
#print axioms OperatorKO7.Meta.BoundaryObserver.DynamicStopping.zero_current_gain_does_not_force_stop
-- ObserverRepair
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.MaximalRepair
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.MaximalRepair
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.stable_pred_le_box
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.stable_pred_le_box
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.maximal_rel_saturated
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.maximal_rel_saturated
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.maximal_pred_saturated
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.maximal_pred_saturated
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.saturated_is_maximal
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.saturated_is_maximal
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.maximal_iff_saturated
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.maximal_iff_saturated
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.endpoint_repairs_maximal
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.endpoint_repairs_maximal
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.maximal_repairs_antichain
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.maximal_repairs_antichain
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.stateCount
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.stateCount
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.edgeCount
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.edgeCount
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.deletionCost
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.deletionCost
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.stateCount_mono
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.stateCount_mono
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.deletionCost_antitone
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.deletionCost_antitone
#check @OperatorKO7.Meta.BoundaryObserver.ObserverRepair.crossing_has_distinct_maximal_repairs
#print axioms OperatorKO7.Meta.BoundaryObserver.ObserverRepair.crossing_has_distinct_maximal_repairs
-- QuantumReconstruction
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.basis
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.basis
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.Hermitian
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.Hermitian
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form_basis
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form_basis
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form_add_left
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form_add_left
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form_add_right
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form_add_right
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form_scale_left
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form_scale_left
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form_scale_right
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.form_scale_right
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.population
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.population
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.plusReport
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.plusReport
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseReport
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseReport
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.population_entry
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.population_entry
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.plusReport_entry
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.plusReport_entry
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseReport_entry
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseReport_entry
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.reports_determine_state
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.reports_determine_state
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.State
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.State
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.state_population_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.state_population_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.state_plus_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.state_plus_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.state_phase_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.state_phase_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.state_equality_iff_reports
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.state_equality_iff_reports
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseMatrix
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseMatrix
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseMatrix_hermitian
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseMatrix_hermitian
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseMatrix_form
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseMatrix_form
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseState
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.phaseState
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.populations_do_not_determine_state
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.populations_do_not_determine_state
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.reconstruct
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.reconstruct
#check @OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.reconstruct_reports
#print axioms OperatorKO7.Meta.BoundaryObserver.QuantumReconstruction.reconstruct_reports
-- END Observation extensions

-- Complete Observation declaration coverage
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.sin_eq_mul_sinc
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.sin_eq_mul_sinc
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.cos_sub_one_sinc
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.cos_sub_one_sinc
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.sqrt_nat_tendsto
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.sqrt_nat_tendsto
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.scaled_cos_identity
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.scaled_cos_identity
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.scaled_cos_limit
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.scaled_cos_limit
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairKernel
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairKernel
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pair_kernel_variance_limit
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pair_kernel_variance_limit
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.normalized_pair_kernel_limit
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.normalized_pair_kernel_limit
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairOutcome
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairOutcome
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_sum
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_sum
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairPMF
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairPMF
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairLaw
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairLaw_isProbabilityMeasure
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairLaw_isProbabilityMeasure
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairReport
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairReport
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairLaw_integral
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairLaw_integral
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.exp_opposite_sum
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.exp_opposite_sum
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairLaw_charFun
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairLaw_charFun
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_nonnegative_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_nonnegative_iff
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_mean
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_mean
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_second_moment
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_second_moment
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_cross_moment
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_cross_moment
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_disagreement
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_disagreement
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_table_rate
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_table_rate
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairSumLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairSumLaw
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairSumLaw_succ
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairSumLaw_succ
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairSumLaw_isProbabilityMeasure
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairSumLaw_isProbabilityMeasure
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairSumLaw_charFun
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairSumLaw_charFun
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.normalizePair
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.normalizePair
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_isProbabilityMeasure
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_isProbabilityMeasure
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairReport_normalize
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairReport_normalize
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_charFun
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_charFun
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_characteristic_limit
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_characteristic_limit
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairNormal_charFun
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairNormal_charFun
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_tendsto_pairNormal_charFun
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_tendsto_pairNormal_charFun
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairReport_coordinates
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairReport_coordinates
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_all_characteristic_limit
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_all_characteristic_limit
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_zero
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_zero
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_one
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_one
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_zero_correlation
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_zero_correlation
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_outside_range
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairMass_outside_range
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.one_sub_pow_abs_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.one_sub_pow_abs_le
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.one_sub_cos_abs_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.one_sub_cos_abs_le
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.normalized_cos_increment_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.normalized_cos_increment_le
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_coordinate_charFun
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_coordinate_charFun
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.coordinate_characteristic_increment_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.coordinate_characteristic_increment_le
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.coordinate_tail_of_increment
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.coordinate_tail_of_increment
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_coordinate_tail
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_coordinate_tail
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.clampValue
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.clampValue
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.clampValue_abs_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.clampValue_abs_le
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.clampValue_eq_self
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.clampValue_eq_self
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.clampValue_error
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.clampValue_error
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.bounded_aeval_apply
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.bounded_aeval_apply
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.bounded_algebra_approximation
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.bounded_algebra_approximation
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.integral_approximation_bound
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.integral_approximation_bound
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.tight_algebra_integral_limit
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.tight_algebra_integral_limit
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.tight_charFunDual_limit
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.tight_charFunDual_limit
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_box_tail
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_box_tail
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_tight
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_tight
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalProbability
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalProbability
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairNormalProbability
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairNormalProbability
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_weak_limit
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_weak_limit
#check @OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_bounded_test_limit
#print axioms OperatorKO7.Meta.BoundaryObserver.BinaryPairLimit.pairTotalLaw_bounded_test_limit
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.partition
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.partition
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.partition_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.partition_pos
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbsLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbsLaw
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_pos
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.log_gibbs
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.log_gibbs
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.expectedCost
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.expectedCost
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.entropyMinusCost
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.entropyMinusCost
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_gap_identity
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_gap_identity
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.finite_divergence_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.finite_divergence_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.neg_divergence_term_lt
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.neg_divergence_term_lt
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.finite_divergence_eq_zero_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.finite_divergence_eq_zero_iff
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_objective
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_objective
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_unique_maximum
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_unique_maximum
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.maxent_at_equal_cost
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.maxent_at_equal_cost
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.maxent_under_cost_budget
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.maxent_under_cost_budget
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.carrierRaw_quadratic
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.carrierRaw_quadratic
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burdenLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burdenLaw
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burden_log_density
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burden_log_density
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burden_unique_maximum
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burden_unique_maximum
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burden_phase_weights
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burden_phase_weights
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burden_phase_normalized
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burden_phase_normalized
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.zero_penalty_uniform
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.zero_penalty_uniform
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.zero_horizon
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.zero_horizon
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.free_energy_minimum
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.free_energy_minimum
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_cost_antitone
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_cost_antitone
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_entropy_antitone
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_entropy_antitone
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_depth_multiplicity
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_depth_multiplicity
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.NonnegativeAmplitude
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.NonnegativeAmplitude
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.law_ext
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.law_ext
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.sqrtLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.sqrtLaw
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.squareLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.squareLaw
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.lawAmplitudeEquiv
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.lawAmplitudeEquiv
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_amplitude_unique
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.gibbs_amplitude_unique
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.evidenceWeight
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.evidenceWeight
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.conditionLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.conditionLaw
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.sqrt_condition_commutes
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.sqrt_condition_commutes
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.sqrt_condition_normalized
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.sqrt_condition_normalized
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.condition_one
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.condition_one
#check @OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burden_log_amplitude
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenGibbs.burden_log_amplitude
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.partition
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.partition
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.carrierRaw_ge_last
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.carrierRaw_ge_last
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_pos
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_le_geometric
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_le_geometric
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.geometric_ratio_lt_one
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.geometric_ratio_lt_one
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_summable
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_summable
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.partition_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.partition_pos
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_pos
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_hasSum
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_hasSum
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_infinite_support
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_infinite_support
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.tail
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.tail
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefix_add_tail
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefix_add_tail
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.tail_tendsto_zero
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.tail_tendsto_zero
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_polynomial_moment
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_polynomial_moment
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_polynomial_moment
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_polynomial_moment
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_burden_summable
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_burden_summable
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.log_probability
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.log_probability
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_entropy_summable
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_entropy_summable
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.nonpositive_penalty_not_summable
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.nonpositive_penalty_not_summable
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.zero_payload_not_summable
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.zero_payload_not_summable
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.partition_summable_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.partition_summable_iff
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.entropy
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.entropy
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.meanBurden
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.meanBurden
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.objective
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.objective
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.divergence_term
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.divergence_term
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.entropy_summable_of_burden
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.entropy_summable_of_burden
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.countable_gap_hasSum
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.countable_gap_hasSum
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.countable_divergence_eq_zero_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.countable_divergence_eq_zero_iff
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_objective
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_objective
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.countable_unique_maximum
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.countable_unique_maximum
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixPartition
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixPartition
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixPartition_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixPartition_pos
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_sum
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_sum
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_hasSum
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_hasSum
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_eq_finite
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_eq_finite
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixPartition_tendsto
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixPartition_tendsto
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_tendsto
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_tendsto
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixPartition_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixPartition_le
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_le_prefix
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_le_prefix
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_l1
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_l1
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_l1_tendsto_zero
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_l1_tendsto_zero

-- InstrumentComposition: adaptive composition and finite cutoff checks
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.jointChannel
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.jointChannel
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.exists_joint_output
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.exists_joint_output
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.recoverable_iff_support_separated
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.recoverable_iff_support_separated
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential_positive_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential_positive_iff
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.first_outcome_kept
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.first_outcome_kept
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.equal_joint_laws_persist
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.equal_joint_laws_persist
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential_recoverable
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential_recoverable
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.first_recoverable_of_sequential
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.first_recoverable_of_sequential
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential_recoverable_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential_recoverable_iff
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential_associative
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential_associative
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.deterministic
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.deterministic
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.adaptiveDeterministic
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.adaptiveDeterministic
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.deterministic_restoration_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.deterministic_restoration_iff
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.deterministic_composition_commutes
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.deterministic_composition_commutes

-- BurdenTail: adaptive composition and finite cutoff checks
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_succ
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_succ
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_succ
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_succ
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_strict_decrease
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_strict_decrease
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.log_probability_curvature
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.log_probability_curvature
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.carrierRaw_shift_lower
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.carrierRaw_shift_lower
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_shift_geometric
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.rawWeight_shift_geometric
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_shift_geometric
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.probability_shift_geometric
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.tail_le_geometric
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.tail_le_geometric
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_l1_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixProbability_l1_le

-- I4 and T3: retained-target support and countable amplitude transport
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential_conflict_persists
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.sequential_conflict_persists
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.side_decoder_before_of_after
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.side_decoder_before_of_after
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.side_budget_before_of_after
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.side_budget_before_of_after
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.recoverable_continuation_graph_eq
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.recoverable_continuation_graph_eq
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.recoverable_continuation_decoder_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.recoverable_continuation_decoder_iff
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.recoverable_continuation_chromatic_eq
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.recoverable_continuation_chromatic_eq
#check @OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.erasure_strictly_adds_conflict
#print axioms OperatorKO7.Meta.BoundaryObserver.InstrumentComposition.erasure_strictly_adds_conflict
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.SummableLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.SummableLaw
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.UnitAmplitude
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.UnitAmplitude
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.summableLaw_ext
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.summableLaw_ext
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitudeOfLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitudeOfLaw
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.lawOfAmplitude
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.lawOfAmplitude
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.summableLawAmplitudeEquiv
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.summableLawAmplitudeEquiv
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.bounded_likelihood_summable
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.bounded_likelihood_summable
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.conditionalLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.conditionalLaw
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitude_conditioning_commutes
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitude_conditioning_commutes
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitude_conditioning_normalized
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitude_conditioning_normalized
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.zero_likelihood_no_normalization
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.zero_likelihood_no_normalization
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.sqrt_difference_sq_le
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.sqrt_difference_sq_le
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitude_difference_summable
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitude_difference_summable
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitudeSqDistance
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitudeSqDistance
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitudeSqDistance_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitudeSqDistance_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitudeSqDistance_le_l1
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.amplitudeSqDistance_le_l1
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.burdenSummableLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.burdenSummableLaw
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixSummableLaw
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixSummableLaw
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixAmplitudeSqDistance_le_tail
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixAmplitudeSqDistance_le_tail
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixAmplitudeSqDistance_le_cutoff
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixAmplitudeSqDistance_le_cutoff
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixAmplitudeSqDistance_tendsto_zero
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.prefixAmplitudeSqDistance_tendsto_zero
#check @OperatorKO7.Meta.BoundaryObserver.BurdenTail.countable_amplitude_unique_maximum
#print axioms OperatorKO7.Meta.BoundaryObserver.BurdenTail.countable_amplitude_unique_maximum

-- Self-observation: AS1-AS3 and PS1.

-- AffineSelfObservation
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.observation_eq_iff_kernel_difference
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.observation_eq_iff_kernel_difference
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.solution_iff_kernel_translate
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.solution_iff_kernel_translate
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.target_forced_iff_kernel
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.target_forced_iff_kernel
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.kernelBoundary
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.kernelBoundary
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.kernel_witness_excludes_readout
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.kernel_witness_excludes_readout
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.annihilator_refutes
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.annihilator_refutes
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.no_solution_iff_annihilator
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.no_solution_iff_annihilator
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.Satisfies
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.Satisfies
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.row_certificate_sound
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.row_certificate_sound
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.target_forced_iff_row_certificate
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.target_forced_iff_row_certificate
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.no_row_certificate_iff_kernel_witness
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.no_row_certificate_iff_kernel_witness
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.forced_or_kernel_witness
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.forced_or_kernel_witness
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.inconsistent_row_certificate
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.inconsistent_row_certificate
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.no_solution_iff_row_refutation
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.no_solution_iff_row_refutation
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.source_certificate_trichotomy
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.source_certificate_trichotomy
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.ambiguity_certificate_sound
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.ambiguity_certificate_sound
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.equivalent_equation_readout
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.equivalent_equation_readout
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.boolEquations
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.boolEquations
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.localUpdate
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.localUpdate
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.localUpdate_bottom
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.localUpdate_bottom
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.copy_solutions
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.copy_solutions
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.negation_no_solution
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.negation_no_solution
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.cancellation_unique_solution
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.cancellation_unique_solution
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.localDiagnosticBoundary
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.localDiagnosticBoundary
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.no_bottom_only_consistency_detector
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.no_bottom_only_consistency_detector
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.Bit
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.Bit
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.bit
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.bit
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.affineRows
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.affineRows
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.affineRhs
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.affineRhs
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.bool_equations_linear_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.bool_equations_linear_iff
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.cancellation_row_certificates
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.cancellation_row_certificates
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.negation_row_refutation
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.negation_row_refutation
#check @OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.copy_kernel_vector
#print axioms OperatorKO7.Meta.BoundaryObserver.AffineSelfObservation.copy_kernel_vector

-- PartialSelfEvaluation
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.negate
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.negate
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.negate_none
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.negate_none
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.negate_some
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.negate_some
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.negate_involutive
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.negate_involutive
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.negate_fixed_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.negate_fixed_iff
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.self_evaluation_forces_none
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.self_evaluation_forces_none
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.witnessEval
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.witnessEval
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.witnessEval_false
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.witnessEval_false
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.witnessEval_true
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.witnessEval_true
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.witness_negation
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.witness_negation
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.witness_self_evaluation
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.witness_self_evaluation
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.nonconstant_completion
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.nonconstant_completion
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.no_readout_from_fixed_point
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.no_readout_from_fixed_point
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.no_total_boolean_readout
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.no_total_boolean_readout
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.definite_readout
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.definite_readout
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.cycle
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.cycle
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.cycle_has_no_fixed_point
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.cycle_has_no_fixed_point
#check @OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.cycle_closed_language_has_no_self_evaluator
#print axioms OperatorKO7.Meta.BoundaryObserver.PartialSelfEvaluation.cycle_closed_language_has_no_self_evaluator
