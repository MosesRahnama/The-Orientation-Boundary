import OperatorKO7.Meta.BoundaryObserver.Instances.KernelCases
import OperatorKO7.Meta.BoundaryObserver.Instances.Recursor
import OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest
import OperatorKO7.Meta.BoundaryObserver.BoundarySingularityQuantum
import OperatorKO7.Meta.BoundaryObserver.BoundaryTheoremQuantum

set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

/-!
# Boundary Theorem instance and quantum reach
V1 L3, L6 and L7. Extracted original declarations retain their original
fully qualified names and types while their source modules remain separate.
Each check is paired with its axiom query. This is the full instance reach;
BoundaryTheoremMathReach is the separate mathematics-only gate.
-/

#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqRefl_fires_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqRefl_fires_iff
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqDiff_fires
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqDiff_fires
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_root_reducts
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_root_reducts
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes_pos
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes_pos
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes_eq_one_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.nodes_eq_one_iff
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.frame_pair_to_frame
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.frame_pair_to_frame
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.empty_frame_normal
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.empty_frame_normal
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.empty_frame_ne_blank
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.empty_frame_ne_blank
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.double_frame_normal
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.double_frame_normal
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_step_closed
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_step_closed
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_reducts
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_reducts
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_normal_forms
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.eqW_void_void_ctx_normal_forms
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.guarded_diff_only_distinct
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.guarded_diff_only_distinct
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.guarded_diff_fires_on_distinct
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.guarded_diff_fires_on_distinct
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.numeral
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.numeral
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.spine
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.spine
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.descend
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.descend
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.frameCopy
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.frameCopy
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.spine_ctx_step
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.spine_ctx_step
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.spine_app
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.spine_app
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.unroll_steps
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.unroll_steps
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.descend_spine_add
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.descend_spine_add
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.descend_spine
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.descend_spine
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.frameCopy_spine
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.frameCopy_spine
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.O
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.O
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.O_zero
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.O_zero
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.O_succ
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.O_succ
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.O_unroll
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.O_unroll
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.counter_test_not_determined
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.counter_test_not_determined
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.counter_merged_pair
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.counter_merged_pair
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.observed_test_separates_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.observed_test_separates_iff
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.observed_test_adjacent_iff
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.observed_test_adjacent_iff
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.step_copies_merged_pair
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.step_copies_merged_pair
#check @OperatorKO7.Meta.BoundaryObserver.KernelCases.self_step_infinite_seq
#print axioms OperatorKO7.Meta.BoundaryObserver.KernelCases.self_step_infinite_seq
#check @OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.pass_realized
#print axioms OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.pass_realized
#check @OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.rec_succ_root_reduct
#print axioms OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.rec_succ_root_reduct
#check @OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.ne_app_rec
#print axioms OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.ne_app_rec
#check @OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.returns_iff_observed
#print axioms OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.returns_iff_observed
#check @OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.returnsDecidable
#print axioms OperatorKO7.Meta.BoundaryObserver.RecursorDecidability.returnsDecidable
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.counterSideSymbol_trace
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.counterSideSymbol_trace
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.EqualityOccurrence
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.EqualityOccurrence
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equalityContent
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equalityContent
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equalityPlace
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equalityPlace
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.firstOccurrence
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.firstOccurrence
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.secondOccurrence
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.secondOccurrence
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_places_distinct
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_places_distinct
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_occurrences_distinct
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_occurrences_distinct
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_occurrences_same_content
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_occurrences_same_content
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_occurrences_merged
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_occurrences_merged
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.eqW_root_refl_iff_content_eq
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.eqW_root_refl_iff_content_eq
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.eqW_root_diff_unconditional
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.eqW_root_diff_unconditional
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.sameArgumentPlace
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.sameArgumentPlace
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_place_reading_separates
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_place_reading_separates
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_root_both_rules
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_root_both_rules
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.eqW_root_diff_all_places
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.eqW_root_diff_all_places
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.eqW_root_diff_equal_place
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.eqW_root_diff_equal_place
#check @OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_occurrence_rule_bundle
#print axioms OperatorKO7.Meta.BoundaryObserver.Instances.EqualityTest.equality_occurrence_rule_bundle
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.isMergedPair_void_occurrences
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.isMergedPair_void_occurrences
#check @OperatorKO7.Meta.BoundaryObserver.MergedPair.unit_occurrences
#print axioms OperatorKO7.Meta.BoundaryObserver.MergedPair.unit_occurrences
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.embedAt
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.embedAt
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.embedAt_ne_zero
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.embedAt_ne_zero
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.marginalLeft_quadratic
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.marginalLeft_quadratic
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.marginalLeft_posDef
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.marginalLeft_posDef
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.entropy_pos_of_posDef
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.entropy_pos_of_posDef
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.spectralLift_posDef
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.spectralLift_posDef
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.tensor_posDef
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.tensor_posDef
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.thermalJoint_posDef
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.thermalJoint_posDef
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.no_exact_thermal_erasure
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.no_exact_thermal_erasure
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.fairPair
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.fairPair
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.fairPair_posDef
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.fairPair_posDef
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.fairPair_trace
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.fairPair_trace
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.fairPair_entropy
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.fairPair_entropy
#check @OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.fair_pair_not_erased
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundarySingularity.Thermal.fair_pair_not_erased
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.MergeFloorGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.MergeFloorGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.mergeFloor
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.mergeFloor
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.DemonResetGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.DemonResetGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.demonResetGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.demonResetGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.transcriptRegister
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.transcriptRegister
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.CycleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.CycleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.cycleGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.cycleGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.ApexPairGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.ApexPairGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.apexPairGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.apexPairGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.BoundaryTheoremGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.BoundaryTheoremGoal
#check @OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.boundaryTheoremGoal
#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryTheorem.boundaryTheoremGoal

/-! M2 exact relocated Trace-specific recursor adapter, original public namespace -/
#check @UniversalObservation.Transport.RecursorAdapter.contentProblem
#print axioms UniversalObservation.Transport.RecursorAdapter.contentProblem
#check @UniversalObservation.Transport.RecursorAdapter.content_zero_test_obstruction
#print axioms UniversalObservation.Transport.RecursorAdapter.content_zero_test_obstruction
#check @UniversalObservation.Transport.RecursorAdapter.counter_zero_test_witness
#print axioms UniversalObservation.Transport.RecursorAdapter.counter_zero_test_witness
#check @UniversalObservation.Transport.RecursorAdapter.termination_and_content_blindness
#print axioms UniversalObservation.Transport.RecursorAdapter.termination_and_content_blindness
#check @UniversalObservation.Transport.RecursorAdapter.contentOrientationProblem
#print axioms UniversalObservation.Transport.RecursorAdapter.contentOrientationProblem
#check @UniversalObservation.Transport.RecursorAdapter.content_orientation_obstruction
#print axioms UniversalObservation.Transport.RecursorAdapter.content_orientation_obstruction
#check @UniversalObservation.Transport.RecursorAdapter.native_one_step_return
#print axioms UniversalObservation.Transport.RecursorAdapter.native_one_step_return
#check @UniversalObservation.Transport.RecursorAdapter.depth_alphabet_minimum
#print axioms UniversalObservation.Transport.RecursorAdapter.depth_alphabet_minimum
