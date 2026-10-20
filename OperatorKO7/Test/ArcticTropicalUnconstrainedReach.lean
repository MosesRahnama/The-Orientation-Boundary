import OperatorKO7.Meta.MatrixBarrierArcticNatural
import OperatorKO7.Meta.MatrixBarrierTropicalNatural_Schema
import OperatorKO7.Meta.NonlinearUnconstrainedExactLaw

/-!
Reach gate for lanes P3 (arctic system, KO7, and context layers plus the pump-free strict
barrier), P4 (the certificate-free tropical barrier, killed by a compiled orienter), and P11 (the
exact law behind the unconstrained nonlinear direct row).

Every public declaration carries a paired `#check @` and `#print axioms`.
-/

open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.MatrixBarrierArcticNatural
open OperatorKO7.NonlinearMethodLawCarrier

/-! ## P3: the pump-free arctic barrier -/

#check @ArcticWrapDiagFinite
#print axioms ArcticWrapDiagFinite
#check @arcticWrapDiagPositive_finite
#print axioms arcticWrapDiagPositive_finite
#check @arcticLt_fin
#print axioms arcticLt_fin
#check @arctic_coord_le_counter_of_strict
#print axioms arctic_coord_le_counter_of_strict
#check @arctic_recur_chain_ge_of_strict
#print axioms arctic_recur_chain_ge_of_strict
#check @no_arcticMatrix_orients_dup_step_of_tracked_strict_pumpFree
#print axioms no_arcticMatrix_orients_dup_step_of_tracked_strict_pumpFree
#check @arcticWrapDiagFinite_or_bot
#print axioms arcticWrapDiagFinite_or_bot

/-! ## P3: system layer -/

#check @no_global_orients_arcticMatrix_of_tracked_nonincreasing
#print axioms no_global_orients_arcticMatrix_of_tracked_nonincreasing
#check @no_global_orients_arcticMatrix_of_tracked_strict
#print axioms no_global_orients_arcticMatrix_of_tracked_strict
#check @no_global_orients_arcticMatrix_of_tracked_strict_pumpFree
#print axioms no_global_orients_arcticMatrix_of_tracked_strict_pumpFree

/-! ## P3: the `bot` escape -/

#check @botRightWeight
#print axioms botRightWeight
#check @arcticBotRightMeasure
#print axioms arcticBotRightMeasure
#check @arcticBotRightMeasure_not_wrapDiagFinite
#print axioms arcticBotRightMeasure_not_wrapDiagFinite
#check @arcticBotRightMeasure_strictly_orients
#print axioms arcticBotRightMeasure_strictly_orients
#check @arcticBotRightMeasure_coord_finite
#print axioms arcticBotRightMeasure_coord_finite

/-! ## P3: KO7 and context layers -/

#check @no_global_step_orientation_arcticMatrix_of_tracked_nonincreasing
#print axioms no_global_step_orientation_arcticMatrix_of_tracked_nonincreasing
#check @no_global_step_orientation_arcticMatrix_of_tracked_strict
#print axioms no_global_step_orientation_arcticMatrix_of_tracked_strict
#check @no_global_step_orientation_arcticMatrix_of_tracked_strict_pumpFree
#print axioms no_global_step_orientation_arcticMatrix_of_tracked_strict_pumpFree
#check @no_ctx_orientation_arcticMatrix_of_tracked_nonincreasing
#print axioms no_ctx_orientation_arcticMatrix_of_tracked_nonincreasing
#check @no_ctx_orientation_arcticMatrix_of_tracked_strict
#print axioms no_ctx_orientation_arcticMatrix_of_tracked_strict
#check @no_ctx_orientation_arcticMatrix_of_tracked_strict_pumpFree
#print axioms no_ctx_orientation_arcticMatrix_of_tracked_strict_pumpFree
#check @traceArcticWeight
#print axioms traceArcticWeight
#check @sizeArcticMeasure
#print axioms sizeArcticMeasure
#check @sizeArcticMeasure_wrapDiagPositive
#print axioms sizeArcticMeasure_wrapDiagPositive
#check @sizeArcticMeasure_no_ctx_orientation
#print axioms sizeArcticMeasure_no_ctx_orientation

/-! ## P4: the tropical semiring and the kill -/

#check @TropicalNat
#print axioms TropicalNat
#check @tropicalMin
#print axioms tropicalMin
#check @tropicalPlus
#print axioms tropicalPlus
#check @TropicalLe
#print axioms TropicalLe
#check @TropicalLt
#print axioms TropicalLt
#check @tropicalLe_refl
#print axioms tropicalLe_refl
#check @tropicalMin_le_left
#print axioms tropicalMin_le_left
#check @tropicalMin_le_right
#print axioms tropicalMin_le_right
#check @tropicalVecMin
#print axioms tropicalVecMin
#check @TropicalMatrix
#print axioms TropicalMatrix
#check @tropicalLe_foldr_of_mem
#print axioms tropicalLe_foldr_of_mem
#check @TropicalMatrix.act
#print axioms TropicalMatrix.act
#check @TropicalMatrix.act_le_diag
#print axioms TropicalMatrix.act_le_diag
#check @TropicalNatMatrixMeasure
#print axioms TropicalNatMatrixMeasure
#check @TropicalWrapDiagPositive
#print axioms TropicalWrapDiagPositive
#check @tropicalEscapeWeight
#print axioms tropicalEscapeWeight
#check @tropicalEscapeWeight_recur
#print axioms tropicalEscapeWeight_recur
#check @tropicalEscapeMeasure
#print axioms tropicalEscapeMeasure
#check @tropicalEscapeMeasure_wrapDiagPositive
#print axioms tropicalEscapeMeasure_wrapDiagPositive
#check @tropicalEscapeMeasure_coord_finite
#print axioms tropicalEscapeMeasure_coord_finite
#check @tropicalEscapeMeasure_strictly_orients
#print axioms tropicalEscapeMeasure_strictly_orients
#check @certificate_free_tropical_barrier_false
#print axioms certificate_free_tropical_barrier_false
#check @tropicalEscapeMeasure_no_scalar_dominance
#print axioms tropicalEscapeMeasure_no_scalar_dominance
#check @TropicalWrapStrictAt
#print axioms TropicalWrapStrictAt
#check @tropicalEscapeMeasure_not_wrapStrict_left
#print axioms tropicalEscapeMeasure_not_wrapStrict_left
#check @tropicalEscapeMeasure_not_wrapStrict_right
#print axioms tropicalEscapeMeasure_not_wrapStrict_right
#check @tropical_root_escape_not_context_compatible
#print axioms tropical_root_escape_not_context_compatible
#check @FreeDupStepCtx
#print axioms FreeDupStepCtx
#check @tropicalEscapeMeasure_contextual_equality
#print axioms tropicalEscapeMeasure_contextual_equality
#check @tropicalEscapeMeasure_not_context_orienter
#print axioms tropicalEscapeMeasure_not_context_orienter

/-! ## P11: the exact law -/

#check @UnconstrainedDirectLaw
#print axioms UnconstrainedDirectLaw
#check @seedWrapIter
#print axioms seedWrapIter
#check @eval_seedWrapIter_ge_index
#print axioms eval_seedWrapIter_ge_index
#check @no_unconstrainedDirect_orients_dup_step
#print axioms no_unconstrainedDirect_orients_dup_step
#check @no_unconstrainedDirect_orients_dup_step_of_tracked
#print axioms no_unconstrainedDirect_orients_dup_step_of_tracked
#check @no_global_orients_unconstrainedDirect
#print axioms no_global_orients_unconstrainedDirect
#check @additive_eval_succIter_ge
#print axioms additive_eval_succIter_ge
#check @AdditiveMeasure.toUnconstrainedDirectLaw
#print axioms AdditiveMeasure.toUnconstrainedDirectLaw
#check @unconstrainedDirectLaw_wrap_clause_necessary
#print axioms unconstrainedDirectLaw_wrap_clause_necessary
#check @unconstrainedDirectLaw_wrap_clause_fails
#print axioms unconstrainedDirectLaw_wrap_clause_fails
#check @unconstrainedDirectLaw_wrap_clause_escape
#print axioms unconstrainedDirectLaw_wrap_clause_escape
#check @unconstrainedDirectLaw_counter_clause_escape
#print axioms unconstrainedDirectLaw_counter_clause_escape
#check @crossCoupledWeight_keeps_wrapper_arguments
#print axioms crossCoupledWeight_keeps_wrapper_arguments
#check @crossCoupledWeight_succIter
#print axioms crossCoupledWeight_succIter
#check @crossCoupledWeight_has_no_counter_gain
#print axioms crossCoupledWeight_has_no_counter_gain
#check @tropicalEscapeWeight_le_five
#print axioms tropicalEscapeWeight_le_five
#check @arbitrary_relation_law_boundary_vacuous_off_step
#print axioms arbitrary_relation_law_boundary_vacuous_off_step
#check @arbitrary_relation_law_boundary_off_step_is_emptiness
#print axioms arbitrary_relation_law_boundary_off_step_is_emptiness
