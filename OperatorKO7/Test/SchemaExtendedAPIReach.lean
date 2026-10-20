import OperatorKO7.SchemaExtendedAPI

namespace SchemaExtendedAPIReach

open OperatorKO7

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_tropical_primary_orients_dup_step_of_unbounded
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_matrix_orients_dup_step_of_fixed_row_pump
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_matrixArbitrary_orients_dup_step_of_scalar_dominance_pump
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_arcticMatrix_orients_dup_step_of_scalar_dominance_pump
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_additive
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.System.no_global_orients_ctx_affine_of_unbounded
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.no_global_orients_ctx_additive
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.no_global_orients_ctx_transparent_compositional
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationPayloadFlow.no_global_orients_ctx_additive
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.additive_witness
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.nat_direct_escape_trichotomy
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchemaAPI.final_catalog
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchemaAPI.certified_successor_edge_boundary
  trivial

example : True := by
  have := OperatorKO7.MutualDuplicationFiniteSchemaAPI.two_rule_witness
  trivial

example : True := by
  have := @OperatorKO7.HigherOrderSharingBoundaryAPI.final_catalog
  trivial

example : True := by
  have := OperatorKO7.HigherOrderSharingBoundaryAPI.unqualified_lift_blocker
  trivial

example : True := by
  have := OperatorKO7.HigherOrderSharingBoundaryAPI.full_higher_order_outside_catalog
  trivial

end SchemaExtendedAPIReach
