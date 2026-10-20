import OperatorKO7.Meta.MutualDuplication_SchemaProjection

namespace MutualDuplicationSchemaProjectionReach

open OperatorKO7

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.no_global_orients_ctx_transparent_compositional
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.System.no_global_orients_ctx_transparent_compositional
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.System.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.Schema.CompositionalMeasure.toPrimaryMeasure
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.Schema.projectionSchema
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.projectionSchemaAtZero
  trivial

end MutualDuplicationSchemaProjectionReach
