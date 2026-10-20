import OperatorKO7.Meta.MutualDuplication_SchemaBarrier

namespace MutualDuplicationSchemaReach

open OperatorKO7
open OperatorKO7.MutualDuplicationCase

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.Schema.no_additive_orients_cycle
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.Schema.no_affine_orients_cycle_of_unbounded
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.System.no_global_orients_ctx_additive
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.System.no_global_orients_ctx_affine_of_unbounded
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationGeneral.AlternatingDupSchema.no_additive_orients_via_mutualSchema
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationGeneral.AlternatingDupSchema.no_affine_orients_of_unbounded_via_mutualSchema
  trivial

example : True := by
  have :=
    @OperatorKO7.MutualDuplicationGeneral.AlternatingDupSchema.AlternatingDupSystem.cycle_realized_via_mutualSchema
  trivial

example :
    ∃ u,
      OperatorKO7.MutualDuplicationSchema.System.StepCtx mutualWitnessSystem
        (OperatorKO7.MutualDuplicationSchema.Schema.cycleSource
          mutualWitnessSystem.toSchema AltTerm.base AltTerm.base AltTerm.base) u ∧
      OperatorKO7.MutualDuplicationSchema.System.StepCtx mutualWitnessSystem u
        (OperatorKO7.MutualDuplicationSchema.Schema.cycleTarget
          mutualWitnessSystem.toSchema AltTerm.base AltTerm.base AltTerm.base) := by
  exact
    OperatorKO7.MutualDuplicationCase.mutualWitnessSystem_nonvacuous
      AltTerm.base AltTerm.base AltTerm.base

end MutualDuplicationSchemaReach
