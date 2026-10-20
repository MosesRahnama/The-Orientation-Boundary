import OperatorKO7.Meta.MutualDuplication_FiniteSchema_Instances

namespace MutualDuplicationFiniteSchemaBuilderReach

open OperatorKO7

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.advance
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.Builder
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.Builder.toKCycleSystem
  trivial

#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.Builder.cycle_realized_at

#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.Builder.no_global_orients_ctx_additive

#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.Builder.no_global_orients_ctx_affine_of_unbounded_at

example (D : OperatorKO7.MutualDuplicationFiniteSchema.Constructors.ThreeRuleData)
    (i : Fin 3) (b s n : D.T) :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.Builder.StepCtx D.toFiniteCycleBuilder)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource
        D.toFiniteCycleBuilder.toKCycleSystem.toKCycleSchema i b s n)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget
        D.toFiniteCycleBuilder.toKCycleSystem.toKCycleSchema i b s n) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.Builder.cycle_realized_at
      D.toFiniteCycleBuilder i b s n

example :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.Builder.StepCtx
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessData.toFiniteCycleBuilder)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessData.toFiniteCycleBuilder.toKCycleSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessData.toFiniteCycleBuilder.toKCycleSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.Builder.cycle_realized_at
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessData.toFiniteCycleBuilder
      0
      OperatorKO7.MutualDuplicationCase.AltTerm.base
      OperatorKO7.MutualDuplicationCase.AltTerm.base
      OperatorKO7.MutualDuplicationCase.AltTerm.base

end MutualDuplicationFiniteSchemaBuilderReach
