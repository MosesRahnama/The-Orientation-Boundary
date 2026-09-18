import OperatorKO7.Meta.MutualDuplication_FiniteSchema_Instances

namespace MutualDuplicationFiniteSchemaInstancesReach

open OperatorKO7

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.Constructors.TwoRuleData
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.Constructors.TwoRuleData.toMutualSystem
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.Constructors.TwoRuleData.toKCycleSystem
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.Constructors.ThreeRuleData
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.Constructors.ThreeRuleData.toKCycleSystem
  trivial

example (D : OperatorKO7.MutualDuplicationFiniteSchema.Constructors.TwoRuleData)
    (i : Fin 2) (b s n : D.T) :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.StepCtx D.toKCycleSystem)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource D.toKCycleSystem.toKCycleSchema i b s n)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget D.toKCycleSystem.toKCycleSchema i b s n) := by
  exact OperatorKO7.MutualDuplicationFiniteSchema.Constructors.TwoRuleData.cycle_realized_at D i b s n

example (D : OperatorKO7.MutualDuplicationFiniteSchema.Constructors.ThreeRuleData)
    (i : Fin 3) (b s n : D.T) :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.StepCtx D.toKCycleSystem)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource D.toKCycleSystem.toKCycleSchema i b s n)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget D.toKCycleSystem.toKCycleSchema i b s n) := by
  exact OperatorKO7.MutualDuplicationFiniteSchema.Constructors.ThreeRuleData.cycle_realized_at D i b s n

example :
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessData.toKCycleSystem =
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSystem := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessData_toKCycleSystem_eq

example :
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessData.toKCycleSystem =
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessSystem := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessData_toKCycleSystem_eq

example
    (M : OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.AdditiveMeasure
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSystem.toKCycleSchema) :
    ¬ OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.GlobalOrientsCtx
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSystem M.eval (· < ·) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSystem_no_global_orients_ctx_additive M

example
    (M : OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.AffineMeasure
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessSystem.toKCycleSchema)
    (i : Fin 3)
    (hunbounded : OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.KCycleAffineAt i M)) :
    ¬ OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.GlobalOrientsCtx
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessSystem M.eval (· < ·) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessSystem_no_global_orients_ctx_affine_of_unbounded_at
      M i hunbounded

end MutualDuplicationFiniteSchemaInstancesReach
