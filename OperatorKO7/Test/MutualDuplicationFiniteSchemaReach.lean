import OperatorKO7.Meta.MutualDuplication_FiniteSchema
import OperatorKO7.Meta.MutualDuplication_FiniteSchema_Instances

namespace MutualDuplicationFiniteSchemaReach

open OperatorKO7

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.no_additive_orients_cycle
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.no_affine_orients_cycle_of_unbounded
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.toCycleWitness
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.no_global_orients_ctx_additive
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.no_global_orients_ctx_affine_of_unbounded
  trivial

#check OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.KCycleAffineAt

#check OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.no_global_orients_ctx_affine_of_unbounded_at

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.System.toKCycleSystem_two
  trivial

#check OperatorKO7.MutualDuplicationSchema.Schema.cycleSource_two_eq_schema

#check OperatorKO7.MutualDuplicationSchema.Schema.cycleTarget_two_eq_schema

#check OperatorKO7.MutualDuplicationSchema.System.cycle_realized_via_finiteSchema

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.toKNodeWitness
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.cycle_realized_via_kNode
  trivial

example :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.StepCtx
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSystem)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.two_rule_nonvacuous
      OperatorKO7.MutualDuplicationCase.AltTerm.base
      OperatorKO7.MutualDuplicationCase.AltTerm.base
      OperatorKO7.MutualDuplicationCase.AltTerm.base

example :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.StepCtx
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessSystem)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.three_rule_nonvacuous
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base

end MutualDuplicationFiniteSchemaReach
