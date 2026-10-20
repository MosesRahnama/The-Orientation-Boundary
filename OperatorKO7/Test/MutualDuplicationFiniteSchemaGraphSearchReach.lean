import OperatorKO7.Meta.MutualDuplication_FiniteSchema_GraphSearch

namespace MutualDuplicationFiniteSchemaGraphSearchReach

open OperatorKO7

#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.toSearchCertificate
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.toBuilder
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.local_step_succ_derived
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.cycle_realized_at
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.no_global_orients_ctx_additive
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.no_global_orients_ctx_affine_of_unbounded_at
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.no_global_orients_ctx_affine_of_unbounded

#check OperatorKO7.MutualDuplicationFiniteSchema.Constructors.TwoRuleData.toGraphSearchCertificate
#check OperatorKO7.MutualDuplicationFiniteSchema.Constructors.ThreeRuleData.toGraphSearchCertificate

#check OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate
#check OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate

example :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.cycle_realized_at
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate
      0
      OperatorKO7.MutualDuplicationCase.AltTerm.base
      OperatorKO7.MutualDuplicationCase.AltTerm.base
      OperatorKO7.MutualDuplicationCase.AltTerm.base

example :
    OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate.toSearchCertificate.toBuilder =
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate.toBuilder := by
  simpa using
    OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.toSearchCertificate_toBuilder_eq
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate

example
    (M : OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.AdditiveMeasure
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema) :
    ¬ OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate M.eval (· < ·) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.no_global_orients_ctx_additive
      M

example
    (M : OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.AffineMeasure
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema)
    (hunbounded : OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
      (OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.KCycleAffineAtZero
        (C := OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate) M)) :
    ¬ OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate M.eval (· < ·) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.no_global_orients_ctx_affine_of_unbounded
      M hunbounded

end MutualDuplicationFiniteSchemaGraphSearchReach
