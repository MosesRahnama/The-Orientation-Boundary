import OperatorKO7.Meta.MutualDuplication_FiniteSchema_API

namespace MutualDuplicationFiniteSchemaAPIReach

open OperatorKO7

#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.GraphSearchCertificate
#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.FinalCatalog
#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.CloseoutCatalog
#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.final_catalog
#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.closeout_catalog
#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.cycle_realization
#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.additive_barrier
#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.affine_barrier
#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.certified_successor_edge_boundary
#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.two_rule_witness
#check OperatorKO7.MutualDuplicationFiniteSchemaAPI.three_rule_witness

example :
    OperatorKO7.MutualDuplicationFiniteSchemaAPI.FinalCatalog
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate :=
  OperatorKO7.MutualDuplicationFiniteSchemaAPI.two_rule_witness

example : OperatorKO7.MutualDuplicationFiniteSchemaAPI.CloseoutCatalog :=
  OperatorKO7.MutualDuplicationFiniteSchemaAPI.closeout_catalog
    OperatorKO7.MutualDuplicationFiniteSchemaAPI.two_rule_encoded_search_space

example (i : Fin 2) (b s n : OperatorKO7.MutualDuplicationCase.AltTerm) :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        i b s n)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        i b s n) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchemaAPI.cycle_realization
      OperatorKO7.MutualDuplicationFiniteSchemaAPI.two_rule_witness i b s n

example
    (M : OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.AdditiveMeasure
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema) :
    ¬ OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate M.eval (· < ·) := by
  exact OperatorKO7.MutualDuplicationFiniteSchemaAPI.additive_barrier
    OperatorKO7.MutualDuplicationFiniteSchemaAPI.two_rule_witness M

example
    (M : OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.AffineMeasure
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema)
    (hunbounded : OperatorKO7.StepDuplicating.StepDuplicatingSchema.HasUnboundedRange
      (OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.KCycleAffineAtZero
        (C := OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate) M)) :
    ¬ OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate M.eval (· < ·) := by
  exact OperatorKO7.MutualDuplicationFiniteSchemaAPI.affine_barrier
    OperatorKO7.MutualDuplicationFiniteSchemaAPI.three_rule_witness M hunbounded

end MutualDuplicationFiniteSchemaAPIReach
