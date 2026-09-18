import OperatorKO7.Meta.MutualDuplication_FiniteSchema_BuilderMapping

namespace MutualDuplicationFiniteSchemaBuilderMappingReach

open OperatorKO7

#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.toBuilder
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.StepCtx
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.GlobalOrientsCtx
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.KCycleAffineAt
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.KCycleAffineAtZero
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.cycle_realized_at
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.no_global_orients_ctx_additive
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.no_global_orients_ctx_affine_of_unbounded_at
#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.no_global_orients_ctx_affine_of_unbounded

#check OperatorKO7.MutualDuplicationFiniteSchema.Constructors.TwoRuleData.toSearchCertificate
#check OperatorKO7.MutualDuplicationFiniteSchema.Constructors.TwoRuleData.toSearchCertificate_toBuilder_eq
#check OperatorKO7.MutualDuplicationFiniteSchema.Constructors.ThreeRuleData.toSearchCertificate
#check OperatorKO7.MutualDuplicationFiniteSchema.Constructors.ThreeRuleData.toSearchCertificate_toBuilder_eq

#check OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSearchCertificate
#check OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessSearchCertificate
#check OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSearchCertificate_toBuilder_eq
#check OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessSearchCertificate_toBuilder_eq

example :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.StepCtx
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSearchCertificate)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base
        OperatorKO7.MutualDuplicationCase.AltTerm.base) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate.cycle_realized_at
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessSearchCertificate
      0
      OperatorKO7.MutualDuplicationCase.AltTerm.base
      OperatorKO7.MutualDuplicationCase.AltTerm.base
      OperatorKO7.MutualDuplicationCase.AltTerm.base

end MutualDuplicationFiniteSchemaBuilderMappingReach
