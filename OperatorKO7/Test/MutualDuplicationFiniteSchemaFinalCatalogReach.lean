import OperatorKO7.Meta.MutualDuplication_FiniteSchema_FinalCatalog

namespace MutualDuplicationFiniteSchemaFinalCatalogReach

open OperatorKO7

#check OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleMutualDuplicationFinalCatalog
#check OperatorKO7.MutualDuplicationFiniteSchema.finite_cycle_mutual_duplication_final_catalog
#check OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_search_certificate
#check OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_builder
#check OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_cycle_realization
#check OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_additive_barrier
#check OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_affine_barrier_at
#check OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_affine_barrier_zero
#check OperatorKO7.MutualDuplicationFiniteSchema.graph_search_requires_certified_successor_edges
#check OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_two_rule_nonvacuous
#check OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_three_rule_nonvacuous

example :
    Nonempty (OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilderMapping.SearchCertificate 1) :=
  OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_search_certificate
    (OperatorKO7.MutualDuplicationFiniteSchema.finite_cycle_mutual_duplication_final_catalog
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate)

example :
    Nonempty (OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleBuilder.Builder 2) :=
  OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_builder
    (OperatorKO7.MutualDuplicationFiniteSchema.finite_cycle_mutual_duplication_final_catalog
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate)

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
    OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_cycle_realization
      (OperatorKO7.MutualDuplicationFiniteSchema.finite_cycle_mutual_duplication_final_catalog
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate)
      i b s n

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
    OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_two_rule_nonvacuous
      OperatorKO7.MutualDuplicationCase.AltTerm.base
      OperatorKO7.MutualDuplicationCase.AltTerm.base
      OperatorKO7.MutualDuplicationCase.AltTerm.base

example :
    Relation.TransGen
      (OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.StepCtx
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleSource
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base)
      (OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.cycleTarget
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema
        0
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_three_rule_nonvacuous
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.ThreeRuleWitness.Term.base

example
    (M : OperatorKO7.MutualDuplicationFiniteSchema.KCycleSchema.AdditiveMeasure
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate.toBuilder.toKCycleSystem.toKCycleSchema) :
    ¬ OperatorKO7.MutualDuplicationFiniteSchema.FiniteCycleGraphSearch.GraphSearchCertificate.GlobalOrientsCtx
      OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate M.eval (· < ·) := by
  exact
    OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_additive_barrier
      (OperatorKO7.MutualDuplicationFiniteSchema.finite_cycle_mutual_duplication_final_catalog
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.twoRuleWitnessGraphSearchCertificate)
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
    OperatorKO7.MutualDuplicationFiniteSchema.final_catalog_projects_affine_barrier_zero
      (OperatorKO7.MutualDuplicationFiniteSchema.finite_cycle_mutual_duplication_final_catalog
        OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.threeRuleWitnessGraphSearchCertificate)
      M hunbounded

end MutualDuplicationFiniteSchemaFinalCatalogReach
