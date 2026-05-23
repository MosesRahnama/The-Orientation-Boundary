import OperatorKO7.SchemaAPI

/-!
Sanity check: every newly re-exported schema-level module is reachable
through a single `import OperatorKO7.SchemaAPI`. This file exists only
to fail at elaboration time if any of the imports gets dropped from
the public API.
-/

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.RecordEmissionWitness

section SchemaAPIReach

-- Core
example : ∀ {S : StepDuplicatingSchema} (M : AdditiveMeasure S),
    ¬ (∀ b s n, M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))) :=
  @no_additive_orients_dup_step

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeProjectionRank_unique
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.primitiveTraceImageProjectionRank_unique
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.confession_routes_factor_through_primitiveTraceImage
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.all_route_local_evidence_yields_certified_forgetting_witnesses
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.confessionRouteConvergencePackage
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.confessionRouteConvergencePackage_projects_common_forgetting_witness
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.UsableRulesConfessionRouteResidualObligation
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.HasUsableRulesConfessionRoute
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.usableRulesRouteResidual_projects_common_route
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.usableRulesResidual_projects_core_agreement
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.usableRulesResidual_projects_route_agreement
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.usableRulesResidual_projects_forgetting_rank
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.UsableRulesConvergenceExtension
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.usableRulesResidual_to_convergence_extension
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.hasUsableRulesConfessionRoute_iff_nonempty_convergence_extension
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.no_usableRules_convergence_extension_without_residual
  trivial

example (h : OperatorKO7.ConfessionMethodFamily.HasUsableRulesConfessionRoute) :
    Nonempty OperatorKO7.ConfessionMethodFamily.UsableRulesConvergenceExtension := by
  exact
    (OperatorKO7.ConfessionMethodFamily.hasUsableRulesConfessionRoute_iff_nonempty_convergence_extension).1 h

example (h :
    Nonempty OperatorKO7.ConfessionMethodFamily.UsableRulesConvergenceExtension) :
    OperatorKO7.ConfessionMethodFamily.HasUsableRulesConfessionRoute := by
  exact
    (OperatorKO7.ConfessionMethodFamily.hasUsableRulesConfessionRoute_iff_nonempty_convergence_extension).2 h

example (h : ¬ OperatorKO7.ConfessionMethodFamily.HasUsableRulesConfessionRoute) :
    IsEmpty OperatorKO7.ConfessionMethodFamily.UsableRulesConvergenceExtension := by
  exact
    OperatorKO7.ConfessionMethodFamily.no_usableRules_convergence_extension_without_residual h

example (h : ¬ OperatorKO7.ConfessionMethodFamily.HasUsableRulesConfessionRoute)
    (ext : OperatorKO7.ConfessionMethodFamily.UsableRulesConvergenceExtension) : False := by
  exact
    (OperatorKO7.ConfessionMethodFamily.no_usableRules_convergence_extension_without_residual h).false ext

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.schemaDPPairProblemEvidence
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.directSubterm_to_originalSymbolSubterm
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.schemaSCTClosureSummary
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.argumentFilterTrace_eq_applyConstructorwiseFilter
  trivial

example : True := by
  have := @OperatorKO7.Meta.ConfessionMethodUsableRulesFinalStatus.UsableRulesFinalStatusCatalog
  trivial

example : True := by
  have := @OperatorKO7.Meta.ConfessionMethodUsableRulesFinalStatus.usableRules_final_status_catalog
  trivial

example : True := by
  have := @OperatorKO7.Meta.ConfessionMethodUsableRulesFinalStatus.usableRules_s5_final_status_closes_as_verified_fifthRoute
  trivial

-- Tropical continuation
example : @OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_tropical_primary_orients_dup_step_of_unbounded = @no_tropical_primary_orients_dup_step_of_unbounded := rfl

-- Max-aggregative depth barrier (Category C)
example : @no_maxDepth_orients_dup_step = @no_maxDepth_orients_dup_step := rfl

-- Affine-bound sharpness
example : True := by
  have := @OperatorKO7.StepDuplicating.affineThresholdMeasure_bound
  trivial

-- Matrix projection coverage
example : True := by
  have := @no_matrix_orients_dup_step_of_fixed_row_pump
  trivial

example {Sys : OperatorKO7.StepDuplicating.StepDuplicatingSchema.StepDuplicatingSystem} :
    OperatorKO7.ToolSearchFragmentCoverageFinalCatalog.ToolSearchFragmentFinalCatalog Sys :=
  OperatorKO7.ToolSearchFragmentCoverageFinalCatalog.tool_search_fragment_final_catalog
    (Sys := Sys)

example :
    OperatorKO7.ConstructionRouteCatalogCertificate.CanonicalConstructionCertificate :=
  OperatorKO7.ConstructionRouteCatalogCertificate.canonical_construction_certificate

example :
    OperatorKO7.ConstructionRouteCatalogPartition.CanonicalConstructionCertificateExactness := by
  exact
    OperatorKO7.ConstructionRouteCatalogPartition.canonical_construction_certificate_exactness
      OperatorKO7.ConstructionRouteCatalogCertificate.canonical_construction_certificate

-- Arbitrary mixed-matrix scalarization barrier
example : True := by
  have := @OperatorKO7.MatrixBarrierArbitrary.no_global_step_orientation_matrixArbitrary_of_scalar_dominance_pump
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.MatrixBarrierArbitraryInstances.no_global_step_orientation_matrixArbitrary_rowSum_of_scalar_dominance_pump
  trivial

example : True := by
  have := @OperatorKO7.MatrixBarrierArcticTropical.no_global_step_orientation_arcticMatrix_of_scalar_dominance_pump
  trivial

example : True := by
  have := @OperatorKO7.MatrixToolSearchMapping.fixedRow_fragment_no_global_orientation
  trivial

example : True := by
  have := @OperatorKO7.MatrixToolSearchMapping.rowSum_fragment_no_global_orientation
  trivial

example : True := by
  have := @OperatorKO7.MatrixToolSearchMapping.arcticFixedRow_fragment_no_global_orientation
  trivial

example : True := by
  have := @OperatorKO7.MatrixToolSearchMapping.arcticRowSum_fragment_no_global_orientation
  trivial

example : True := by
  have := @OperatorKO7.MatrixToolSearchMapping.tropicalFixedRow_fragment_no_global_orientation
  trivial

example : True := by
  have := @OperatorKO7.MatrixToolSearchMapping.tropicalRowSum_fragment_no_global_orientation
  trivial

-- Second schema instance
example : True := by
  have := @OperatorKO7.TextbookDupInstance.textbookSchema
  trivial

-- SCC utilities
example : True := by
  have := @OperatorKO7.MutualDuplicationCycleFlow.no_global_orients_ctx_additive
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.System.no_global_orients_ctx_additive
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationFiniteSchema.KCycleSystem.no_global_orients_ctx_affine_of_unbounded
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationSchema.System.no_global_orients_ctx_of_scalar_projection_affine_of_unbounded
  trivial

example : True := by
  have := @OperatorKO7.MutualDuplicationPayloadFlow.no_global_orients_ctx_additive
  trivial

-- Graph utilities
example : True := by
  have := @OperatorKO7.GraphPathExtraction.EdgePath
  trivial

-- DP fragment
example : True := by
  have := @OperatorKO7.DependencyPairsFragment.DPProjection.wfRev
  trivial

-- Paper 2 schema-level quantitative layer
example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.per_step_exchange
  trivial

#check terminalExternalizedTraceStorage
#check @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.ExternalizedTraceStorage.Package
#check @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.ExternalizedTraceStorage.CarrierEquivalenceResidual
#check @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.RecordEmissionWitness.terminalExternalizedTracePackage
#check @OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeRecordEmissionWitness_tracePackage

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.offset_conservation
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.RecordEmissionWitness.normalized_storage_description_lower_bound
  trivial

example : True := by
  have := OperatorKO7.StepDuplicating.StepDuplicatingSchema.free_semanticKernel_faithful_emitter_transaction_realizes_bridge
    (K := 1) (by decide)
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.sum_payloads_doubled
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.proof_entropy_nondecreasing
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.counter_unique_retained_coordinate
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.norm_mismatch_pairwise
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.permutation_gauge_symmetry_package
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.inefficiencyCoefficient_unbounded_atTop
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.inefficiencyCoefficient_perStep_isTheta_linearLog
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.explicitDescription_linear_gap
  trivial

-- Paper 2 seed-carrier factorization
example : True := by
  have := @OperatorKO7.SchemaSeedCarrier.PayloadObservable.factorization_criterion
  trivial

example : True := by
  have := @OperatorKO7.SchemaSeedCarrier.additiveObservable_not_factors
  trivial

-- Paper 2 schema forgetting witness
example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.ForgettingWitness.ofProjectionRank
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.RouteEvidence.toProjectionRank
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.ForgettingWitness.ofRouteEvidence
  trivial

-- Paper 2 schema operational incompleteness
example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.OperationalIncompleteness.ofProjectionRank
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.construction_confession_exclusive
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.directAggregationQuestion_operationallyIncomplete
  trivial

example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.canonical_operational_instance
  trivial

-- Paper 2 schema witness order
example : True := by
  have := @OperatorKO7.StepDuplicating.StepDuplicatingSchema.SchemaWitnessTower.OB_iff_no_directWhole
  trivial

-- Generic route-evidence unification layer
example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.all_route_local_evidence_share_generic_route_evidence
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.all_generic_route_evidence_yields_forgetting_witnesses
  trivial

-- New SCL-2026-04-26-06 convergence-package projection corollaries
example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.confessionRouteConvergencePackage_commonRouteEvidence_rank
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.confessionRouteConvergencePackage_routes_pairwise_agree
  trivial

example : True := by
  have := @OperatorKO7.ConfessionMethodFamily.confessionRouteConvergencePackage_all_routes_recover_dp_rank
  trivial

-- Transformed-call (W2) classification bridge, now reachable through SchemaAPI
example : True := by
  have := @OperatorKO7.TransformedCallClassification.fullDuplicating_w2_success
  trivial

example : True := by
  have := @OperatorKO7.TransformedCallClassification.fullDuplicating_w2_success_projects_confession_route_evidence
  trivial

example : True := by
  have := @OperatorKO7.TransformedCallClassification.canonical_w2_witness_catalog
  trivial

example : True := by
  have := @OperatorKO7.ToolSearchFragmentCoverageFinalCatalog.tool_search_fragment_final_catalog
  trivial

example : True := by
  have := @OperatorKO7.ConstructionRouteCatalogPartition.canonical_construction_certificate_exactness
  trivial

end SchemaAPIReach
