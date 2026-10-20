import OperatorKO7.Meta.RDRSProjectionTransaction
import OperatorKO7.Meta.BarrierWitness_Extended
import OperatorKO7.Meta.EscapeTrichotomy
import OperatorKO7.Meta.MatrixBarrierArbitrary_Schema
import OperatorKO7.Meta.KBO_Impossible
import OperatorKO7.Meta.PolyInterpretation_FullStep
import OperatorKO7.Meta.ConstructionMethodClassification
import OperatorKO7.Meta.ObjectAxiom_Ablation
import OperatorKO7.Meta.SharingBarrierLift
import OperatorKO7.Meta.MutualDuplication_Preserving
import OperatorKO7.Meta.MPO_Precedence_Barrier
import OperatorKO7.Meta.SchemaNormMismatch
import OperatorKO7.Meta.SchemaSeedCarrierFactorization
import OperatorKO7.Meta.RDRSSemanticArbitraryClassifier
import OperatorKO7.Meta.RDRSSemanticClassifier
import OperatorKO7.Meta.RDRSSearchBudgetInvariance
import OperatorKO7.Meta.RDRSReflectedDirectMeasureDSL
import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
import OperatorKO7.Meta.ContextClosedBarrier
import OperatorKO7.Meta.TPDB_Export
import OperatorKO7.Meta.TTT2_CertificateReplay
import OperatorKO7.Meta.DPSubtermCriterionExact
import OperatorKO7.Meta.SafeTrace_TripleLexExactness
import OperatorKO7.Meta.ComputableMeasure
import OperatorKO7.Meta.Newman_Safe
import OperatorKO7.Meta.SafeStepCtx_Confluence
import OperatorKO7.Meta.SynthesisOracle
import OperatorKO7.Meta.RDRSTerminationMethodUniverseCloseout
import OperatorKO7.Meta.RDRSSemanticCoverageLedger
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability
import OperatorKO7.Meta.ComparatorNecessity
import OperatorKO7.Meta.ComparatorNecessityPartial
import OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence
import OperatorKO7.Meta.DistinctionBoundary.DiagonalJoinObstruction
import OperatorKO7.Meta.DistinctionBoundary.SafeStepPolicyMaximality
import OperatorKO7.Meta.BoundaryOperator.AxisIndependence
import OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope
import OperatorKO7.Meta.SafeStep.DistinctionControls
import OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord
import OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit
import OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit
import OperatorKO7.Meta.SafeStep.BranchTransaction
import OperatorKO7.Meta.SafeStep.BranchEntropy
import OperatorKO7.Meta.DistinctionBoundary.Quantitative.TerminalMultiplicity
import OperatorKO7.Meta.DistinctionBoundary.EqualityModeCertificate
import OperatorKO7.Meta.SafeStep.FaithfulnessNoGo
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.OrthogonalDefects
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.KO7SemanticAdequacy
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.KO7TerminalSupportCollapse
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.StructuralComposition
import OperatorKO7.Meta.LicensedBoundaryCalculus.Integrated.CertifiedCompositionBoundary

/-!
# Hallucination-detection source-mechanism claim reach gate

This audit module pins the live theorem types and axiom surfaces for HD-OB-05 through
HD-OB-15, HD-OB-17 through HD-OB-27, and HD-DB-02 through HD-DB-18.  It checks only
the formal source mechanisms.  Cross-domain transfer to model behavior remains an
ANALOGY or NO-TRANSPORT claim unless a separate adapter and validation theorem is supplied.
-/

namespace OperatorKO7.Test.HallucinationDetectionOrientationDistinctionClaimReach

-- HD-OB-05: relation and scope stay explicit.
#check @OperatorKO7.RDRSProjectionTransaction.ProjectionTransactionEscape.lifted_orients
#check @OperatorKO7.ContextClosedBarrier.stepCtxFull_orientation_implies_root
#print axioms OperatorKO7.RDRSProjectionTransaction.ProjectionTransactionEscape.lifted_orients
#print axioms OperatorKO7.ContextClosedBarrier.stepCtxFull_orientation_implies_root

-- HD-OB-06: constructive freeze-and-pump certificate.
#check @OperatorKO7.StepDuplicating.StepDuplicatingSchema.affine_with_pump_witness
#print axioms OperatorKO7.StepDuplicating.StepDuplicatingSchema.affine_with_pump_witness

-- HD-OB-07: escape trichotomy.
#check @OperatorKO7.EscapeTrichotomy.ko7_nat_direct_escape_trichotomy
#print axioms OperatorKO7.EscapeTrichotomy.ko7_nat_direct_escape_trichotomy

-- HD-OB-08: scalarization of a mixed matrix witness.
#check @OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_matrixArbitrary_orients_dup_step_of_scalar_dominance_pump
#print axioms OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_matrixArbitrary_orients_dup_step_of_scalar_dominance_pump

-- HD-OB-09: symbolic multiplicity and the KBO variable condition.
#check @OperatorKO7.KBOImpossible.no_kbo_orients_ko7_rec_succ_trace
#print axioms OperatorKO7.KBOImpossible.no_kbo_orients_ko7_rec_succ_trace

-- HD-OB-10: a successful construction exposes the assumption it leaves.
#check @OperatorKO7.PolyInterpretation.W_orients_step
#check @OperatorKO7.PolyInterpretation.W_violates_transparency
#print axioms OperatorKO7.PolyInterpretation.W_orients_step
#print axioms OperatorKO7.PolyInterpretation.W_violates_transparency

-- HD-OB-11: causal ablations distinguish sharing from an irrelevant wrapper collapse.
#check @OperatorKO7.SharingBarrierLift.sharing_breaks_tree_barrier
#check @OperatorKO7.ObjectAxiomAblation.collapse_surrogate_preserves_direct_barrier
#print axioms OperatorKO7.SharingBarrierLift.sharing_breaks_tree_barrier
#print axioms OperatorKO7.ObjectAxiomAblation.collapse_surrogate_preserves_direct_barrier

-- HD-OB-12: a full synchronized cycle exposes the obstruction.
#check @OperatorKO7.MutualDuplicationPreserving.no_additive_orients_synchronized_cycle
#print axioms OperatorKO7.MutualDuplicationPreserving.no_additive_orients_synchronized_cycle

-- HD-OB-13: the nearby bad precedence fails on a concrete instance.
#check @OperatorKO7.MPOPrecedenceBarrier.not_mpoBad_rec_succ_instance
#print axioms OperatorKO7.MPOPrecedenceBarrier.not_mpoBad_rec_succ_instance

-- HD-OB-14: additive mass and support-style readings separate.
#check @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.normInf_le_norm1
#check @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.norm0_le_normInf_of_posSize
#check @OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.inefficiency_doubled_burden_lower_bound
#print axioms OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.normInf_le_norm1
#print axioms OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.norm0_le_normInf_of_posSize
#print axioms OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem.inefficiency_doubled_burden_lower_bound

-- HD-OB-15: the positive witness is checked against every constructor of Step.
#check @OperatorKO7.PolyInterpretation.W_orients_step
#print axioms OperatorKO7.PolyInterpretation.W_orients_step

-- HD-OB-17: carrier-insensitivity is equivalent to factorization through the seed.
#check @OperatorKO7.SchemaSeedCarrier.PayloadObservable.factorization_criterion
#print axioms OperatorKO7.SchemaSeedCarrier.PayloadObservable.factorization_criterion

-- HD-OB-18: raw payload mention is separated from decisive payload sensitivity.
#check @OperatorKO7.RDRSSemanticArbitraryClassifier.counterFirstLex_no_arbitrary_decisive_payload_sensitive
#print axioms OperatorKO7.RDRSSemanticArbitraryClassifier.counterFirstLex_no_arbitrary_decisive_payload_sensitive

-- HD-OB-19: the classifier is total only on its normalized certificate domain.
#check @OperatorKO7.RDRSSemanticClassifier.semantic_classifier_total
#check @OperatorKO7.RDRSSemanticClassifier.semantic_temporary_unclassified_count_is_zero
#print axioms OperatorKO7.RDRSSemanticClassifier.semantic_classifier_total
#print axioms OperatorKO7.RDRSSemanticClassifier.semantic_temporary_unclassified_count_is_zero

-- HD-OB-20: search budget does not change a W0 boundary classification.
#check @OperatorKO7.RDRSSearchBudgetInvariance.boundary_invariant_under_W0_budget
#print axioms OperatorKO7.RDRSSearchBudgetInvariance.boundary_invariant_under_W0_budget

-- HD-OB-21: reflected totality, soundness, and a named semantic false negative.
#check @OperatorKO7.RDRSReflectedDirectMeasureDSL.reflectedClassify_total
#check @OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure.payloadEffective?_not_payloadBlind
#check @OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure.payloadEffective?_semantic_completeness_gap
#print axioms OperatorKO7.RDRSReflectedDirectMeasureDSL.reflectedClassify_total
#print axioms OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure.payloadEffective?_not_payloadBlind
#print axioms OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure.payloadEffective?_semantic_completeness_gap

-- HD-OB-22: internal positive replay and theorem-backed negative are distinct receipts.
#check @OperatorKO7.ko7_full_step_tpdb_matches_artifact_text
#check @OperatorKO7.TTT2CertificateReplay.ko7FastReplay_matches_all_extraction_surfaces
#check @OperatorKO7.TTT2CertificateReplay.ko7FastReplay_sound
#check @OperatorKO7.DPSubtermCriterionExactNS.dp_subterm_and_ceta_independent_support
#check @OperatorKO7.KBOImpossible.no_kbo_orients_ko7_rec_succ_trace
#print axioms OperatorKO7.ko7_full_step_tpdb_matches_artifact_text
#print axioms OperatorKO7.TTT2CertificateReplay.ko7FastReplay_matches_all_extraction_surfaces
#print axioms OperatorKO7.TTT2CertificateReplay.ko7FastReplay_sound
#print axioms OperatorKO7.DPSubtermCriterionExactNS.dp_subterm_and_ceta_independent_support
#print axioms OperatorKO7.KBOImpossible.no_kbo_orients_ko7_rec_succ_trace

-- HD-OB-23: ambient exactness fails, while the realizable subcarrier has its own package.
#check @OperatorKO7.SafeTraceTripleLexExactness.trace_exact_order_type_residual_false
#check @OperatorKO7.SafeTraceTripleLexExactness.traceRealizableCarrierExactnessPackage
#print axioms OperatorKO7.SafeTraceTripleLexExactness.trace_exact_order_type_residual_false
#print axioms OperatorKO7.SafeTraceTripleLexExactness.traceRealizableCarrierExactnessPackage

-- HD-OB-24: generated text, internal replay, and independent support remain separate layers.
#check @OperatorKO7.ko7_full_step_tpdb_matches_artifact_text
#check @OperatorKO7.TTT2CertificateReplay.ko7FastReplay_sound
#check @OperatorKO7.DPSubtermCriterionExactNS.dp_subterm_and_ceta_independent_support
#print axioms OperatorKO7.ko7_full_step_tpdb_matches_artifact_text
#print axioms OperatorKO7.TTT2CertificateReplay.ko7FastReplay_sound
#print axioms OperatorKO7.DPSubtermCriterionExactNS.dp_subterm_and_ceta_independent_support

-- HD-OB-25: the guarded relation has both the certified descent and confluence receipts.
#check @OperatorKO7.MetaCM.wf_SafeStepRev_c
#check @MetaSN_KO7.confluentSafe
#check @MetaSN_KO7.confluentSafeCtx
#print axioms OperatorKO7.MetaCM.wf_SafeStepRev_c
#print axioms MetaSN_KO7.confluentSafe
#print axioms MetaSN_KO7.confluentSafeCtx

-- HD-OB-26: successful synthesis changes the failed certificate.
#check @OperatorKO7.StepDuplicating.successful_refinement_changes_certificate
#print axioms OperatorKO7.StepDuplicating.successful_refinement_changes_certificate

-- HD-OB-27: zero residual is scoped to the named finite universe.
#check @OperatorKO7.RDRSTerminationMethodUniverseCloseout.rdrs_termination_method_universe_closed
#check @OperatorKO7.RDRSSemanticCoverageLedger.semantic_coverage_ledger_closed
#print axioms OperatorKO7.RDRSTerminationMethodUniverseCloseout.rdrs_termination_method_universe_closed
#print axioms OperatorKO7.RDRSSemanticCoverageLedger.semantic_coverage_ledger_closed

-- HD-DB-02: disequality is not expressible by the owned signature algebra.
#check @OperatorKO7.Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional
#print axioms OperatorKO7.Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional

-- HD-DB-03: total comparison and guarded global confluence have separate receipts.
#check @OperatorKO7.Meta.ComparatorNecessity.exactComparator_decidableEq
#check @OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_globally_confluent
#print axioms OperatorKO7.Meta.ComparatorNecessity.exactComparator_decidableEq
#print axioms OperatorKO7.Meta.DistinctionBoundary.GlobalConfluence.safeStep_globally_confluent

-- HD-DB-04: independently admissible finite-fiber greatest repair and guard.
#check @OperatorKO7.Meta.DistinctionBoundary.canonicalDiagonalCriticalPolicy_is_greatest_semantic
#check @OperatorKO7.Meta.DistinctionBoundary.criticalGuard_idempotent
#print axioms OperatorKO7.Meta.DistinctionBoundary.canonicalDiagonalCriticalPolicy_is_greatest_semantic
#print axioms OperatorKO7.Meta.DistinctionBoundary.criticalGuard_idempotent

-- HD-DB-05: orientation and distinction are independent typed axes.
#check @OperatorKO7.Meta.BoundaryOperator.orientation_distinction_axis_independent
#print axioms OperatorKO7.Meta.BoundaryOperator.orientation_distinction_axis_independent

-- HD-DB-06: contextual survival and dissolution are one scoped theorem bundle.
#check @OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope.contextual_fracture_scope
#print axioms OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope.contextual_fracture_scope

-- HD-DB-07: non-left-linearity is necessary here and insufficient by itself.
#check @OperatorKO7.Meta.SafeStep.DistinctionControls.nonLeftLinearity_necessary_not_sufficient
#print axioms OperatorKO7.Meta.SafeStep.DistinctionControls.nonLeftLinearity_necessary_not_sufficient

-- HD-DB-08: equality is record-inert on a distinction-complete surface.
#check @OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord.equality_record_inert
#print axioms OperatorKO7.Meta.BoundaryGeneral.DistinctionRecord.equality_record_inert

-- HD-DB-09: zero channel deficit and the raw fork coexist.
#check @OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit.eqW_diagonal_echo_vacuum_with_fork
#print axioms OperatorKO7.Meta.InformationalIncompleteness.EqWDiagonalDeficit.eqW_diagonal_echo_vacuum_with_fork

-- HD-DB-10: the partial comparator has Y, N, and abstention, and decisiveness yields DecidableEq.
#check @OperatorKO7.Meta.ComparatorNecessityPartial.decisive_decidableEq
#check @OperatorKO7.Meta.ComparatorNecessityPartial.classify_exhaustive
#print axioms OperatorKO7.Meta.ComparatorNecessityPartial.decisive_decidableEq
#print axioms OperatorKO7.Meta.ComparatorNecessityPartial.classify_exhaustive

-- HD-DB-11: licensed-channel deficit lies between zero and residual uncertainty.
#check @OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit.deficit_bracket
#print axioms OperatorKO7.Meta.InformationalIncompleteness.LicensedChannelDeficit.deficit_bracket

-- HD-DB-12: the branch transaction carries a selected branch and refusal certificate.
#check @OperatorKO7.Meta.SafeStep.BranchTransaction.ko7_branchTransaction
#print axioms OperatorKO7.Meta.SafeStep.BranchTransaction.ko7_branchTransaction

-- HD-DB-13: terminal multiplicity needs the stated local-normalization premise.
#check @OperatorKO7.Meta.DistinctionBoundary.Quantitative.confluentAt_iff_terminalMultiplicity_eq_one
#check @OperatorKO7.Meta.DistinctionBoundary.Quantitative.normalizingAt_premise_cannot_be_weakened
#check @OperatorKO7.Meta.SafeStep.BranchEntropy.eqW_void_void_branchEntropy_collapse
#print axioms OperatorKO7.Meta.DistinctionBoundary.Quantitative.confluentAt_iff_terminalMultiplicity_eq_one
#print axioms OperatorKO7.Meta.DistinctionBoundary.Quantitative.normalizingAt_premise_cannot_be_weakened
#print axioms OperatorKO7.Meta.SafeStep.BranchEntropy.eqW_void_void_branchEntropy_collapse

-- HD-DB-14: the enumerated equality-mode certificate is complete at its stated scope.
#check @OperatorKO7.Meta.DistinctionBoundary.EqualityModeCertificate.five_mode_certificate_complete
#print axioms OperatorKO7.Meta.DistinctionBoundary.EqualityModeCertificate.five_mode_certificate_complete

-- HD-DB-15: payload-discarding covering transport cannot be payload-faithful.
#check @OperatorKO7.Meta.SafeStep.FaithfulnessNoGo.not_payloadFaithful_of_covers
#print axioms OperatorKO7.Meta.SafeStep.FaithfulnessNoGo.not_payloadFaithful_of_covers

-- HD-DB-16: domain exclusion and license rejection form a disjoint sum.
#check @OperatorKO7.Meta.LicensedBoundaryCalculus.PartialLicensedReductionMorphism.nonAdmittedRawEdge_equiv_domainExcluded_sum_licenseRejected
#check @OperatorKO7.Meta.LicensedBoundaryCalculus.PartialLicensedReductionMorphism.state_domain_edge_defects_disjoint
#print axioms OperatorKO7.Meta.LicensedBoundaryCalculus.PartialLicensedReductionMorphism.nonAdmittedRawEdge_equiv_domainExcluded_sum_licenseRejected
#print axioms OperatorKO7.Meta.LicensedBoundaryCalculus.PartialLicensedReductionMorphism.state_domain_edge_defects_disjoint

-- HD-DB-17: semantic profile coordinates are tied to an adequacy certificate.
#check @OperatorKO7.Meta.LicensedBoundaryCalculus.SemanticAdequacyCertificate.terminalMultiplicity_eq_alternative_card
#check @OperatorKO7.Meta.LicensedBoundaryCalculus.KO7DistinctionAdapter.ko7_raw_semantic_adequacy_fixture
#check @OperatorKO7.Meta.LicensedBoundaryCalculus.TerminalSupportCollapse.value_nonneg
#print axioms OperatorKO7.Meta.LicensedBoundaryCalculus.SemanticAdequacyCertificate.terminalMultiplicity_eq_alternative_card
#print axioms OperatorKO7.Meta.LicensedBoundaryCalculus.KO7DistinctionAdapter.ko7_raw_semantic_adequacy_fixture
#print axioms OperatorKO7.Meta.LicensedBoundaryCalculus.TerminalSupportCollapse.value_nonneg

-- HD-DB-18: structural composition is universal; semantic composition needs a domain law.
#check @OperatorKO7.Meta.LicensedBoundaryCalculus.PartialLicensedReductionMorphism.structural_composition_universal
#check @OperatorKO7.Meta.LicensedBoundaryCalculus.KO7DistinctionAdapter.no_universal_semantic_composer_without_domain_law
#print axioms OperatorKO7.Meta.LicensedBoundaryCalculus.PartialLicensedReductionMorphism.structural_composition_universal
#print axioms OperatorKO7.Meta.LicensedBoundaryCalculus.KO7DistinctionAdapter.no_universal_semantic_composer_without_domain_law

end OperatorKO7.Test.HallucinationDetectionOrientationDistinctionClaimReach
