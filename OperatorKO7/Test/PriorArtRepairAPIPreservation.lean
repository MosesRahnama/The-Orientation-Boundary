import OperatorKO7.OrientationBoundaryAPI
import OperatorKO7.CrossPaperAPI
import OperatorKO7.InformationalIncompletenessAPI
import OperatorKO7.Meta.Recursor.CanonicalExecution
import OperatorKO7.Meta.DistinctionBoundary.TerminalRepair
import OperatorKO7.Meta.DistinctionBoundary.RepairCategory
import OperatorKO7.Meta.DistinctionBoundary.GuardingComonad

/-!
# Tier 17 API preservation and migration reach

G-03 requires an external elaboration receipt and type hashes.  This source
asserts name reach from the public roots while keeping old declarations and
new migration targets visibly separate.
-/

set_option autoImplicit false

-- Preserve: scalar and vector orientation core.
#check OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure.orients_iff_payloadBlind_and_counterStrict
#check OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure.dominated_scalar_orients_implies_payload_blind
#check OperatorKO7.StepDuplicating.StepDuplicatingSchema.VecLexLt
#check OperatorKO7.Meta.BoundaryGeneral.VectorGrammarClosure.PrimaryFirstLt
#check OperatorKO7.StepDuplicating.StepDuplicatingSchema.no_global_orients_matrixLexD_with_primary_pump
#check OperatorKO7.StepDuplicating.BarrierCertificate
#check OperatorKO7.StepDuplicating.StepDuplicatingSchema.RelationBarrierCertificate
#check OperatorKO7.StepDuplicating.StepDuplicatingSchema.ScalarBarrierClass
#check OperatorKO7.RDRSMethodCertificate.RawDirectCertificate
#check OperatorKO7.RDRSMethodCertificate.normalize_total
#check OperatorKO7.RDRSTerminationMethodUniverse.allMethodFamilies_length

-- Preserve: generic operational and quotient surfaces.
#check OperatorKO7.StepDuplicating.StepDuplicatingSchema.OperationallyIncomplete
#check OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive.TypedBoundary
#check OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive.TypedBoundary.verdict_not_observation_function
#check OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel.factorization
#check OperatorKO7.StepDuplicating.StepDuplicatingSchema.construction_confession_exclusive
#check OperatorKO7.Meta.LCELBoundaryReimportRepair.annotated_clauses_strictly_weaker_than_conservativity

-- Preserve: exact input-family comparison, now explicitly named as such.
#check OperatorKO7.Meta.Recursor.CircularIdentity.RecursorOrbit
#check OperatorKO7.Meta.Recursor.CanonicalExecution.RecursorInputFamily
#check OperatorKO7.Meta.Recursor.MassProfileIdentity.recursorOrbit_selfEmbeddingOrbit_massProfile_pointwise_eq
#check OperatorKO7.Meta.Recursor.MassProfileIdentity.mergeChainOrbit_massProfile_never_eq_recursorOrbit

-- Preserve: seven-constructor and diagonal-necessity roots.
#check OperatorKO7.Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional
#check OperatorKO7.Meta.DistinctionBoundary.confluence_forces_no_diagonal_diff
#check MetaSN_KO7.confluentSafe

-- Legacy compatibility only: these names remain importable for downstream
-- code, but their modules are no longer re-exported by `CrossPaperAPI`.
#check OperatorKO7.Meta.DistinctionBoundary.TerminalRepair.safeStep_terminal_repair
#check OperatorKO7.Meta.DistinctionBoundary.RepairCategory.safeStep_final_object_hom_nonempty
#check OperatorKO7.Meta.DistinctionBoundary.GuardingComonad.guarding_is_idempotent_interior

-- Replace/migrate: old advertised readings point to these stronger objects.
#check OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair.primaryFirstLt_fin3_two_cycle
#check OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair.vecLexLt_wellFounded
#check OperatorKO7.Meta.Recursor.CanonicalExecution.canonicalExecution
#check OperatorKO7.Meta.OperationalInexpressibility.KO7FixedInputLanguage.ko7FixedInputBoundary
#check OperatorKO7.Meta.LCELAnnotatedReimport.AnnotatedDerivation
#check OperatorKO7.Meta.LCELTypedDerivations.TheoryExtension
#check OperatorKO7.Meta.LCELFactorization.SplitProjection
#check OperatorKO7.Meta.LCELDPInstance.KO7FixedSystemLicense
#check OperatorKO7.Meta.LCELDPInstance.ko7DPCertificateConsumingLicense
#check OperatorKO7.Meta.LCELDPInstance.ko7TypedDPSemanticBoundaryModel
#check OperatorKO7.Meta.DistinctionBoundary.AdmissibleAtDiagonal
#check OperatorKO7.Meta.DistinctionBoundary.CriticalRepairObject
#check OperatorKO7.Meta.DistinctionBoundary.canonicalCriticalRepair_isTerminal
#check OperatorKO7.Meta.DistinctionBoundary.criticalGuard_idempotent
#check OperatorKO7.Meta.SafeStep.SafeStepConfessionBridge.safeStepSemanticClassifier
#check OperatorKO7.Meta.OperationalInexpressibility.KO7LicensedChannel.ko7_licensedChannel_headline
