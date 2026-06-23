# Public Lean Release Note

**Date:** 2026-05-23

This repository is the public companion artifact for three manuscripts:

- *The Orientation Boundary for Step-Duplicating Recursors: Mechanized Impossibility, Escape, and Certification.*
- *Operational Inexpressibility at the Primitive-Recursion Orientation Boundary.*
- *The Confluence-Preservation Boundary for Diagonal Identity Queries: Non-Left-Linearity, Signature Inexpressibility, and External Guarding.*

The files below are included in this public Lean release for inspection of the theorem surfaces used by those three manuscripts. The first two papers trace the termination axis of the boundary; the third traces the confluence axis, contributing a generic first-order Critical Pair Lemma library, the equality-witness diagonal fork with its global-confluence and guarded-repair results, and a metatheoretic-strength calibration in reverse mathematics. Reviewer-NDA modules are the runtime-consumed classifier, oracle, coverage-ledger, audit, route-ledger, universal-API, plug-intake, and bridge surfaces that the supervisory engine product depends on at run time; they are released to qualified reviewers under NDA, not in this public tree.

## Release Contents

```text
[manuscript theorem claims]
        |
        v
[Lean source files and external proof artifacts listed below]
        |
        v
[reviewer verification]
```

| Group | Included paths |
|---|---:|
| Orientation Boundary Lean files | 256 |
| Operational Inexpressibility Lean files | 96 |
| Confluence-Preservation Boundary Lean files | 73 |
| Shared Lean infrastructure | 6 |
| External proof artifacts | 12 |
| Reviewer NDA Lean files for Orientation Boundary | 141 |
| Reviewer NDA Lean files for Operational Inexpressibility | 48 |
| Reviewer NDA Lean files for Confluence-Preservation Boundary | 23 |

## Paper A Lean Files

| Path |
|---|
| `OperatorKO7\Kernel.lean` |
| `OperatorKO7\Meta\AffineThresholdSharpness.lean` |
| `OperatorKO7\Meta\ArcticBarrier.lean` |
| `OperatorKO7\Meta\ArcticBarrier_Schema.lean` |
| `OperatorKO7\Meta\BarrierWitness.lean` |
| `OperatorKO7\Meta\BoundaryFactorization.lean` |
| `OperatorKO7\Meta\CanonicalWitnessUniversality.lean` |
| `OperatorKO7\Meta\CompositionalMeasure_Impossibility.lean` |
| `OperatorKO7\Meta\ComputableMeasure.lean` |
| `OperatorKO7\Meta\ComputableMeasure_Verification.lean` |
| `OperatorKO7\Meta\Confluence_Safe.lean` |
| `OperatorKO7\Meta\Conjecture_Boundary.lean` |
| `OperatorKO7\Meta\ConstructionMethodClassification.lean` |
| `OperatorKO7\Meta\ConstructionRouteCatalog.lean` |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Certificate.lean` |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Payload.lean` |
| `OperatorKO7\Meta\ContextClosed_SN.lean` |
| `OperatorKO7\Meta\ContextClosed_SN_Full.lean` |
| `OperatorKO7\Meta\ContextClosedBarrier.lean` |
| `OperatorKO7\Meta\ContextSCCTransport.lean` |
| `OperatorKO7\Meta\ContextualCopyBudget.lean` |
| `OperatorKO7\Meta\ContextualCopyBudget_NoGo.lean` |
| `OperatorKO7\Meta\DependencyPairs_CallGraph.lean` |
| `OperatorKO7\Meta\DependencyPairs_ExtractedCallGraph.lean` |
| `OperatorKO7\Meta\DependencyPairs_FiniteCarrierView.lean` |
| `OperatorKO7\Meta\DependencyPairs_FiniteGraph.lean` |
| `OperatorKO7\Meta\DependencyPairs_FirstOrderEngine.lean` |
| `OperatorKO7\Meta\DependencyPairs_FirstOrderExtraction.lean` |
| `OperatorKO7\Meta\DependencyPairs_FirstOrderFrontend.lean` |
| `OperatorKO7\Meta\DependencyPairs_Fragment.lean` |
| `OperatorKO7\Meta\DependencyPairs_HeadView.lean` |
| `OperatorKO7\Meta\DependencyPairs_KernelFirstOrder.lean` |
| `OperatorKO7\Meta\DependencyPairs_TPDBExtraction.lean` |
| `OperatorKO7\Meta\DependencyPairs_Works.lean` |
| `OperatorKO7\Meta\DepthBarrier.lean` |
| `OperatorKO7\Meta\DepthBarrier_Schema.lean` |
| `OperatorKO7\Meta\DirectBarrierScope.lean` |
| `OperatorKO7\Meta\DirectToolSearchMapping.lean` |
| `OperatorKO7\Meta\DirectWholeTermObserver.lean` |
| `OperatorKO7\Meta\DM_OrderType.lean` |
| `OperatorKO7\Meta\DM_OrderType_LowerBound.lean` |
| `OperatorKO7\Meta\DM_TripleLexExactness.lean` |
| `OperatorKO7\Meta\DM_TripleLexExactness_FinalCatalog.lean` |
| `OperatorKO7\Meta\DM_TripleLexImage.lean` |
| `OperatorKO7\Meta\DM_UpstreamSurface.lean` |
| `OperatorKO7\Meta\DP_BaseOrder_Boundary.lean` |
| `OperatorKO7\Meta\DPSubtermCriterionExact.lean` |
| `OperatorKO7\Meta\DuplicatingRecursiveFamily.lean` |
| `OperatorKO7\Meta\EqGuardedConfluence.lean` |
| `OperatorKO7\Meta\EqW_Guard_Barrier.lean` |
| `OperatorKO7\Meta\EscapeTrichotomy.lean` |
| `OperatorKO7\Meta\EscapeTrichotomy_Schema.lean` |
| `OperatorKO7\Meta\ExtendedDirectToolSearchMapping.lean` |
| `OperatorKO7\Meta\ExternalizedTraceStorage.lean` |
| `OperatorKO7\Meta\FiniteGraphReachability.lean` |
| `OperatorKO7\Meta\FiniteGraphSCC.lean` |
| `OperatorKO7\Meta\GraphPathExtraction.lean` |
| `OperatorKO7\Meta\HigherOrderNoSharingBoundary.lean` |
| `OperatorKO7\Meta\HigherOrderRewriting_BetaBinder.lean` |
| `OperatorKO7\Meta\HigherOrderRewriting_Boundary.lean` |
| `OperatorKO7\Meta\HigherOrderRewriting_CaptureSubfamilies.lean` |
| `OperatorKO7\Meta\HigherOrderRewriting_Syntax.lean` |
| `OperatorKO7\Meta\HigherOrderSharingBoundary.lean` |
| `OperatorKO7\Meta\HigherOrderSharingBoundary_FinalCatalog.lean` |
| `OperatorKO7\Meta\Impossibility_Lemmas.lean` |
| `OperatorKO7\Meta\KBO_Impossible.lean` |
| `OperatorKO7\Meta\KBO_Impossible_Schema.lean` |
| `OperatorKO7\Meta\KO7EscapeRouteCharacterization.lean` |
| `OperatorKO7\Meta\KO7RDRSAdapter.lean` |
| `OperatorKO7\Meta\LinearRec_Ablation.lean` |
| `OperatorKO7\Meta\ManySortedBarrierSurvival.lean` |
| `OperatorKO7\Meta\MatrixBarrier2.lean` |
| `OperatorKO7\Meta\MatrixBarrier2_Schema.lean` |
| `OperatorKO7\Meta\MatrixBarrierArbitrary.lean` |
| `OperatorKO7\Meta\MatrixBarrierArbitrary_Instances.lean` |
| `OperatorKO7\Meta\MatrixBarrierArbitrary_Schema.lean` |
| `OperatorKO7\Meta\MatrixBarrierArcticTropical.lean` |
| `OperatorKO7\Meta\MatrixBarrierArcticTropical_Instances.lean` |
| `OperatorKO7\Meta\MatrixBarrierArcticTropical_Schema.lean` |
| `OperatorKO7\Meta\MatrixBarrierD.lean` |
| `OperatorKO7\Meta\MatrixBarrierD_Schema.lean` |
| `OperatorKO7\Meta\MatrixBarrierFunctional.lean` |
| `OperatorKO7\Meta\MatrixBarrierFunctional_Schema.lean` |
| `OperatorKO7\Meta\MatrixBarrierLex.lean` |
| `OperatorKO7\Meta\MatrixBarrierLex_Schema.lean` |
| `OperatorKO7\Meta\MatrixBarrierLexD.lean` |
| `OperatorKO7\Meta\MatrixBarrierLexD_Schema.lean` |
| `OperatorKO7\Meta\MatrixBarrierLexPermD.lean` |
| `OperatorKO7\Meta\MatrixBarrierLexPermD_Schema.lean` |
| `OperatorKO7\Meta\MatrixBarrierMix2.lean` |
| `OperatorKO7\Meta\MatrixBarrierMix2_Schema.lean` |
| `OperatorKO7\Meta\MatrixOrderInterfaces.lean` |
| `OperatorKO7\Meta\MatrixOverPolynomialReduction.lean` |
| `OperatorKO7\Meta\MatrixResidualClosureCatalog.lean` |
| `OperatorKO7\Meta\MatrixResidualTaxonomy.lean` |
| `OperatorKO7\Meta\MatrixToolSearchMapping.lean` |
| `OperatorKO7\Meta\MatrixUnrestrictedSplit.lean` |
| `OperatorKO7\Meta\MaxBarrier.lean` |
| `OperatorKO7\Meta\MaxBarrier_Schema.lean` |
| `OperatorKO7\Meta\MPO_FullStep.lean` |
| `OperatorKO7\Meta\MPO_Precedence_Barrier.lean` |
| `OperatorKO7\Meta\MPO_ProofTheoreticBound.lean` |
| `OperatorKO7\Meta\Mu3c_Image_LowerBound.lean` |
| `OperatorKO7\Meta\MultilinearBarrier.lean` |
| `OperatorKO7\Meta\MultilinearBarrier_Schema.lean` |
| `OperatorKO7\Meta\MutualDuplication_CallGraph.lean` |
| `OperatorKO7\Meta\MutualDuplication_Case.lean` |
| `OperatorKO7\Meta\MutualDuplication_CycleFlow.lean` |
| `OperatorKO7\Meta\MutualDuplication_ExtractedCallGraph.lean` |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema.lean` |
| `OperatorKO7\Meta\MutualDuplication_General.lean` |
| `OperatorKO7\Meta\MutualDuplication_GraphCycle.lean` |
| `OperatorKO7\Meta\MutualDuplication_KNode.lean` |
| `OperatorKO7\Meta\MutualDuplication_KNode_Abstract.lean` |
| `OperatorKO7\Meta\MutualDuplication_PacketGraph.lean` |
| `OperatorKO7\Meta\MutualDuplication_PayloadFlow.lean` |
| `OperatorKO7\Meta\MutualDuplication_Preserving.lean` |
| `OperatorKO7\Meta\MutualDuplication_Preserving_Abstract.lean` |
| `OperatorKO7\Meta\MutualDuplication_Preserving_KNode.lean` |
| `OperatorKO7\Meta\MutualDuplication_Preserving_Transparent.lean` |
| `OperatorKO7\Meta\MutualDuplication_RelationalGraph.lean` |
| `OperatorKO7\Meta\MutualDuplication_Schema.lean` |
| `OperatorKO7\Meta\MutualDuplication_SchemaBarrier.lean` |
| `OperatorKO7\Meta\MutualDuplication_SchemaProjection.lean` |
| `OperatorKO7\Meta\MutualDuplication_Transparent.lean` |
| `OperatorKO7\Meta\Newman_Safe.lean` |
| `OperatorKO7\Meta\NonlinearDirectBoundary.lean` |
| `OperatorKO7\Meta\NonlinearDominanceCriteria.lean` |
| `OperatorKO7\Meta\NonlinearDominanceWitnesses.lean` |
| `OperatorKO7\Meta\NonlinearMethodLawCarrier.lean` |
| `OperatorKO7\Meta\NonlinearResidualTaxonomy.lean` |
| `OperatorKO7\Meta\NonlinearTransparentProjection.lean` |
| `OperatorKO7\Meta\NonlinearUnconstrainedSplit.lean` |
| `OperatorKO7\Meta\Normalize_Safe.lean` |
| `OperatorKO7\Meta\NormalizeSafe_LowerBound.lean` |
| `OperatorKO7\Meta\ObjectAxiom_Ablation.lean` |
| `OperatorKO7\Meta\OrdinalHierarchy.lean` |
| `OperatorKO7\Meta\OrdinalHierarchy_Control.lean` |
| `OperatorKO7\Meta\OrdinalHierarchy_Controlled.lean` |
| `OperatorKO7\Meta\PayloadExposureMatrix.lean` |
| `OperatorKO7\Meta\PolyInterpretation_FullStep.lean` |
| `OperatorKO7\Meta\PolynomialBarrierGeneral.lean` |
| `OperatorKO7\Meta\PolynomialBarrierGeneral_Schema.lean` |
| `OperatorKO7\Meta\PrecedenceBarrier.lean` |
| `OperatorKO7\Meta\ProjectedPrimaryBarrier.lean` |
| `OperatorKO7\Meta\PumpedBarrierClasses.lean` |
| `OperatorKO7\Meta\PumpedBarrierClasses_Schema.lean` |
| `OperatorKO7\Meta\QuadraticBarrier.lean` |
| `OperatorKO7\Meta\QuadraticBarrier_Schema.lean` |
| `OperatorKO7\Meta\QuadraticCrossTermBarrier.lean` |
| `OperatorKO7\Meta\QuadraticCrossTermBarrier_Schema.lean` |
| `OperatorKO7\Meta\RDRSBoundaryBottleneck.lean` |
| `OperatorKO7\Meta\RDRSDescentLens.lean` |
| `OperatorKO7\Meta\RDRSMethodCertificate.lean` |
| `OperatorKO7\Meta\RDRSNonKO7Instances.lean` |
| `OperatorKO7\Meta\RDRSProjectionSyntax.lean` |
| `OperatorKO7\Meta\RDRSProjectionTransaction.lean` |
| `OperatorKO7\Meta\RDRSRawDirectMeasure.lean` |
| `OperatorKO7\Meta\RDRSRetainedCoordinate.lean` |
| `OperatorKO7\Meta\RDRSSearchBudgetInvariance.lean` |
| `OperatorKO7\Meta\RDRSSeedCollapse.lean` |
| `OperatorKO7\Meta\RDRSSemanticCertificate.lean` |
| `OperatorKO7\Meta\RDRSSemanticDirectMeasure.lean` |
| `OperatorKO7\Meta\RDRSSemanticLensPump.lean` |
| `OperatorKO7\Meta\RDRSSemanticPayloadSensitivity.lean` |
| `OperatorKO7\Meta\RDRSSemanticProjectionTransaction.lean` |
| `OperatorKO7\Meta\RDRSSemanticProjectionTransactionAudit.lean` |
| `OperatorKO7\Meta\RDRSSemanticRawUniversalAdjudication.lean` |
| `OperatorKO7\Meta\RDRSWitnessTransport.lean` |
| `OperatorKO7\Meta\Reachability_Complexity.lean` |
| `OperatorKO7\Meta\RecCore.lean` |
| `OperatorKO7\Meta\RecursiveFamilyEscapeCharacterization.lean` |
| `OperatorKO7\Meta\RightDuplicatingRecursorSchema.lean` |
| `OperatorKO7\Meta\SafeRoot_Complexity.lean` |
| `OperatorKO7\Meta\SafeStep.lean` |
| `OperatorKO7\Meta\SafeStep\SigmaFreeAlgebra.lean` |
| `OperatorKO7\Meta\SafeStep\SyntacticNonDerivability.lean` |
| `OperatorKO7\Meta\SafeStep_Complexity.lean` |
| `OperatorKO7\Meta\SafeStep_Complexity_FastGrowing.lean` |
| `OperatorKO7\Meta\SafeStep_Complexity_MW_Ctx.lean` |
| `OperatorKO7\Meta\SafeStep_Complexity_MW_CtxExact.lean` |
| `OperatorKO7\Meta\SafeStep_Complexity_MW_Root.lean` |
| `OperatorKO7\Meta\SafeStep_Complexity_Ordinal.lean` |
| `OperatorKO7\Meta\SafeStep_Core.lean` |
| `OperatorKO7\Meta\SafeStep_Ctx.lean` |
| `OperatorKO7\Meta\SafeStepCtx_Complexity_Cichon.lean` |
| `OperatorKO7\Meta\SafeStepCtx_Complexity_Exponential.lean` |
| `OperatorKO7\Meta\SafeStepCtx_Complexity_LowerBound.lean` |
| `OperatorKO7\Meta\SafeStepCtx_Confluence.lean` |
| `OperatorKO7\Meta\ScalarProjectionBarrier.lean` |
| `OperatorKO7\Meta\SemanticMethodBoundary.lean` |
| `OperatorKO7\Meta\SharingBarrierLift.lean` |
| `OperatorKO7\Meta\StandardPumpLemmas.lean` |
| `OperatorKO7\Meta\StepDuplicatingSchema.lean` |
| `OperatorKO7\Meta\SymbolicComparatorBarrier.lean` |
| `OperatorKO7\Meta\SymbolicComparatorBarrier_Schema.lean` |
| `OperatorKO7\Meta\TextbookDupInstance.lean` |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage.lean` |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_Status.lean` |
| `OperatorKO7\Meta\TPDB_Export.lean` |
| `OperatorKO7\Meta\TransformedCallClassification.lean` |
| `OperatorKO7\Meta\TropicalBarrier.lean` |
| `OperatorKO7\Meta\TropicalBarrier_Schema.lean` |
| `OperatorKO7\Meta\TTT2_CertificateReplay.lean` |
| `OperatorKO7\Meta\TupleDecomposition.lean` |
| `OperatorKO7\Meta\TypedBarrierSurvival.lean` |
| `OperatorKO7\Meta\UniversalFirstOrderEmbeddings.lean` |
| `OperatorKO7\Meta\UniversalFirstOrderInterpretationMethod.lean` |
| `OperatorKO7\Meta\WitnessOrder.lean` |
| `OperatorKO7\Meta\WPO_PolynomialBarrier.lean` |
| `OperatorKO7\Meta\WPO_PolynomialBarrier_Schema.lean` |
| `OperatorKO7\PrimitiveSchemaAPI.lean` |
| `OperatorKO7\SchemaAPI.lean` |
| `OperatorKO7\SchemaExtendedAPI.lean` |
| `OperatorKO7\Test\CanonicalWitnessUniversalityReach.lean` |
| `OperatorKO7\Test\ConstructionMethodClassificationReach.lean` |
| `OperatorKO7\Test\ContextSCCTransportReach.lean` |
| `OperatorKO7\Test\DirectBarrierScopeReach.lean` |
| `OperatorKO7\Test\DirectWholeTermObserverReach.lean` |
| `OperatorKO7\Test\DMOrderTypeLowerBoundReach.lean` |
| `OperatorKO7\Test\DMTripleLexExactnessFinalCatalogReach.lean` |
| `OperatorKO7\Test\DMTripleLexExactnessReach.lean` |
| `OperatorKO7\Test\DMTripleLexImageReach.lean` |
| `OperatorKO7\Test\DMUpstreamSurfaceReach.lean` |
| `OperatorKO7\Test\DPSubtermCriterionExactReach.lean` |
| `OperatorKO7\Test\EscapeRouteCharacterizationReach.lean` |
| `OperatorKO7\Test\HigherOrderRewritingBetaBinderReach.lean` |
| `OperatorKO7\Test\HigherOrderRewritingBoundaryReach.lean` |
| `OperatorKO7\Test\HigherOrderRewritingCaptureSubfamiliesReach.lean` |
| `OperatorKO7\Test\HigherOrderSharingBoundaryReach.lean` |
| `OperatorKO7\Test\MatrixBarrierArbitraryInstancesReach.lean` |
| `OperatorKO7\Test\MatrixBarrierArbitraryReach.lean` |
| `OperatorKO7\Test\MatrixBarrierArcticTropicalInstancesReach.lean` |
| `OperatorKO7\Test\MatrixBarrierArcticTropicalReach.lean` |
| `OperatorKO7\Test\MatrixOrderInterfacesReach.lean` |
| `OperatorKO7\Test\MatrixUnrestrictedSplitReach.lean` |
| `OperatorKO7\Test\MutualDuplicationSchemaProjectionReach.lean` |
| `OperatorKO7\Test\MutualDuplicationSchemaReach.lean` |
| `OperatorKO7\Test\NonlinearDirectBoundaryReach.lean` |
| `OperatorKO7\Test\NonlinearDominanceCriteriaReach.lean` |
| `OperatorKO7\Test\NonlinearMethodLawCarrierReach.lean` |
| `OperatorKO7\Test\NonlinearTransparentProjectionReach.lean` |
| `OperatorKO7\Test\NonlinearUnconstrainedSplitReach.lean` |
| `OperatorKO7\Test\PhaseCVectorMatrixTupleReach.lean` |
| `OperatorKO7\Test\PrimitiveSchemaAPIReach.lean` |
| `OperatorKO7\Test\RDRSDescentLensAndProjectionReach.lean` |
| `OperatorKO7\Test\RDRSNonKO7InstancesReach.lean` |
| `OperatorKO7\Test\RDRSSemanticProjectionTransactionAuditReach.lean` |
| `OperatorKO7\Test\RDRSSemanticProjectionTransactionReach.lean` |
| `OperatorKO7\Test\RecursiveFamilyBoundaryReach.lean` |
| `OperatorKO7\Test\SafeStepAggregatorReach.lean` |
| `OperatorKO7\Test\SafeStepSyntacticNonDerivabilityReach.lean` |
| `OperatorKO7\Test\SchemaAPIReach.lean` |
| `OperatorKO7\Test\SchemaExtendedAPIReach.lean` |
| `OperatorKO7\Test\TPDB_Export.lean` |
| `OperatorKO7\Test\TransformedCallClassificationReach.lean` |

## Operational Inexpressibility Lean Files

| Path |
|---|
| `OperatorKO7\Meta\ArtsGiesl_DerivationalComplexity.lean` |
| `OperatorKO7\Meta\ArtsGiesl_LowerBound.lean` |
| `OperatorKO7\Meta\ArtsGiesl_ReverseMathCalibration.lean` |
| `OperatorKO7\Meta\ArtsGiesl_UpperBound.lean` |
| `OperatorKO7\Meta\ArtsGieslExactCalibrationUniversal.lean` |
| `OperatorKO7\Meta\BenchmarkedPrimitiveRecursionFamily.lean` |
| `OperatorKO7\Meta\ClassicalAscentProfile.lean` |
| `OperatorKO7\Meta\ComputationalLayerCrossing.lean` |
| `OperatorKO7\Meta\ConfessionMethod.lean` |
| `OperatorKO7\Meta\ConfessionMethod_ArgumentFiltering.lean` |
| `OperatorKO7\Meta\ConfessionMethod_CounterProjection.lean` |
| `OperatorKO7\Meta\ConfessionMethod_DP.lean` |
| `OperatorKO7\Meta\ConfessionMethod_Family.lean` |
| `OperatorKO7\Meta\ConfessionMethod_RouteEvidence.lean` |
| `OperatorKO7\Meta\ConfessionMethod_SCT.lean` |
| `OperatorKO7\Meta\ConfessionMethod_Unification.lean` |
| `OperatorKO7\Meta\FreeStepDuplicatingSyntax.lean` |
| `OperatorKO7\Meta\FreeStepDuplicatingTraceBridge.lean` |
| `OperatorKO7\Meta\GenericConfessionMove.lean` |
| `OperatorKO7\Meta\InformationAccess.lean` |
| `OperatorKO7\Meta\InformationTheoreticConfession.lean` |
| `OperatorKO7\Meta\LawvereYanofskySeparation.lean` |
| `OperatorKO7\Meta\LCELAdmissibilityData.lean` |
| `OperatorKO7\Meta\LCELBenchmarkDpComparison.lean` |
| `OperatorKO7\Meta\LCELBenchmarkDpUnrestrictedTheorem.lean` |
| `OperatorKO7\Meta\LCELDpInstance.lean` |
| `OperatorKO7\Meta\LCELGenericTransportBridge.lean` |
| `OperatorKO7\Meta\LCELLiteralSubstrate.lean` |
| `OperatorKO7\Meta\LCELMathematicalStructuralIdentity.lean` |
| `OperatorKO7\Meta\LCELMathematicalSupportWitness.lean` |
| `OperatorKO7\Meta\LCELReversibility.lean` |
| `OperatorKO7\Meta\LCELReversibilityUnconditional.lean` |
| `OperatorKO7\Meta\LCELRouteSemanticsClassification.lean` |
| `OperatorKO7\Meta\LCELSchema.lean` |
| `OperatorKO7\Meta\LCELSemanticCorrespondence.lean` |
| `OperatorKO7\Meta\LCELStructuralIdentity.lean` |
| `OperatorKO7\Meta\LCELSubstrateMathematics.lean` |
| `OperatorKO7\Meta\LCELTypedSigmaGamma.lean` |
| `OperatorKO7\Meta\LCELUniversalTheorem.lean` |
| `OperatorKO7\Meta\LCELUnrestrictedClassification.lean` |
| `OperatorKO7\Meta\LCELUnrestrictedExistence.lean` |
| `OperatorKO7\Meta\LCELUnrestrictedTheorem.lean` |
| `OperatorKO7\Meta\LCELWitnessFreeStructuralIdentity.lean` |
| `OperatorKO7\Meta\OperationalIncompleteness.lean` |
| `OperatorKO7\Meta\ProjectionAsConservativeExtension.lean` |
| `OperatorKO7\Meta\ProjectionTransactionDynamics.lean` |
| `OperatorKO7\Meta\ProofTheoreticRegister.lean` |
| `OperatorKO7\Meta\Recursor\CircularIdentity.lean` |
| `OperatorKO7\Meta\Recursor\DPConfessionLicense.lean` |
| `OperatorKO7\Meta\Recursor\DPConfessionLicenseUnconditional.lean` |
| `OperatorKO7\Meta\Recursor\InformationEquivalence.lean` |
| `OperatorKO7\Meta\Recursor\PayloadGrowthBlindness.lean` |
| `OperatorKO7\Meta\Recursor\RecursorFreeAlgebra.lean` |
| `OperatorKO7\Meta\ReflectionSchema.lean` |
| `OperatorKO7\Meta\ReverseMathFramework.lean` |
| `OperatorKO7\Meta\ReverseMathSupport.lean` |
| `OperatorKO7\Meta\SafeStep\EqWVoidAnomaly.lean` |
| `OperatorKO7\Meta\SafeStep\SmugglingUndecidability.lean` |
| `OperatorKO7\Meta\SchemaCanonicalTrace.lean` |
| `OperatorKO7\Meta\SchemaConfessionDominance.lean` |
| `OperatorKO7\Meta\SchemaForgettingWitness.lean` |
| `OperatorKO7\Meta\SchemaNormMismatch.lean` |
| `OperatorKO7\Meta\SchemaOffsetAndWrapper.lean` |
| `OperatorKO7\Meta\SchemaOperationalIncompleteness.lean` |
| `OperatorKO7\Meta\SchemaSeedCarrierFactorization.lean` |
| `OperatorKO7\Meta\SchemaWitnessOrder.lean` |
| `OperatorKO7\Meta\StructuralIdentityComparison.lean` |
| `OperatorKO7\Meta\TerminationPrincipleRegister.lean` |
| `OperatorKO7\Meta\UniversalFirstOrderDichotomy.lean` |
| `OperatorKO7\Test\ArtsGieslDerivationalReach.lean` |
| `OperatorKO7\Test\ArtsGieslExactCalibrationUniversalReach.lean` |
| `OperatorKO7\Test\ArtsGieslReverseMathCalibrationReach.lean` |
| `OperatorKO7\Test\InformationTheoreticConfessionReach.lean` |
| `OperatorKO7\Test\LCELBenchmarkDpComparison.lean` |
| `OperatorKO7\Test\LCELBenchmarkDpUnrestrictedTheorem.lean` |
| `OperatorKO7\Test\LCELDpInstanceReach.lean` |
| `OperatorKO7\Test\LCELGenericTransportBridgeReach.lean` |
| `OperatorKO7\Test\LCELLiteralSubstrateReach.lean` |
| `OperatorKO7\Test\LCELMathematicalStructuralIdentity.lean` |
| `OperatorKO7\Test\LCELMathematicalSupportWitness.lean` |
| `OperatorKO7\Test\LCELReversibilitySupport.lean` |
| `OperatorKO7\Test\LCELReversibilityUnconditionalReach.lean` |
| `OperatorKO7\Test\LCELSemanticCorrespondence.lean` |
| `OperatorKO7\Test\LCELSubstrateMathematics.lean` |
| `OperatorKO7\Test\LCELTypedSigmaGammaReach.lean` |
| `OperatorKO7\Test\LCELUniversalTheorem.lean` |
| `OperatorKO7\Test\LCELUnrestrictedTheorem.lean` |
| `OperatorKO7\Test\LCELWitnessFreeStructuralIdentity.lean` |
| `OperatorKO7\Test\RecursorCircularIdentityReach.lean` |
| `OperatorKO7\Test\RecursorDPConfessionLicenseReach.lean` |
| `OperatorKO7\Test\RecursorFreeAlgebraReach.lean` |
| `OperatorKO7\Test\RecursorInformationEquivalenceReach.lean` |
| `OperatorKO7\Test\RecursorPayloadGrowthBlindnessReach.lean` |
| `OperatorKO7\Test\SafeStepEqWVoidAnomalyReach.lean` |
| `OperatorKO7\Test\SafeStepSmugglingUndecidabilityReach.lean` |
| `OperatorKO7\Test\SchemaLCELRoadmapCloseoutReach.lean` |

## Confluence-Preservation Boundary (Paper C) Lean Files

These are the public theorem surfaces for *The Confluence-Preservation Boundary for Diagonal Identity Queries*: the generic first-order rewriting and Critical Pair Lemma library (`Meta\Rewriting`), the KO7 equality-witness diagonal fork with its global-confluence and guarded-repair results (`Meta\DistinctionBoundary`, `Meta\SafeStep`), the informational-incompleteness and Landauer readings of the fork (`Meta\InformationalIncompleteness`, `Meta\Physics`), and the reverse-mathematics strength calibration (`Meta\ReverseMath`). The engine-coupled modules of this paper are listed separately under reviewer NDA below.

| Path |
|---|
| `OperatorKO7\Meta\BoundaryGeneral\DiagonalMirror.lean` |
| `OperatorKO7\Meta\BoundaryGeneral\DistinctionRecord.lean` |
| `OperatorKO7\Meta\BoundaryOperator.lean` |
| `OperatorKO7\Meta\ComparatorNecessity.lean` |
| `OperatorKO7\Meta\ComparatorNecessityPartial.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\CriticalPairCompleteness.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\CriticalPairLemmaKO7.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\GlobalConfluence.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\RepairRoutes.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ArchitecturalOrigin.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\AxisGrowthSeparation.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\CarrierBurden.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\CertFragmentWitness.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\CertificateInterface.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ComparisonAsymmetry.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ConditionalEntropy.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\DiagonalEntropy.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\DiagonalInert.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\EqWDiagonalDeficit.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\GradedDeficit.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\LicensedChannelDeficit.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\LicensedCollapseDeficit.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\MemoryDistinction.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ParticipatoryQuery.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\PropagationResidual.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\QueryInterface.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ShannonFinite.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\WitnessChannelBoundary.lean` |
| `OperatorKO7\Meta\Physics\ConfessionLandauerExact.lean` |
| `OperatorKO7\Meta\Physics\ConfessionLandauerSplit.lean` |
| `OperatorKO7\Meta\Physics\LandauerErasureFinite.lean` |
| `OperatorKO7\Meta\Physics\LandauerHeatBound.lean` |
| `OperatorKO7\Meta\Physics\RecordFormation.lean` |
| `OperatorKO7\Meta\QuantumBoundary\CategoricalLandauer.lean` |
| `OperatorKO7\Meta\RepShift_BottleneckPredicate.lean` |
| `OperatorKO7\Meta\RepShift_LayeredSemanticsTower.lean` |
| `OperatorKO7\Meta\ReverseMath\Complexity.lean` |
| `OperatorKO7\Meta\ReverseMath\ConfluenceOrderType.lean` |
| `OperatorKO7\Meta\ReverseMath\Language.lean` |
| `OperatorKO7\Meta\ReverseMath\NewmanComplexity.lean` |
| `OperatorKO7\Meta\ReverseMath\NewmanRCA0Upper.lean` |
| `OperatorKO7\Meta\ReverseMath\RCA0.lean` |
| `OperatorKO7\Meta\ReverseMath\StandardModel.lean` |
| `OperatorKO7\Meta\Rewriting\Commutation.lean` |
| `OperatorKO7\Meta\Rewriting\ConfluenceDecision.lean` |
| `OperatorKO7\Meta\Rewriting\CriticalPair.lean` |
| `OperatorKO7\Meta\Rewriting\CriticalPairComplete.lean` |
| `OperatorKO7\Meta\Rewriting\CriticalPairLemma.lean` |
| `OperatorKO7\Meta\Rewriting\Match.lean` |
| `OperatorKO7\Meta\Rewriting\Orthogonality.lean` |
| `OperatorKO7\Meta\Rewriting\ParallelReduction.lean` |
| `OperatorKO7\Meta\Rewriting\ParallelReductionConfluence.lean` |
| `OperatorKO7\Meta\Rewriting\ParallelReductionDiamond.lean` |
| `OperatorKO7\Meta\Rewriting\Position.lean` |
| `OperatorKO7\Meta\Rewriting\Reach.lean` |
| `OperatorKO7\Meta\Rewriting\Rewrite.lean` |
| `OperatorKO7\Meta\Rewriting\Subst.lean` |
| `OperatorKO7\Meta\Rewriting\Term.lean` |
| `OperatorKO7\Meta\Rewriting\TerminationCriterion.lean` |
| `OperatorKO7\Meta\Rewriting\Unify.lean` |
| `OperatorKO7\Meta\Rewriting\UnifyCorrect.lean` |
| `OperatorKO7\Meta\SafeStep\BoundaryBundle.lean` |
| `OperatorKO7\Meta\SafeStep\BoundaryDuality.lean` |
| `OperatorKO7\Meta\SafeStep\BranchEntropy.lean` |
| `OperatorKO7\Meta\SafeStep\BranchEntropyGeneral.lean` |
| `OperatorKO7\Meta\SafeStep\DiagonalForkClassicInstance.lean` |
| `OperatorKO7\Meta\SafeStep\DistinctionControls.lean` |
| `OperatorKO7\Meta\SafeStep\DistinctionWitnessBoundary.lean` |
| `OperatorKO7\Meta\SafeStep\DynamicalBoundaryFunctor.lean` |
| `OperatorKO7\Meta\SafeStep\FaithfulnessNoGo.lean` |
| `OperatorKO7\Meta\SafeStep\GenericDiagonalFork.lean` |
| `OperatorKO7\Meta\SafeStep\NonlinearityDichotomy.lean` |
| `OperatorKO7\Meta\SafeStep\SafeStepInterpreter.lean` |

## Shared Lean Infrastructure

| Path |
|---|
| `lakefile.lean` |
| `OperatorKO7.lean` |
| `OperatorKO7\CrossPaperAPI.lean` |
| `OperatorKO7\Test\CrossPaperAPIReach.lean` |
| `OperatorKO7\Test\Sanity.lean` |
| `OperatorKO7\Test\TopLevelImportReach.lean` |

## External Proof Artifacts

| Path |
|---|
| `Artifacts\ttt2\README.md` |
| `Artifacts\ttt2\KO7_full_step.trs` |
| `Artifacts\ttt2\KO7_full_step_TTT2_results_FAST.txt` |
| `Artifacts\ttt2\KO7_full_step_TTT2_results_POLY.txt` |
| `Artifacts\ttt2\KO7_CeTA_certification.txt` |
| `Artifacts\ttt2\KO7_FAST.cpf` |
| `Artifacts\ttt2\KO7_COMP.cpf` |
| `Artifacts\ttt2\KO7_KBO.cpf` |
| `Artifacts\ttt2\KO7_LPO.cpf` |
| `Artifacts\ttt2\KO7_MAT2.cpf` |
| `Artifacts\ttt2\KO7_MAT3.cpf` |
| `Artifacts\ttt2\KO7_POLY.cpf` |

## Reviewer NDA Lean Files

The following Lean files are handled through reviewer NDA access. These are the runtime-consumed engine surface (classifier, oracle, coverage-ledger, audit, route-ledger, universal-API, plug-intake, certificate-replay bridge, tool-search mapping, P4C closeout cluster, FBI-method carrier, W1/W2 method carrier, higher-order policy-audit cluster, mutual-duplication algorithmic-search cluster, SafeTrace audit-log bridge cluster), released to qualified reviewers on request.

### Paper A Reviewer NDA Files

| Path |
|---|
| `OperatorKO7\Meta\BarrierClass_Classifier.lean` |
| `OperatorKO7\Meta\BarrierWitness_Budgets.lean` |
| `OperatorKO7\Meta\BarrierWitness_Extended.lean` |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Audit.lean` |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Exactness.lean` |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Partition.lean` |
| `OperatorKO7\Meta\FBI_AdequacyBoundary.lean` |
| `OperatorKO7\Meta\FBI_Classification.lean` |
| `OperatorKO7\Meta\FBI_FinalCatalog.lean` |
| `OperatorKO7\Meta\FBI_GenericAdequacy.lean` |
| `OperatorKO7\Meta\FBI_Method.lean` |
| `OperatorKO7\Meta\GenericDPGrammar.lean` |
| `OperatorKO7\Meta\GenericDPMethodBoundary.lean` |
| `OperatorKO7\Meta\HigherOrderRewriting_CaptureDecidable.lean` |
| `OperatorKO7\Meta\HigherOrderRewriting_Closeout.lean` |
| `OperatorKO7\Meta\HigherOrderRewriting_DecidableClassifiers.lean` |
| `OperatorKO7\Meta\HigherOrderRewriting_FinalCatalog.lean` |
| `OperatorKO7\Meta\HigherOrderRewriting_FullCaptureBoundary.lean` |
| `OperatorKO7\Meta\HigherOrderRewriting_PolicyAudit.lean` |
| `OperatorKO7\Meta\HigherOrderSharingBoundary_API.lean` |
| `OperatorKO7\Meta\MatrixProjectionCoverage.lean` |
| `OperatorKO7\Meta\MatrixProjectionCoverage_Schema.lean` |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_AlgorithmicSearch.lean` |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_AlgorithmicSearch_FinalCatalog.lean` |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_API.lean` |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_Builder.lean` |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_BuilderMapping.lean` |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_Closeout.lean` |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_FinalCatalog.lean` |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_GraphSearch.lean` |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_Instances.lean` |
| `OperatorKO7\Meta\RDRSAlgebraicInterpretationAtlas.lean` |
| `OperatorKO7\Meta\RDRSConditionalTypedAtlas.lean` |
| `OperatorKO7\Meta\RDRSCoverageLedger.lean` |
| `OperatorKO7\Meta\RDRSCoverageLedgerSeed.lean` |
| `OperatorKO7\Meta\RDRSDPProcessorClassification.lean` |
| `OperatorKO7\Meta\RDRSMethodCertificateClassifier.lean` |
| `OperatorKO7\Meta\RDRSNoBarrierZones.lean` |
| `OperatorKO7\Meta\RDRSNonConservativeEscapeAtlas.lean` |
| `OperatorKO7\Meta\RDRSNotesReconciliationAddendum.lean` |
| `OperatorKO7\Meta\RDRSPathOrderDichotomy.lean` |
| `OperatorKO7\Meta\RDRSSemanticClassifier.lean` |
| `OperatorKO7\Meta\RDRSSemanticCounterexampleAudit.lean` |
| `OperatorKO7\Meta\RDRSSemanticCoverageLedger.lean` |
| `OperatorKO7\Meta\RDRSSemanticStructuralAtlas.lean` |
| `OperatorKO7\Meta\RDRSTerminationMethodAtlas.lean` |
| `OperatorKO7\Meta\RDRSTerminationMethodUniverse.lean` |
| `OperatorKO7\Meta\RDRSTerminationMethodUniverseCloseout.lean` |
| `OperatorKO7\Meta\RDRSUniversalPayloadSensitiveBarrier.lean` |
| `OperatorKO7\Meta\RecursiveFamilyBoundaryCloseoutCatalog.lean` |
| `OperatorKO7\Meta\RecursiveFamilyTypedPolicyRows.lean` |
| `OperatorKO7\Meta\ResidualMethodClosureCatalog.lean` |
| `OperatorKO7\Meta\SafeTrace_CertificateAudit.lean` |
| `OperatorKO7\Meta\SafeTrace_CertificateBridge.lean` |
| `OperatorKO7\Meta\SafeTrace_ComplexityBridge.lean` |
| `OperatorKO7\Meta\SafeTrace_RoadmapCloseout.lean` |
| `OperatorKO7\Meta\SafeTrace_TripleLexExactness.lean` |
| `OperatorKO7\Meta\SafeTrace_TripleLexExactness_FinalCatalog.lean` |
| `OperatorKO7\Meta\SemanticMethodGrammar.lean` |
| `OperatorKO7\Meta\SynthesisOracle.lean` |
| `OperatorKO7\Meta\TheoryExpansionCloseoutSurface.lean` |
| `OperatorKO7\Meta\TheoryExpansionReleaseAudit.lean` |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_Exactness.lean` |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_FinalCatalog.lean` |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_ListAudit.lean` |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_PerFamily.lean` |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_ResidualBoundary.lean` |
| `OperatorKO7\Meta\W1AscentStructuralIdentity.lean` |
| `OperatorKO7\Meta\W1MethodCarrier.lean` |
| `OperatorKO7\OrientationBoundaryAPI.lean` |
| `OperatorKO7\ResidualMethodAPI.lean` |
| `OperatorKO7\Test\ConstructionRouteCatalogCertificateReach.lean` |
| `OperatorKO7\Test\ConstructionRouteCatalogExactnessReach.lean` |
| `OperatorKO7\Test\ConstructionRouteCatalogFinalReach.lean` |
| `OperatorKO7\Test\ConstructionRouteCatalogPayloadReach.lean` |
| `OperatorKO7\Test\ConstructionRouteCatalogReach.lean` |
| `OperatorKO7\Test\DirectToolSearchMappingReach.lean` |
| `OperatorKO7\Test\ExtendedDirectToolSearchMappingReach.lean` |
| `OperatorKO7\Test\FBIAdequacyBoundaryReach.lean` |
| `OperatorKO7\Test\FBIClassificationReach.lean` |
| `OperatorKO7\Test\FBIFinalCatalogReach.lean` |
| `OperatorKO7\Test\FBIFinalCatalogRootReach.lean` |
| `OperatorKO7\Test\FBIGenericAdequacyReach.lean` |
| `OperatorKO7\Test\GenericDPSemanticBoundaryReach.lean` |
| `OperatorKO7\Test\GenericDPSemanticGrammarReach.lean` |
| `OperatorKO7\Test\HigherOrderRewritingCaptureDecidableReach.lean` |
| `OperatorKO7\Test\HigherOrderRewritingCloseoutReach.lean` |
| `OperatorKO7\Test\HigherOrderRewritingDecidableClassifiersReach.lean` |
| `OperatorKO7\Test\HigherOrderRewritingFinalCatalogReach.lean` |
| `OperatorKO7\Test\HigherOrderRewritingFullCaptureBoundaryReach.lean` |
| `OperatorKO7\Test\HigherOrderRewritingPolicyAuditReach.lean` |
| `OperatorKO7\Test\HigherOrderSharingBoundaryAPIReach.lean` |
| `OperatorKO7\Test\HigherOrderSharingBoundaryFinalCatalogReach.lean` |
| `OperatorKO7\Test\MatrixResidualClosureCatalogReach.lean` |
| `OperatorKO7\Test\MatrixResidualTaxonomyReach.lean` |
| `OperatorKO7\Test\MatrixToolSearchMappingReach.lean` |
| `OperatorKO7\Test\MutualDuplicationFiniteSchemaAlgorithmicSearchFinalCatalogReach.lean` |
| `OperatorKO7\Test\MutualDuplicationFiniteSchemaAlgorithmicSearchReach.lean` |
| `OperatorKO7\Test\MutualDuplicationFiniteSchemaAPIReach.lean` |
| `OperatorKO7\Test\MutualDuplicationFiniteSchemaBuilderMappingReach.lean` |
| `OperatorKO7\Test\MutualDuplicationFiniteSchemaBuilderReach.lean` |
| `OperatorKO7\Test\MutualDuplicationFiniteSchemaCloseoutReach.lean` |
| `OperatorKO7\Test\MutualDuplicationFiniteSchemaFinalCatalogReach.lean` |
| `OperatorKO7\Test\MutualDuplicationFiniteSchemaGraphSearchReach.lean` |
| `OperatorKO7\Test\MutualDuplicationFiniteSchemaInstancesReach.lean` |
| `OperatorKO7\Test\MutualDuplicationFiniteSchemaReach.lean` |
| `OperatorKO7\Test\OrientationBoundaryAPIReach.lean` |
| `OperatorKO7\Test\RDRSAlgebraicInterpretationAtlasReach.lean` |
| `OperatorKO7\Test\RDRSConditionalTypedAtlasReach.lean` |
| `OperatorKO7\Test\RDRSCoverageLedgerAxiomCheck.lean` |
| `OperatorKO7\Test\RDRSCoverageLedgerSeedReach.lean` |
| `OperatorKO7\Test\RDRSDPProcessorClassificationReach.lean` |
| `OperatorKO7\Test\RDRSNoBarrierZonesReach.lean` |
| `OperatorKO7\Test\RDRSNonConservativeEscapeAtlasReach.lean` |
| `OperatorKO7\Test\RDRSNotesReconciliationAddendumReach.lean` |
| `OperatorKO7\Test\RDRSPathOrderDichotomyReach.lean` |
| `OperatorKO7\Test\RDRSSemanticStructuralAtlasReach.lean` |
| `OperatorKO7\Test\RDRSTerminationMethodAtlasReach.lean` |
| `OperatorKO7\Test\RDRSTerminationMethodUniverseCloseoutReach.lean` |
| `OperatorKO7\Test\RDRSUniversalPayloadSensitiveBarrierReach.lean` |
| `OperatorKO7\Test\RecursiveFamilyBoundaryCloseoutCatalogReach.lean` |
| `OperatorKO7\Test\RecursiveFamilyTypedPolicyRowsReach.lean` |
| `OperatorKO7\Test\ResidualMethodAPIReach.lean` |
| `OperatorKO7\Test\ResidualMethodClosureCatalogReach.lean` |
| `OperatorKO7\Test\SafeTraceCertificateAuditReach.lean` |
| `OperatorKO7\Test\SafeTraceCertificateBridgeReach.lean` |
| `OperatorKO7\Test\SafeTraceComplexityBridgeReach.lean` |
| `OperatorKO7\Test\SafeTraceRoadmapCloseoutReach.lean` |
| `OperatorKO7\Test\SafeTraceSurjectivityReach.lean` |
| `OperatorKO7\Test\SafeTraceTripleLexExactnessFinalCatalogReach.lean` |
| `OperatorKO7\Test\SafeTraceTripleLexExactnessReach.lean` |
| `OperatorKO7\Test\TheoryExpansionCloseoutSurfaceReach.lean` |
| `OperatorKO7\Test\ToolSearchFragmentCoverageExactnessReach.lean` |
| `OperatorKO7\Test\ToolSearchFragmentCoverageFinalCatalogReach.lean` |
| `OperatorKO7\Test\ToolSearchFragmentCoverageListAuditReach.lean` |
| `OperatorKO7\Test\ToolSearchFragmentCoveragePerFamilyReach.lean` |
| `OperatorKO7\Test\ToolSearchFragmentCoverageReach.lean` |
| `OperatorKO7\Test\ToolSearchFragmentCoverageStatusReach.lean` |
| `OperatorKO7\Test\W1AscentStructuralIdentityReach.lean` |
| `OperatorKO7\Test\W1MethodCarrierReach.lean` |
| `VerifyTpdbExport.lean` |

### Operational Inexpressibility Reviewer NDA Files

| Path |
|---|
| `OperatorKO7\Meta\ConfessionMethod_FutureRouteSchema.lean` |
| `OperatorKO7\Meta\ConfessionMethod_OptimalityBoundary.lean` |
| `OperatorKO7\Meta\ConfessionMethod_UniversalAPI.lean` |
| `OperatorKO7\Meta\ConfessionMethod_UniversalInstances.lean` |
| `OperatorKO7\Meta\ConfessionMethod_UniversalRouteLedger.lean` |
| `OperatorKO7\Meta\ConfessionMethod_UniversalUsableRules.lean` |
| `OperatorKO7\Meta\ConfessionMethod_UsableRules.lean` |
| `OperatorKO7\Meta\ConfessionMethod_UsableRulesBridgeAttempt.lean` |
| `OperatorKO7\Meta\ConfessionMethod_UsableRulesConcrete.lean` |
| `OperatorKO7\Meta\ConfessionMethod_UsableRulesFinalStatus.lean` |
| `OperatorKO7\Meta\LCELP4CCanonicalInstances.lean` |
| `OperatorKO7\Meta\LCELP4CCloseout.lean` |
| `OperatorKO7\Meta\LCELP4CFinalStatus.lean` |
| `OperatorKO7\Meta\LCELP4CResidualObligation.lean` |
| `OperatorKO7\Meta\LCELP4CUniversalBlueprint.lean` |
| `OperatorKO7\Meta\LCELP4CUniversalCertification.lean` |
| `OperatorKO7\Meta\MetaHalt_Fracture.lean` |
| `OperatorKO7\Meta\MetaHalt_PaperInterface.lean` |
| `OperatorKO7\Meta\MetaHalt_Predicate.lean` |
| `OperatorKO7\Meta\MetaHalt_Regress.lean` |
| `OperatorKO7\Meta\MetaHalt_Signatures.lean` |
| `OperatorKO7\Meta\MetaHalt_Soundness.lean` |
| `OperatorKO7\Meta\RecordEmissionNecessity.lean` |
| `OperatorKO7\Meta\RecordEmissionNecessity_BeyondFirstOrder.lean` |
| `OperatorKO7\Meta\Recursor\TRSEquivalence.lean` |
| `OperatorKO7\Meta\W1W2UniversalNecessity.lean` |
| `OperatorKO7\Test\ConfessionMethodFutureRouteSchemaReach.lean` |
| `OperatorKO7\Test\ConfessionMethodOptimalityBoundaryReach.lean` |
| `OperatorKO7\Test\ConfessionMethodUniversalAPIReach.lean` |
| `OperatorKO7\Test\ConfessionMethodUniversalInstancesReach.lean` |
| `OperatorKO7\Test\ConfessionMethodUniversalRouteLedgerReach.lean` |
| `OperatorKO7\Test\ConfessionMethodUniversalUsableRulesReach.lean` |
| `OperatorKO7\Test\ConfessionMethodUsableRulesBridgeAttemptReach.lean` |
| `OperatorKO7\Test\ConfessionMethodUsableRulesFinalStatusReach.lean` |
| `OperatorKO7\Test\ConfessionMethodUsableRulesReach.lean` |
| `OperatorKO7\Test\GenericConfessionMoveReach.lean` |
| `OperatorKO7\Test\LCELP4CCanonicalInstancesReach.lean` |
| `OperatorKO7\Test\LCELP4CCloseoutReach.lean` |
| `OperatorKO7\Test\LCELP4CFinalStatusReach.lean` |
| `OperatorKO7\Test\LCELP4CResidualObligationReach.lean` |
| `OperatorKO7\Test\LCELP4CUniversalBlueprintReach.lean` |
| `OperatorKO7\Test\LCELP4CUniversalCertificationReach.lean` |
| `OperatorKO7\Test\LCELRoadmapFinalReach.lean` |
| `OperatorKO7\Test\LCELRouteSemanticsClassificationReach.lean` |
| `OperatorKO7\Test\MetaHalt.lean` |
| `OperatorKO7\Test\RecursorTRSEquivalenceReach.lean` |
| `OperatorKO7\Test\UniversalFirstOrderDichotomyReach.lean` |
| `OperatorKO7\Test\UsableRulesBridgeReach.lean` |

### Confluence-Preservation Boundary Reviewer NDA Files

These Confluence-Preservation Boundary modules reuse runtime-consumed engine surfaces (the META-HALT typed-output algebra, the confession-method universal-API instances, and the semantic method classifier) and are released to qualified reviewers under NDA alongside the public theorem surface above.

| Path |
|---|
| `OperatorKO7\Meta\BoundaryOperator\TypedRefusalCompleteness.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\Pillar.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\SharedRoot.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\CarrierCapacity.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ConfluenceForcedTrilemma.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ForcedTrilemma.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\LicensedFactorisation.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\RecursorPayloadErasure.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\SemanticWitnessBridge.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\SharpnessCounterexample.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\UnivDeficitViaChar.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\UniversalDeficit.lean` |
| `OperatorKO7\Meta\RDRSSemanticArbitraryClassifier.lean` |
| `OperatorKO7\Meta\RDRSSemanticNormalizedRawSyntax.lean` |
| `OperatorKO7\Meta\SafeStep\BranchTransaction.lean` |
| `OperatorKO7\Meta\SafeStep\DistinctionAscentProfile.lean` |
| `OperatorKO7\Meta\SafeStep\DistinctionInexpressible.lean` |
| `OperatorKO7\Meta\SafeStep\GaugeFixingGuard.lean` |
| `OperatorKO7\Meta\SafeStep\GuardNecessity.lean` |
| `OperatorKO7\Meta\SafeStep\RefusalLoad.lean` |
| `OperatorKO7\Test\DistinctionBoundaryPillarReach.lean` |
| `OperatorKO7\Test\DistinctionBoundaryReach.lean` |
| `OperatorKO7\Test\InformationalIncompletenessReach.lean` |

## Build Check

The public Lean package should be checked from the repository root with:

```bash
lake build OperatorKO7
```

## Reviewer Access

Reviewer NDA Lean files may be requested through the contact address listed in `README.md` and `CITATION.cff`.
