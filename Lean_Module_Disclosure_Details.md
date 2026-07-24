# Public Lean and Manuscript Release Note

**Date:** 2026-07-21

This repository is the public companion artifact for three manuscripts:

- *The Orientation Boundary for Step-Duplicating Recursors: Mechanized Impossibility, Escape, and Certification.*
- *Operational Inexpressibility at the Primitive-Recursion Orientation Boundary.*
- *The Confluence-Preservation Boundary for Diagonal Identity Queries: Non-Left-Linearity, Signature Inexpressibility, and External Guarding.*

The files below are included in this public Lean release for inspection of the theorem surfaces used by those three manuscripts. The first two papers trace the termination axis of the boundary; the third traces the confluence axis, contributing a generic first-order Critical Pair Lemma library, the equality-witness diagonal fork with its global-confluence, guarded-repair, SafeStep-maximality, finite-expansion, categorical wrapper, finite Cech obstruction, normalization-face, and reverse-mathematics results. For the Orientation Boundary paper, every file in the 380-file Lean closure is designated public and no NDA applies. NDA handling elsewhere in this document concerns only other manuscripts or product-facing engine material outside that closure.

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
| Orientation Boundary complete Lean closure | 380 (201 exact, 80 require synchronization, 99 pending transfer) |
| Operational Inexpressibility Lean files | 94 |
| Confluence-Preservation Boundary Lean files | 114 |
| Shared Lean infrastructure | 4 |
| External proof artifacts | 12 |
| Manuscript source snapshots | 3 |
| Direct Supervisory Engine Lean files withheld under NDA | 22 |
| Supervisory Engine import and bridge dependencies withheld under NDA | 3 |
| Orientation Boundary closure files under NDA | 0 |
| Reviewer NDA Lean files for Operational Inexpressibility | 29 |
| Reviewer NDA Lean files for Confluence-Preservation Boundary | 12 |

## Manuscript Sources

| Path |
|---|
| `Manuscripts\Orientation_Boundary\Rahnama_The_Orientation_Boundary.tex` |
| `Manuscripts\Orientation_Boundary\references.bib` |
| `Manuscripts\Operational_Inexpressibility\Rahnama_Operational_Inexpressibility.tex` |
| `Manuscripts\Operational_Inexpressibility\references.bib` |
| `Manuscripts\Distinction_Boundary\Rahnama_The_Distinction_Boundary.tex` |

## The Orientation Boundary (Paper A) Complete Lean Closure

> **Audit date:** 2026-07-21. The current manuscript names `270` Lean files directly. Its recursively resolved project-owned import closure contains `380` files. This table supersedes the former 215-file public list and the former Paper-A reviewer-NDA list.
>
> All `380` files are designated **public, no NDA**. `pending transfer` means the source is not yet in this repository; `synchronization required` means a public copy exists but differs from the authoritative source snapshot. No transfer or source synchronization was performed in this documentation-only pass.
>
> ```text
> [380 required] -> [201 exact | 80 sync | 99 transfer] -> [0 NDA]
> ```

| Path | Relationship to manuscript | Public repository | Source parity | NDA status |
|---|---|---|---|---|
| `OperatorKO7\CrossPaperAPI.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Kernel.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\AffineThresholdSharpness.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ArcticBarrier_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ArcticBarrier.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArtsGiesl_DerivationalComplexity.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArtsGiesl_LowerBound.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArtsGiesl_ReverseMathCalibration.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArtsGiesl_UpperBound.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\BarrierClass_Classifier.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\BarrierWitness_Budgets.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\BarrierWitness_Extended.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\BarrierWitness.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\BenchmarkedPrimitiveRecursionFamily.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\BoundaryFactorization.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\BoundaryGeneral\DirectMeasureGrammarClosure.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\CanonicalWitnessUniversality.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ClassicalAscentProfile.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\CompositionalMeasure_Impossibility.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ComputableMeasure.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ComputationalLayerCrossing.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_ArgumentFiltering.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_CounterProjection.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_DP.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_Family.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_FutureRouteSchema.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_OptimalityBoundary.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_RouteEvidence.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_SCT.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_Unification.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UniversalAPI.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UniversalInstances.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UniversalRouteLedger.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UniversalUsableRules.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UsableRules.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UsableRulesBridgeAttempt.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UsableRulesConcrete.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UsableRulesFinalStatus.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\Confluence_Safe.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\Conjecture_Boundary.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ConstructionMethodClassification.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Audit.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Certificate.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Exactness.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Partition.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Payload.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ContextClosed_SN_Full.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ContextClosed_SN.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ContextClosedBarrier.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ContextSCCTransport.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ContextualCopyBudget_NoGo.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ContextualCopyBudget.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_CallGraph.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_ExtractedCallGraph.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_FiniteCarrierView.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_FiniteGraph.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_FirstOrderEngine.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_FirstOrderExtraction.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_FirstOrderFrontend.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_Fragment.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_HeadView.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_KernelFirstOrder.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_TPDBExtraction.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_Works.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\DepthBarrier_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DepthBarrier.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\DirectBarrierScope.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\DirectToolSearchMapping.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DirectWholeTermObserver.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DM_OrderType_LowerBound.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DM_OrderType.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DM_TripleLexExactness_FinalCatalog.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DM_TripleLexExactness.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DM_TripleLexImage.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DM_UpstreamSurface.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DP_BaseOrder_Boundary.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\DPSubtermCriterionExact.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\DuplicatingRecursiveFamily.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\EqGuardedConfluence.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\EqW_Guard_Barrier.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\EscapeTrichotomy_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\EscapeTrichotomy.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ExtendedDirectToolSearchMapping.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ExternalizedTraceStorage.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\FBI_AdequacyBoundary.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\FBI_Classification.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\FBI_FinalCatalog.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\FBI_GenericAdequacy.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\FBI_Method.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\FiniteGraphReachability.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\FiniteGraphSCC.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\FreeStepDuplicatingSyntax.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\FreeStepDuplicatingTraceBridge.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\GenericConfessionMove.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\GenericDPMethodBoundary.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\GenericSupervisoryEngine.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\GraphPathExtraction.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\HigherOrderNoSharingBoundary.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_BetaBinder.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_Boundary.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_CaptureDecidable.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_CaptureSubfamilies.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_Closeout.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_DecidableClassifiers.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_FinalCatalog.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_FullCaptureBoundary.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_PolicyAudit.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_Syntax.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\HigherOrderSharingBoundary_API.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\HigherOrderSharingBoundary_FinalCatalog.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\HigherOrderSharingBoundary.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\Impossibility_Lemmas.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\InformationAccess.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\InformationTheoreticConfession.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\KBO_Impossible_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\KBO_Impossible.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\KO7EscapeRouteCharacterization.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\KO7RDRSAdapter.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\LawvereYanofskySeparation.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELAdmissibilityData.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\LCELBenchmarkDpComparison.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\LCELBenchmarkDpUnrestrictedTheorem.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\LCELDpInstance.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\LCELGenericTransportBridge.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\LCELMathematicalStructuralIdentity.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELMathematicalSupportWitness.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELP4CCanonicalInstances.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\LCELP4CCloseout.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\LCELP4CFinalStatus.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\LCELP4CResidualObligation.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\LCELP4CUniversalBlueprint.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\LCELP4CUniversalCertification.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\LCELReversibility.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELRouteSemanticsClassification.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\LCELSchema.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELSemanticCorrespondence.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELStructuralIdentity.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\LCELSubstrateMathematics.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELTypedSigmaGamma.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELUniversalTheorem.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELUnrestrictedClassification.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELUnrestrictedExistence.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\LCELUnrestrictedTheorem.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELWitnessFreeStructuralIdentity.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\LinearRec_Ablation.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\ManySortedBarrierSurvival.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrier2_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrier2.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArbitrary_Instances.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArbitrary_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArbitrary.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArcticTropical_Instances.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArcticTropical_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArcticTropical.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierD_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierD.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierFunctional_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierFunctional.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLex_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLex.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLexD_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLexD.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLexPermD_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLexPermD.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierMix2_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierMix2.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixOrderInterfaces.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixOverPolynomialReduction.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixProjectionCoverage_Schema.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MatrixProjectionCoverage.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MatrixResidualClosureCatalog.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixResidualTaxonomy.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixToolSearchMapping.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MatrixUnrestrictedSplit.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MaxBarrier_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MaxBarrier.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MetaHalt_Predicate.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MetaHalt_Regress.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MetaHalt_Signatures.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MPO_FullStep.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MPO_Precedence_Barrier.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MPO_ProofTheoreticBound.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\Mu3c_Image_LowerBound.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MultilinearBarrier_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MultilinearBarrier.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_CallGraph.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Case.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_CycleFlow.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_ExtractedCallGraph.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_AlgorithmicSearch_FinalCatalog.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_AlgorithmicSearch.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_API.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_Builder.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_BuilderMapping.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_Closeout.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_FinalCatalog.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_GraphSearch.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_Instances.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_General.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_GraphCycle.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_KNode_Abstract.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_KNode.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_PacketGraph.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_PayloadFlow.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Preserving_Abstract.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Preserving_KNode.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Preserving_Transparent.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Preserving.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_RelationalGraph.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Schema.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_SchemaBarrier.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_SchemaProjection.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Transparent.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\Newman_Safe.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\NonlinearDirectBoundary.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearDominanceCriteria.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearDominanceWitnesses.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearMethodLawCarrier.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\NonlinearResidualTaxonomy.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearTransparentProjection.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearUnconstrainedSplit.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\Normalize_Safe.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\NormalizeSafe_LowerBound.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\ObjectAxiom_Ablation.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\OperationalIncompleteness.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\OrdinalHierarchy_Control.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\OrdinalHierarchy_Controlled.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\OrdinalHierarchy.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\PayloadExposureMatrix.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\Physics\LandauerHeatBound.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\Physics\RecordFormation.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\PolyInterpretation_FullStep.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\PolynomialBarrierGeneral_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\PolynomialBarrierGeneral.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\PrecedenceBarrier.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ProjectedPrimaryBarrier.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ProjectionAsConservativeExtension.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\ProjectionTransactionDynamics.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\ProofTheoreticRegister.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\PumpedBarrierClasses_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\PumpedBarrierClasses.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\QuadraticBarrier_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\QuadraticBarrier.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\QuadraticCrossTermBarrier_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\QuadraticCrossTermBarrier.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\RDRSAlgebraicInterpretationAtlas.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSBoundaryBottleneck.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSConditionalTypedAtlas.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSCoverageLedger.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSCoverageLedgerSeed.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSDescentLens.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSDPProcessorClassification.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSMethodCertificate.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSMethodCertificateClassifier.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSNoBarrierZones.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSNonConservativeEscapeAtlas.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSNonKO7Instances.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\RDRSNotesReconciliationAddendum.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSPathOrderDichotomy.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSProjectionSyntax.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSProjectionTransaction.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSRawDirectMeasure.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSReflectedDirectMeasureDSL.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSRetainedCoordinate.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSearchBudgetInvariance.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSeedCollapse.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticArbitraryClassifier.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticCertificate.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticClassifier.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticCounterexampleAudit.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticCoverageLedger.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticDirectMeasure.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticLensPump.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticNormalizedRawSyntax.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticPayloadSensitivity.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticProjectionTransaction.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticProjectionTransactionAudit.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticRawUniversalAdjudication.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticStructuralAtlas.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSTerminationMethodAtlas.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSTerminationMethodUniverse.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSTerminationMethodUniverseCloseout.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSUniversalPayloadSensitiveBarrier.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RDRSWitnessTransport.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\Reachability_Complexity.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RecCore.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\RecordStorageForm.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RecursiveFamilyBoundaryCloseoutCatalog.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\RecursiveFamilyEscapeCharacterization.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\RecursiveFamilyTypedPolicyRows.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\Recursor\CircularIdentity.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\Recursor\PayloadGrowthBlindness.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ReflectionSchema.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\RepShift_BottleneckPredicate.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\RepShift_LayeredSemanticsTower.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\ResidualMethodClosureCatalog.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ReverseMathFramework.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMathOmega3WellOrdering.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMathSupport.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\RightDuplicatingRecursorSchema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeRoot_Complexity.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Complexity_FastGrowing.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Complexity_MW_Ctx.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Complexity_MW_CtxExact.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Complexity_MW_Root.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Complexity_Ordinal.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Complexity.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Core.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Ctx.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep\BoundaryDuality.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep\DynamicalBoundaryFunctor.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep\EqWVoidAnomaly.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep\FaithfulnessNoGo.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep\GaugeFixingGuard.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep\NonlinearityDichotomy.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep\SigmaFreeAlgebra.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep\SmugglingUndecidability.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep\SyntacticNonDerivability.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStepCtx_Complexity_Cichon.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStepCtx_Complexity_Exponential.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStepCtx_Complexity_LowerBound.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeStepCtx_Confluence.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SafeTrace_CertificateAudit.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\SafeTrace_CertificateBridge.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\SafeTrace_ComplexityBridge.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\SafeTrace_RoadmapCloseout.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\SafeTrace_TripleLexExactness_FinalCatalog.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\SafeTrace_TripleLexExactness.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ScalarProjectionBarrier.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SchemaCanonicalTrace.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SchemaConfessionDominance.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\SchemaForgettingWitness.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SchemaNormMismatch.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SchemaOffsetAndWrapper.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SchemaOperationalIncompleteness.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\SchemaSeedCarrierFactorization.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SchemaWitnessOrder.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SemanticMethodBoundary.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SharingBarrierLift.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\StandardPumpLemmas.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\StepDuplicatingSchema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\StructuralIdentityComparison.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\SymbolicComparatorBarrier_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SymbolicComparatorBarrier.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\SynthesisOracle.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\TerminationPrincipleRegister.lean` | transitive import | present | exact | public, no NDA |
| `OperatorKO7\Meta\TextbookDupInstance.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\TheoryExpansionCloseoutSurface.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\TheoryExpansionReleaseAudit.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_Exactness.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_FinalCatalog.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_ListAudit.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_PerFamily.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_ResidualBoundary.lean` | transitive import | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_Status.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\TPDB_Export.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\TransformedCallClassification.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\TropicalBarrier_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\TropicalBarrier.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\TTT2_CertificateReplay.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\TupleDecomposition.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\TypedBarrierSurvival.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\UniversalBoundary\GrammarClosure.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\W1MethodCarrier.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Meta\WitnessOrder.lean` | transitive import | present | synchronization required | public, no NDA |
| `OperatorKO7\Meta\WPO_PolynomialBarrier_Schema.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\Meta\WPO_PolynomialBarrier.lean` | direct manuscript reference | present | exact | public, no NDA |
| `OperatorKO7\OrientationBoundaryAPI.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\PrimitiveSchemaAPI.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\ResidualMethodAPI.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\SchemaAPI.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\SchemaExtendedAPI.lean` | direct manuscript reference | present | synchronization required | public, no NDA |
| `OperatorKO7\Test\RDRSNotesReconciliationAddendumReach.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
| `OperatorKO7\Test\RDRSTerminationMethodUniverseCloseoutReach.lean` | direct manuscript reference | pending transfer | not present | public, no NDA |
## Operational Inexpressibility Lean Files

### Quantitative manuscript peer-review closure (2026-07-21)

Target manuscript: `C:\Users\Moses\KO7-LLM-Benchmark\1.paper\Operational-Inexpressibility\Rahnama_Operational_Inexpressibility_Quant.tex`.

All **488** Lean files in this closure are designated **public, no NDA**. The closure consists of 186 manuscript-named modules, 11 additional cited-declaration owners, and 291 recursive project imports. Release state is recorded separately from disclosure class: a file may be public/no-NDA while still awaiting transfer or synchronization.

Snapshot against the live authoritative source tree: **182** exact, **93** synchronization required, **213** pending transfer. No files were copied or synchronized during this audit.

| Path | Paper relationship | Public repository state | Disclosure |
|---|---|---|---|
| `OperatorKO7\CrossPaperAPI.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Kernel.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\AffineThresholdSharpness.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArcticBarrier.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArcticBarrier_Schema.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArtsGiesl_DerivationalComplexity.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArtsGiesl_LowerBound.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArtsGiesl_ReverseMathCalibration.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArtsGiesl_UpperBound.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ArtsGieslExactCalibrationUniversal.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\BarrierClass_Classifier.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BarrierWitness.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\BarrierWitness_Budgets.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BarrierWitness_Extended.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BenchmarkedPrimitiveRecursionFamily.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\BoundaryFactorization.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\BoundaryGeneral\C4Classifier.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\BoundaryGeneral\CostedConfession.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryGeneral\EndogenousProvenance.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\BoundaryGeneral\ProvenanceLicense.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\BoundaryGeneral\UniversalityGate.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryGeneral\WholeTermIndistinguishability.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\BoundaryGeneral\WitnessFirst.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\BarrierTransport.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\BoundaryWeightBornRatio.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\ClaimRegistry.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\EngineContract.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\LandauerBridge.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\LicensedQuotient.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\LicensedQuotientFactorization.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\PromotionGate.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\TransportCard.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\TypedRefusalCompleteness.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalAbstentionBound.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalCertificationChain.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalConditionalBound.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalCramerRao.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalDecidableW0.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalFramework.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalGoedelTransfer.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalHeisenbergBound.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalNMethodConvergence.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalP4CObligationLattice.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalProjectionMetaTheorems.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalSPRTBound.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\BoundaryOperator\UniversalSymNCodeDistance.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ClassicalAscentProfile.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\CompositionalMeasure_Impossibility.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ComputableMeasure.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ComputationalLayerCrossing.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_ArgumentFiltering.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_CounterProjection.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_DP.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_Family.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_FutureRouteSchema.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_OptimalityBoundary.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_RouteEvidence.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_SCT.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_Unification.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UniversalAPI.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UniversalInstances.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UniversalRouteLedger.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UniversalUsableRules.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UsableRules.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UsableRulesBridgeAttempt.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UsableRulesConcrete.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConfessionMethod_UsableRulesFinalStatus.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Confluence_Safe.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Conjecture_Boundary.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ConstructionMethodClassification.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Audit.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Certificate.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Exactness.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Partition.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ConstructionRouteCatalog_Payload.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ContextClosed_SN.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ContextClosed_SN_Full.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_CallGraph.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_ExtractedCallGraph.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_FiniteCarrierView.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_FiniteGraph.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_FirstOrderEngine.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_FirstOrderExtraction.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_FirstOrderFrontend.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_Fragment.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_HeadView.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_KernelFirstOrder.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_TPDBExtraction.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DependencyPairs_Works.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DepthBarrier.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\DepthBarrier_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DirectToolSearchMapping.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\CertificateLowerBound.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\Core.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\CriticalPairDefect.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\FiniteDistinctionSurface.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\KO7CriticalPairDefect.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\KO7LocalCone.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\KO7RepairCover.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\KO7TerminalMultiplicity.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\KO7WitnessRank.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\KraftPrefixCertificate.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\RefusalCostModel.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\RepairCover.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\TerminalMultiplicity.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\WitnessRank.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DM_OrderType.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DM_OrderType_LowerBound.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DM_TripleLexExactness.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DM_TripleLexImage.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DM_UpstreamSurface.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\DomainTransformerCertificate_Faithfulness.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\DP_BaseOrder_Boundary.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\EqW_Guard_Barrier.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\EscapeTrichotomy.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\EscapeTrichotomy_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ExtendedDirectToolSearchMapping.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ExternalizedTraceStorage.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\FBI_AdequacyBoundary.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\FBI_Classification.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\FBI_FinalCatalog.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\FBI_GenericAdequacy.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\FBI_Method.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\FiniteGraphReachability.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\FiniteGraphSCC.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\FreeStepDuplicatingSyntax.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\FreeStepDuplicatingTraceBridge.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\GenericConfessionMove.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\GenericDPMethodBoundary.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\GenericSupervisoryEngine.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\GraphPathExtraction.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\HigherOrderNoSharingBoundary.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_BetaBinder.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_Boundary.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_CaptureDecidable.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_CaptureSubfamilies.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_Closeout.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_DecidableClassifiers.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_FinalCatalog.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_FullCaptureBoundary.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_PolicyAudit.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\HigherOrderRewriting_Syntax.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\HigherOrderSharingBoundary.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\HigherOrderSharingBoundary_API.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\HigherOrderSharingBoundary_FinalCatalog.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\Impossibility_Lemmas.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\InformationAccess.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\InformationalIncompleteness\RecursorPayloadErasure.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\InformationalIncompleteness\SharpnessCounterexample.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\InformationTheoreticConfession.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\KBO_Impossible.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\KBO_Impossible_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LawvereYanofskySeparation.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELAdmissibilityData.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LCELBenchmarkDpComparison.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LCELBenchmarkDpUnrestrictedTheorem.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LCELDpInstance.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LCELGenericTransportBridge.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LCELLiteralSubstrate.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LCELMathematicalStructuralIdentity.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELMathematicalSupportWitness.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELP4CCanonicalInstances.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LCELP4CCloseout.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LCELP4CFinalStatus.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LCELP4CResidualObligation.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LCELP4CUniversalBlueprint.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LCELP4CUniversalCertification.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LCELReversibility.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELReversibilityUnconditional.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LCELRouteSemanticsClassification.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LCELSchema.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELSemanticCorrespondence.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELStructuralIdentity.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LCELSubstrateMathematics.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELTypedSigmaGamma.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELUniversalTheorem.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELUnrestrictedClassification.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELUnrestrictedExistence.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LCELUnrestrictedTheorem.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\LCELWitnessFreeStructuralIdentity.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Accounting\AdditiveValuation.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Accounting\BoundaryEvent.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Accounting\EventLedger.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Accounting\EventTrace.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Accounting\ResourceVector.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Accounting\ScalarPolicyFirewall.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\API\Structural.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Audit\AnchorVerificationElab.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Audit\ClaimEntry.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Audit\ClaimKind.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Capabilities\ChannelCapability.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Capabilities\CommittedThermalBoundary.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Capabilities\GaugeCapability.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Capabilities\MinimalBoundary.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Capabilities\PayloadForgettingCapability.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Capabilities\RecordCapability.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Capabilities\ThermalErasureCapability.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Core.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Core\AdmittedEdgeARS.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Core\CanonicalBoundaryFactorization.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Core\DomainRestrictedARS.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Core\ImageARS.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Core\KernelQuotientARS.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Core\PartialComposition.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Core\PartialLicensedReductionMorphism.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Core\QuotientImageEquiv.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Core\RestrictionLaws.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\DistinctionFace.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Execution\BoundaryGate.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Execution\EventSemantics.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Execution\LedgerSoundness.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Execution\TraceAdequacy.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Integrated\BoundaryTransaction.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Integrated\Builders.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Integrated\CertifiedBoundaryTransaction.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Integrated\CertifiedCompositionBoundary.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Integrated\Composition.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Integrated\ConstructionData.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Integrated\Identity.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Integrated\QuantitativeLaws.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Integrated\SemanticNoGo.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\LicensedARS.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\LicensedReductionMorphism.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Machine.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Observer\AbstractPost.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Observer\Galois.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\OrientationFace.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\PlugInstance.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\AlternativeCarrier.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\CoverageDefect.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\DefectAdequacy.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\DistinctionAdapters.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\DomainDefect.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\EdgeDefect.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\FiberDefect.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\GuardedRates.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\KO7ExactProfile.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\KO7SemanticAdequacy.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\KO7TerminalSupportCollapse.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\OrthogonalDefects.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\RepairSemantics.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\SemanticAdequacyCertificate.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\SemanticProfile.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\SemanticScope.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\StructuralComposition.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\StructuralProfile.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\TerminalSupportCollapse.lean` | cited-declaration owner | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Quantitative\WitnessLanguageAdequacy.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Transport\Counterexamples.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Transport\StepLifting.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LicensedBoundaryCalculus\Transport\Strength.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\LinearRec_Ablation.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrier2.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrier2_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArbitrary.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArbitrary_Instances.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArbitrary_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArcticTropical.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArcticTropical_Instances.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierArcticTropical_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierD.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierD_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierFunctional.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierFunctional_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLex.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLex_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLexD.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLexD_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLexPermD.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierLexPermD_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierMix2.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixBarrierMix2_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixOrderInterfaces.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MatrixProjectionCoverage.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MatrixProjectionCoverage_Schema.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MatrixResidualClosureCatalog.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixResidualTaxonomy.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MatrixToolSearchMapping.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MaxBarrier.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MaxBarrier_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MetaHalt_Predicate.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MetaHalt_Regress.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MetaHalt_Signatures.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MPO_FullStep.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MultilinearBarrier.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\MultilinearBarrier_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_CallGraph.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Case.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_CycleFlow.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_ExtractedCallGraph.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_AlgorithmicSearch.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_AlgorithmicSearch_FinalCatalog.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_API.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_Builder.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_BuilderMapping.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_Closeout.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_FinalCatalog.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_GraphSearch.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_FiniteSchema_Instances.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_General.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_GraphCycle.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_KNode.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_KNode_Abstract.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_PacketGraph.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_PayloadFlow.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Preserving.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Preserving_Abstract.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Preserving_KNode.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Preserving_Transparent.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_RelationalGraph.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_SchemaBarrier.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_SchemaProjection.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\MutualDuplication_Transparent.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearDirectBoundary.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearDominanceCriteria.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearDominanceWitnesses.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearMethodLawCarrier.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\NonlinearResidualTaxonomy.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearTransparentProjection.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\NonlinearUnconstrainedSplit.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Normalize_Safe.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\OperationalIncompleteness.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\OperationalInexpressibility\ObserverKernel.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\OperationalInexpressibility\OrbitSimulation.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Physics\LandauerAuditPayload.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Physics\LandauerHeatBound.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Physics\QECSyndromeAsStage2.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Physics\RecordFormation.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Plugs\LawUSStateCA\DecidableW0.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Plugs\LawUSStateCA\DTCFaithfulness.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Plugs\LawUSStateCA\Routes.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Plugs\LawUSStateCA\RoutesExact.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Plugs\PharmaUSFda\DecidableW0.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Plugs\PharmaUSFda\Routes.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Plugs\PharmaUSFda\RoutesExact.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Plugs\QuantumQecPilot\DecidableW0.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Plugs\QuantumQecPilot\Routes.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Plugs\QuantumQecPilot\RoutesExact.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\PolyInterpretation_FullStep.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\PolynomialBarrierGeneral.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\PolynomialBarrierGeneral_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\PrecedenceBarrier.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ProjectedPrimaryBarrier.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ProjectionAsConservativeExtension.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ProjectionTransactionDynamics.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ProofTheoreticRegister.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\PumpedBarrierClasses.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\PumpedBarrierClasses_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\QEC\FourMethodConvergence.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\QEC\MethodFourSymNGaugedCode.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\QEC\MethodOneObligationType.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\QEC\MethodThreeObligationType.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\QEC\MethodTwoSPRTBound.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\QuadraticBarrier.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\QuadraticBarrier_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\QuadraticCrossTermBarrier.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\QuadraticCrossTermBarrier_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RDRSDescentLens.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RDRSProjectionSyntax.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RDRSProjectionTransaction.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSeedCollapse.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticArbitraryClassifier.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticCertificate.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticClassifier.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticDirectMeasure.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticLensPump.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticNormalizedRawSyntax.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticPayloadSensitivity.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RDRSSemanticProjectionTransaction.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RecCore.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RecordEmissionNecessity.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\RecordStorageForm.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Recursor\CircularIdentity.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\Recursor\DPConfessionLicense.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Recursor\DPConfessionLicenseUnconditional.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\Recursor\GaugeCost.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Recursor\InformationEquivalence.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\Recursor\PayloadGrowthBlindness.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Recursor\RaryDuplicator.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Recursor\RecursorFreeAlgebra.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Recursor\SchemaTraceKernel.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Recursor\TraceAction.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Recursor\TraceInvariants.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\Recursor\TRSEquivalence.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ReflectionSchema.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RepShift_BottleneckPredicate.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\RepShift_LayeredSemanticsTower.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ResidualMethodClosureCatalog.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\ArtsGieslFaithful.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\ArtsGieslKO7Bridge.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\ArtsGieslPi02.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\ArtsGieslProduct.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\ArtsGieslProductFull.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\ArtsGieslUpperSemantic.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\ArtsGieslUpperSyntactic.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\Complexity.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\DeductionFO.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\DeductionH.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\Language.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\RCA0.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\StandardModel.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMath\Substitution.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMathFramework.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMathOmega3WellOrdering.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ReverseMathSupport.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Rewriting\ConfluenceDecision.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Rewriting\CriticalPair.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Rewriting\CriticalPairComplete.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Rewriting\CriticalPairLemma.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Rewriting\Position.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Rewriting\Rewrite.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Rewriting\Subst.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Rewriting\Term.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Rewriting\Unify.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Rewriting\UnifyCorrect.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep\BoundaryDuality.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep\BranchEntropy.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep\BranchTransaction.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep\DynamicalBoundaryFunctor.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep\EqWVoidAnomaly.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep\FaithfulnessNoGo.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep\GaugeFixingGuard.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep\NonlinearityDichotomy.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep\SigmaFreeAlgebra.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep\SmugglingUndecidability.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep\SyntacticNonDerivability.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Complexity.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Core.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SafeStep_Ctx.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SafeStepCtx_Confluence.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ScalarProjectionBarrier.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SchemaCanonicalTrace.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SchemaConfessionDominance.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SchemaForgettingWitness.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SchemaNormMismatch.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SchemaOffsetAndWrapper.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SchemaOperationalIncompleteness.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SchemaSeedCarrierFactorization.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SchemaWitnessOrder.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SemanticMethodBoundary.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SharingBarrierLift.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\StandardPumpLemmas.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\StepDuplicatingSchema.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\StructuralIdentityComparison.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\SymbolicComparatorBarrier.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SymbolicComparatorBarrier_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\SynthesisOracle.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\TerminationPrincipleRegister.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\TextbookDupInstance.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_Exactness.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_FinalCatalog.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_ListAudit.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_PerFamily.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_ResidualBoundary.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\ToolSearchFragmentCoverage_Status.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\TPDB_Export.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\TransformedCallClassification.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\TropicalBarrier.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\TropicalBarrier_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\TTT2_CertificateReplay.lean` | manuscript-named module | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\TypedBarrierSurvival.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\Universal\ClassifyUniversal.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\UniversalBoundary\BoundaryClass.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\UniversalBoundary\BoundaryGeneralBridge.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\UniversalBoundary\WitnessTower.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\Meta\UniversalFirstOrderDichotomy.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\UniversalFirstOrderEmbeddings.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\UniversalFirstOrderInterpretationMethod.lean` | required project import | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\W1MethodCarrier.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\W1W2UniversalNecessity.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Meta\WitnessOrder.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Meta\WPO_PolynomialBarrier.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\Meta\WPO_PolynomialBarrier_Schema.lean` | required project import | present, SHA-256 exact | public, no NDA |
| `OperatorKO7\PrimitiveSchemaAPI.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\QEC\Codes\KnillLaflammeEmpirical.lean` | required project import | pending transfer | public, no NDA |
| `OperatorKO7\ResidualMethodAPI.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\SchemaAPI.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\SchemaExtendedAPI.lean` | manuscript-named module | present, synchronization required | public, no NDA |
| `OperatorKO7\Test\LBCIntegratedBoundaryReach.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Test\LBCQuantitativeCrownReach.lean` | manuscript-named module | pending transfer | public, no NDA |
| `OperatorKO7\Test\QuantLawsReach.lean` | manuscript-named module | pending transfer | public, no NDA |

### Preserved operational-adjacent public entries outside the current quantitative manuscript closure (9)

These pre-existing disclosure rows are retained, but they are not counted in the 488-file manuscript closure.

| Path |
|---|
| `OperatorKO7\Test\LCELBenchmarkDpComparison.lean` |
| `OperatorKO7\Test\LCELBenchmarkDpUnrestrictedTheorem.lean` |
| `OperatorKO7\Test\LCELMathematicalStructuralIdentity.lean` |
| `OperatorKO7\Test\LCELMathematicalSupportWitness.lean` |
| `OperatorKO7\Test\LCELSemanticCorrespondence.lean` |
| `OperatorKO7\Test\LCELSubstrateMathematics.lean` |
| `OperatorKO7\Test\LCELUniversalTheorem.lean` |
| `OperatorKO7\Test\LCELUnrestrictedTheorem.lean` |
| `OperatorKO7\Test\LCELWitnessFreeStructuralIdentity.lean` |
## Confluence-Preservation Boundary (Paper C) Lean Files

These are the public theorem surfaces for *The Confluence-Preservation Boundary for Diagonal Identity Queries*: the generic first-order rewriting and Critical Pair Lemma library (`Meta\Rewriting`), the KO7 equality-witness diagonal fork with its global-confluence, guarded-repair, and SafeStep-maximality results (`Meta\DistinctionBoundary`, `Meta\SafeStep`), the informational-incompleteness and retained-route cost-dual readings of the fork (`Meta\InformationalIncompleteness`, `Meta\BoundaryGeneral`, `Meta\DistinctionBoundary`), the finite directed-space and finite Cech obstruction package, the normalization-face irreversibility package, and the reverse-mathematics strength calibration (`Meta\ReverseMath`). The engine-coupled modules of this paper are listed separately under reviewer NDA below.

| Path |
|---|
| `OperatorKO7\Meta\BoundaryGeneral\DiagonalMirror.lean` |
| `OperatorKO7\Meta\BoundaryGeneral\DistinctionRecord.lean` |
| `OperatorKO7\Meta\BoundaryGeneral\PayloadStress.lean` |
| `OperatorKO7\Meta\BoundaryOperator.lean` |
| `OperatorKO7\Meta\ComparatorNecessity.lean` |
| `OperatorKO7\Meta\ComparatorNecessityPartial.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\AxisDualityFunctor.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\CriticalPairCompleteness.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\CriticalPairLemmaKO7.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\ContextualDiagonalFork.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\CopyDiscardDeterminism.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\CostDual.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\CostScalingDimension.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\DirectedReductionSpace.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\DualExternalLicenseBoundary.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\EqualityModeCertificate.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\EqualizerObstruction.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\FiniteCechDiagonalObstruction.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\FiniteGluingObstruction.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\GlobalConfluence.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\GuardingComonad.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\KolmogorovBranchCertificate.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\LawvereObstruction.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\LinearLogicDiagonalInterface.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\MetricDiagonalAxiom.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\Pillar.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\RepairBasis.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\RepairCategory.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\RepairRoutes.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\RewritingLiar.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\SafeStepCtxDerivationLength.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\SemanticsPreservingMaximality.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\SharedRoot.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\SingleBadCriticalPair.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\StrictTransform.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\TerminalRepair.lean` |
| `OperatorKO7\Meta\DistinctionBoundary\TransactionGalois.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\AxisGrowthSeparation.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\CarrierBurden.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\CertificateInterface.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ComparisonAsymmetry.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ConditionalEntropy.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ConfluenceForcedTrilemma.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\DiagonalEntropy.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\DiagonalInert.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\EqWDiagonalCapacity.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\EqWDiagonalDeficit.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\LicensedChannelDeficit.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\LicensedCollapseDeficit.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\MemoryDistinction.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\QueryInterface.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\SemideciderCollapseSchema.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ShannonFinite.lean` |
| `OperatorKO7\Meta\NormalizationBoundary\AntiNormalizationMap.lean` |
| `OperatorKO7\Meta\NormalizationBoundary\DeltaIntegrateAsymmetry.lean` |
| `OperatorKO7\Meta\NormalizationBoundary\DeltaIntegrateLoop.lean` |
| `OperatorKO7\Meta\NormalizationBoundary\NormalizationLicense.lean` |
| `OperatorKO7\Meta\RepShift_BottleneckPredicate.lean` |
| `OperatorKO7\Meta\RepShift_LayeredSemanticsTower.lean` |
| `OperatorKO7\Meta\ReverseMath\Complexity.lean` |
| `OperatorKO7\Meta\ReverseMath\ConfluenceOrderType.lean` |
| `OperatorKO7\Meta\ReverseMath\GuardedNewmanExactCalibration.lean` |
| `OperatorKO7\Meta\ReverseMath\GuardedNewmanRCA0.lean` |
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
| `OperatorKO7\Meta\SafeStep\BranchAdmissionFloor.lean` |
| `OperatorKO7\Meta\SafeStep\BranchCodeFloor.lean` |
| `OperatorKO7\Meta\SafeStep\BranchEntropy.lean` |
| `OperatorKO7\Meta\SafeStep\BranchEntropyGeneral.lean` |
| `OperatorKO7\Meta\SafeStep\BranchTransaction.lean` |
| `OperatorKO7\Meta\SafeStep\DiagonalForkClassicInstance.lean` |
| `OperatorKO7\Meta\SafeStep\DistinctionAscentProfile.lean` |
| `OperatorKO7\Meta\SafeStep\DistinctionControls.lean` |
| `OperatorKO7\Meta\SafeStep\DistinctionInexpressible.lean` |
| `OperatorKO7\Meta\SafeStep\DistinctionWitnessBoundary.lean` |
| `OperatorKO7\Meta\SafeStep\DynamicalBoundaryFunctor.lean` |
| `OperatorKO7\Meta\SafeStep\EntropySink.lean` |
| `OperatorKO7\Meta\SafeStep\EqualityReflectionInstance.lean` |
| `OperatorKO7\Meta\SafeStep\EqualityWitnessGeneralization.lean` |
| `OperatorKO7\Meta\SafeStep\FaithfulnessNoGo.lean` |
| `OperatorKO7\Meta\SafeStep\FalseFormalLegitimacy.lean` |
| `OperatorKO7\Meta\SafeStep\GaugeFixingGuard.lean` |
| `OperatorKO7\Meta\SafeStep\GenericDiagonalFork.lean` |
| `OperatorKO7\Meta\SafeStep\GuardNecessity.lean` |
| `OperatorKO7\Meta\SafeStep\NonlinearityDichotomy.lean` |
| `OperatorKO7\Meta\SafeStep\RecordSurfaceGenerator.lean` |
| `OperatorKO7\Meta\SafeStep\RefusalLoad.lean` |
| `OperatorKO7\Meta\SafeStep\RefusalLoadMinimum.lean` |
| `OperatorKO7\Meta\SafeStep\SafeStepInterpreter.lean` |
| `OperatorKO7\Meta\SafeStep\UniversalGuardCompletion.lean` |
| `OperatorKO7\Test\DistinctionBoundaryClaimLiveness.lean` |

## Shared Lean Infrastructure

| Path |
|---|
| `lakefile.lean` |
| `OperatorKO7.lean` |
| `OperatorKO7\CrossPaperAPI.lean` |
| `OperatorKO7\Test\Sanity.lean` |

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

The following NDA classifications apply only outside the current Orientation Boundary 380-file closure. No Orientation Boundary closure file is withheld under NDA.

### Direct Supervisory Engine Reviewer NDA Files

These files live in the private `OperatorKO7\SupervisoryEngine` tree and are directly used by the supervisory engine project. They are not part of this public repository.

| Path |
|---|
| `OperatorKO7\SupervisoryEngine\ClassifyBarrier.lean` |
| `OperatorKO7\SupervisoryEngine\ClassifyGrammarMeasure.lean` |
| `OperatorKO7\SupervisoryEngine\ClassifyMetaBarrier.lean` |
| `OperatorKO7\SupervisoryEngine\ClassifyMutualDuplication.lean` |
| `OperatorKO7\SupervisoryEngine\ClassifyUniversal.lean` |
| `OperatorKO7\SupervisoryEngine\ConfluenceSurface.lean` |
| `OperatorKO7\SupervisoryEngine\CrossRunDedup.lean` |
| `OperatorKO7\SupervisoryEngine\DistinctionGate.lean` |
| `OperatorKO7\SupervisoryEngine\EngineSelfAudit.lean` |
| `OperatorKO7\SupervisoryEngine\EvidenceCompilerClosure.lean` |
| `OperatorKO7\SupervisoryEngine\EvidenceCompilerDisagreement.lean` |
| `OperatorKO7\SupervisoryEngine\EvidenceCompilerGates.lean` |
| `OperatorKO7\SupervisoryEngine\EvidenceCompilerVerdict.lean` |
| `OperatorKO7\SupervisoryEngine\ForcedOutputCertificate.lean` |
| `OperatorKO7\SupervisoryEngine\ImmigrationEligibility.lean` |
| `OperatorKO7\SupervisoryEngine\LicensedDynamics.lean` |
| `OperatorKO7\SupervisoryEngine\SupervisorState.lean` |
| `OperatorKO7\SupervisoryEngine\TenantPolicy.lean` |
| `OperatorKO7\SupervisoryEngine\TestEngineR3Reach.lean` |
| `OperatorKO7\SupervisoryEngine\TryBarrierCatalog.lean` |
| `OperatorKO7\SupervisoryEngine\TryDPConfession.lean` |
| `OperatorKO7\SupervisoryEngine\W0BaseClassifier.lean` |

### Supervisory Engine Import and Bridge Dependency Reviewer NDA Files

These files are withheld because they are direct supervisory-engine import dependencies or universal bridge/classifier surfaces whose public release would pull private engine/product closure rather than a paper-only theorem closure.

| Path |
|---|

| `OperatorKO7\Meta\Physics\ConfessionLandauerExact.lean` |
| `OperatorKO7\Meta\UniversalBoundary\BoundaryGeneralBridge.lean` |

| `OperatorKO7\Meta\Universal\ClassifyUniversal.lean` |

### Paper A NDA Classification Retired

No file in the current 380-file Orientation Boundary Lean closure is subject to NDA. The former 142-row Paper-A NDA list mixed current closure files with broader development surfaces and is superseded by the complete closure inventory above. Files marked `pending transfer` or `synchronization required` remain release work, but their disclosure class is public.
### Operational-Inexpressibility Legacy NDA Files Outside the Current Quantitative Manuscript Closure

No file in the 488-file `Rahnama_Operational_Inexpressibility_Quant.tex` closure is subject to NDA. The three former conflicts (`RecordEmissionNecessity.lean`, `Recursor/TRSEquivalence.lean`, and `W1W2UniversalNecessity.lean`) are now classified public/no-NDA above. The remaining rows are outside the current quantitative manuscript closure.

| Path |
|---|
| `OperatorKO7\Meta\MetaHalt_Fracture.lean` |
| `OperatorKO7\Meta\MetaHalt_PaperInterface.lean` |
| `OperatorKO7\Meta\MetaHalt_Soundness.lean` |
| `OperatorKO7\Meta\RecordEmissionNecessity_BeyondFirstOrder.lean` |
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
| `OperatorKO7\Meta\InformationalIncompleteness\CarrierCapacity.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\ForcedTrilemma.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\LicensedFactorisation.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\RecursorPayloadErasure.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\SemanticWitnessBridge.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\SharpnessCounterexample.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\UnivDeficitViaChar.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\UniversalDeficit.lean` |
| `OperatorKO7\Meta\SafeStep\GaugeFixingGuardMetaHalt.lean` |
| `OperatorKO7\Test\DistinctionBoundaryReach.lean` |
| `OperatorKO7\Test\InformationalIncompletenessReach.lean` |

## Build Check

The public Lean package should be checked from the repository root with:

```bash
lake build OperatorKO7
```

## Reviewer Access

Reviewer NDA access described here applies only to material outside the Orientation Boundary 380-file closure. Every Lean file supporting that paper is designated public without NDA.
