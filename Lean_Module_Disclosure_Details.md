# Lean Module Disclosure Details

## Current Release Scope

This repository is the public Lean companion for exactly three manuscripts:

- *The Orientation Boundary for Step-Duplicating Recursors: Mechanized Impossibility, Escape, and Certification.*
- *Operational Inexpressibility at the Primitive-Recursion Orientation Boundary.*
- *The Confluence-Preservation Boundary for Diagonal Identity Queries: Non-Left-Linearity, Signature Inexpressibility, and External Guarding.*

As of 2026-07-26, after the second release delta below, the `OperatorKO7\` tree contains 678 Lean source files. A file is included only when it is directly named by one of the three manuscripts, owns a declaration cited by one of them, or lies in the recursive project-owned import closure of such a file. Repository metadata, proof artifacts, and Lake configuration are retained as supporting release infrastructure.

No NDA, qualified-reviewer restriction, or separate access grant applies to the retained public-release copies. The separate NDA-controlled inventory at the end governs excluded/private material and records the six historical paths whose manuscript-required public copies remain public.

## Closure Receipt

| Manuscript | Project-owned Lean closure |
|---|---:|
| Orientation Boundary | 383 files: 273 manuscript-named modules plus 110 recursive imports |
| Operational Inexpressibility (quantitative manuscript) | 500 files: 197 manuscript-named modules, 11 cited-declaration owners, and 292 recursive imports |
| Confluence-Preservation Boundary | 263 files: 158 public module-map seeds plus 105 recursive imports |
| Deduplicated three-manuscript union | 678 files |

The Operational-Inexpressibility count rose by eleven on 2026-07-26 with the gap-closure modules recorded in the second release delta below. All eleven are named by the manuscript's appendix module map, and each one's project-owned imports were already public, so the closure grows by exactly eleven.

The union figure also absorbs a one-file reconciliation. The first delta of 2026-07-26 added `OperatorKO7\Meta\DistinctionBoundary\ContextualDiagonalScope.lean` and raised the Confluence-Preservation count to 263, but left the union at its pre-addition value of 666; the correct pre-gap-closure union was 667, and adding the eleven gap-closure modules gives 678.

**Count verification required before release.** The per-manuscript figures above are carried forward from the previous receipt with the gap-closure delta applied; they were not recomputed against the working tree, which was mid-synchronization when this section was written. Reproduce the tree count with

```bash
find OperatorKO7 -name '*.lean' | wc -l
```

and recompute the three per-manuscript closures from the current manuscript sources before publishing. Any difference from 678 means files entered or left the tree after this delta and the receipt needs regenerating.

The Orientation count includes `OperatorKO7\Meta\ComputableMeasure_Verification.lean`, which is named without a `.lean` suffix in the manuscript and was omitted from the earlier 382-file parser receipt.

The Confluence-Preservation count rose by one on 2026-07-26 with the addition of `OperatorKO7\Meta\DistinctionBoundary\ContextualDiagonalScope.lean`, a new module-map seed named by the Distinction Boundary manuscript.

## Release Delta 2026-07-26

An editorial audit of the confluence-axis and quantitative manuscripts found two places where manuscript prose ran ahead of the mechanization it cited. Both were closed with new Lean, and all four affected files are source-synchronized here.

| Public path | Change | Headline | Trusted base |
|---|---|---|---|
| `OperatorKO7\Meta\DistinctionBoundary\ContextualDiagonalScope.lean` | new file | `contextual_fracture_scope` | axiom-free |
| `OperatorKO7\Meta\DistinctionBoundary\Quantitative\TerminalMultiplicity.lean` | extended | `normalizingAt_premise_cannot_be_weakened` | baseline whitelist |
| `OperatorKO7\Meta\Recursor\TRSEquivalence.lean` | extended | `recursor_circular_orbit_system_isomorphism` | baseline whitelist |
| `OperatorKO7\Test\DistinctionBoundaryClaimLiveness.lean` | extended | imports and checks the two new headlines | n/a (gate) |

**Scope of the contextual fracture.** The `eqW` diagonal fork is uniform in `a` under the root relation `Step`, and that uniformity does not carry to the full context closure. At a `delta`-headed diagonal the difference verdict contracts to `void` and the peak joins, so the fracture dissolves; it survives at `eqW void void` because `integrate void` is stuck. The new module proves both directions and the cone invariant separating them. The pre-existing `ContextualDiagonalFork.lean` certificate is a root statement despite its name and is unaffected.

**Load-bearing premise.** The terminal-support characterization requires that *every* term reachable from the source itself reach a normal form, which is stronger than requiring a normal form for the source alone. The new three-state witness shows the weaker reading makes the biconditional false, pinning the hypothesis as unweakenable.

**Verification.** Each module replays under single-file `lake env lean` with zero errors and zero `sorry`, and reports the trusted base above under `#print axioms`. A whole-repository `lake build` is currently blocked by a ProofWidgets dependency-checkout state unrelated to these files; resolve that before relying on the aggregate build check below.

## Release Delta 2026-07-26 (second wave): quantitative-manuscript gap closure

A full editorial audit of `Rahnama_Operational_Inexpressibility_Quant.tex` found three blocking and fifteen major defects where manuscript prose ran ahead of, diverged from, or overstated the mechanization it cited. All eighteen are closed by proof. Eleven new modules enter the public release, and the manuscript's appendix module map names every one of them.

| Public path | Closes | Headline | Trusted base |
|---|---|---|---|
| `OperatorKO7\Meta\Recursor\MassProfileIdentity.lean` | mass-profile separation claim | `recursorOrbit_selfEmbeddingOrbit_massProfile_pointwise_eq`, `massProfileObserver_cannot_separate_recursorOrbit_from_selfEmbeddingOrbit` | baseline whitelist |
| `OperatorKO7\Meta\Recursor\NonvacuousClosure.lean` | trivial licensed quotient, generic orbit isomorphism, stipulated information equivalence | `massProfileLicensedQuotient_separates`, `orbit_isomorphism_does_not_transport_termination`, `information_equivalence_for_every_functional` | baseline whitelist |
| `OperatorKO7\Meta\ReverseMath\SizeChangeSoundness.lean` | dependency-pair soundness content | `sizeChangeGraph_has_no_infinite_call_chain`, `sizeChangeGraph_boundedSN`, `dupDPStep_wellFounded` | baseline whitelist |
| `OperatorKO7\Meta\LCELBoundaryReimportRepair.lean` | layer-crossing clause collision | `boundary_and_reimport_overlap_is_impossible`, `annotated_clauses_strictly_weaker_than_conservativity` | axiom-free |
| `OperatorKO7\Meta\RecordEmissionDynamic.lean` | orphaned dynamic record-emission definition | `canonicalStage_carries_frame_and_active_generator_positions` | baseline whitelist |
| `OperatorKO7\Meta\Recursor\TerminalDecoderScope.lean` | dropped sort-separation hypothesis | `schemaTerm_base_is_never_frame_headed`, `unsortedTerminalRecord_depth_not_recoverable` | baseline whitelist |
| `OperatorKO7\Meta\SchemaExplicitDescriptionGap.lean` | unqualified explicit-description gap | `explicitDescription_gap_positive`, `explicitDescription_gap_fails_at_zero` | baseline whitelist |
| `OperatorKO7\Meta\ArtsGiesl_ProofLengthBySize.lean` | rule size conflated with signature size | `agProofLength_le_of_nonempty`, `constructionCost_unbounded_in_ruleSize` | baseline whitelist |
| `OperatorKO7\Meta\BoundaryGeneral\ProjectionSensitivityAndProvenance.lean` | undefined sensitivity, circular staticity, undefined provenance vocabulary | `statements_not_determined_by_reversible_layer_lie_outside_base_derivability`, `static_of_stepInvariant_license`, `endogenous_provenance_collapse` | axiom-free to baseline whitelist |
| `OperatorKO7\Meta\Recursor\SignatureDerivabilitySharpness.lean` | unscoped non-derivability conclusion | `counterHeightAlgebra_separates_witnessPair`, `signature_nonDerivability_is_relative_to_the_constant_class` | axiom-free to baseline whitelist |
| `OperatorKO7\Test\GapClosureReach.lean` | reach gate | per-theorem axiom audit over all of the above | n/a (gate) |

**Mass-profile separation.** Two orbits satisfying the same existential linear-growth predicate remain separable by slope and intercept, so the growth-class statement alone does not deliver a separation failure. The repair names the circular reference the schematic actually describes, the self-embedding rule `t -> delta t`, whose right-hand side contains its own left-hand side and which excludes every strictly decreasing measure. Launched from the recursor's own initial state, the two orbits carry equal mass at every index, so every observer factoring through the mass profile returns the same value on both. A companion theorem shows the earlier merge-chain witness attains the growth class alone, which is why it supported the weaker statement.

**Layer-crossing clauses.** The boundary clause, the licensed-extension clause, and the reimport-conservativity clause jointly forbid any statement from lying in both the boundary and the reimport class. Both canonical instances arrange that overlap, the reflection instance by taking the reimport class to be a complexity class containing its own boundary sentence. The repair replaces conservativity with the annotated reimport both instances actually perform, which admits the overlap; the collision, the repair, and a model carrying the overlap are all mechanized.

**Dependency-pair soundness.** `Meta\ReverseMath\ArtsGieslPi02.lean` and `Meta\ReverseMath\ArtsGieslUpperSyntactic.lean` are unchanged and remain correct. They certify a `Pi02` shape on an elementary predecessor-descent sentence, and their own docstrings decline to identify that sentence with dependency-pair soundness. The manuscript now states this, and the soundness content it previously attributed to those records is carried by `SizeChangeSoundness.lean`, which proves one-thread size-change soundness, chain freeness and well-foundedness of the extracted singleton pair, the bounded universal-existential presentation with the counter height as explicit chain-length bound, and surjectivity of the projection fixing the instance measure at order type `omega`.

**Verification.** Each module replays under single-file `lake env lean` with zero errors, zero `sorry`, zero `admit`, zero new `axiom`, and zero native reduction. Every headline theorem reports a subset of the baseline whitelist `{propext, Classical.choice, Quot.sound}` under `#print axioms`, and several report no axioms at all. The repository theorem-naming lint passes over 27,428 declarations. The whole-repository `lake build` remains blocked by the ProofWidgets dependency-checkout state noted in the previous delta, which is unrelated to these files.

**Synchronization.** All eleven paths above are present in this tree and byte-identical to the source repository. Their prerequisite imports (`Kernel.lean`, `Meta\Recursor\CircularIdentity.lean`, `Meta\Recursor\GaugeCost.lean`, `Meta\Recursor\SchemaTraceKernel.lean`, `Meta\RecordEmissionNecessity.lean`) were already public, so the release closure required no further additions.

## Foundational Former-NDA Files Disclosed Publicly

No proof-foundational file may remain NDA-only. Any module directly named by a manuscript, owning a cited declaration, or imported recursively by a manuscript proof must be included in the public release before the corresponding formal claim is presented as publicly reproducible.

The 2026-07-26 proof-closure audit identified six paths in the historical NDA inventory that meet that rule. All six are present and source-synchronized in this repository:

| Public path | Proof relationship |
|---|---|
| `OperatorKO7\Meta\UniversalBoundary\BoundaryGeneralBridge.lean` | Named directly by the Operational-Inexpressibility manuscript |
| `OperatorKO7\Meta\Physics\ConfessionLandauerExact.lean` | Imported by `Meta\InformationalIncompleteness\LicensedCollapseDeficit.lean` |
| `OperatorKO7\Meta\Universal\ClassifyUniversal.lean` | Imported by the public universal-decision and domain-plug proof surfaces |
| `OperatorKO7\Meta\BoundaryOperator\TypedRefusalCompleteness.lean` | Imported by `Meta\BoundaryOperator\EngineContract.lean` and `Meta\Universal\ClassifyUniversal.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\RecursorPayloadErasure.lean` | Imported by `Meta\LicensedBoundaryCalculus\Core.lean` |
| `OperatorKO7\Meta\InformationalIncompleteness\SharpnessCounterexample.lean` | Imported by `Meta\LicensedBoundaryCalculus\Core.lean` |

The other 57 NDA-controlled paths have zero exact path/module references in the three manuscripts and zero import edges from the 665-file public proof stack. They are not required to elaborate the disclosed proofs.

## Supervisory Engine Boundary

The separate product-facing `SupervisoryEngine\` tree is not part of any of the three manuscripts and is intentionally excluded. The 22 files previously copied into that repository-root tree had no exact path reference, module-name reference, or import edge from the manuscript stack.

`OperatorKO7\Meta\GenericSupervisoryEngine.lean` remains included because it is a proof-layer dependency imported by `OperatorKO7\CrossPaperAPI.lean`; it is part of the manuscript closure despite its name. It is not one of the removed product-facing engine files.

## Manuscript Inputs

The release scope was computed from the current source manuscripts `Rahnama_The_Orientation_Boundary.tex`, `Rahnama_Operational_Inexpressibility_Quant.tex`, and `Rahnama_The_Distinction_Boundary.tex`. Manuscript source snapshots are not part of this Lean-only repository release.

## Build Check

Run from the repository root:

```bash
lake build OperatorKO7
```

## NDA-Controlled File Inventory

**Reinstated 2026-07-26.** This final section preserves the exact 63-path NDA inventory from the earlier disclosure: 22 direct Supervisory Engine files, 3 engine bridge dependencies, 26 Operational-Inexpressibility legacy files, and 12 confluence reviewer files.

Fifty-seven paths are NDA-controlled and excluded from this public repository. The six foundational overlaps are disclosed in the main section above and already have public release copies; those copies remain public, while non-public product variants and associated private material remain NDA-controlled. Reinstating this inventory does not add excluded source files back into the repository.

### Direct Supervisory Engine Files (22)

| Path | Status |
|---|---|
| `OperatorKO7\SupervisoryEngine\ClassifyBarrier.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\ClassifyGrammarMeasure.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\ClassifyMetaBarrier.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\ClassifyMutualDuplication.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\ClassifyUniversal.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\ConfluenceSurface.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\CrossRunDedup.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\DistinctionGate.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\EngineSelfAudit.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\EvidenceCompilerClosure.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\EvidenceCompilerDisagreement.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\EvidenceCompilerGates.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\EvidenceCompilerVerdict.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\ForcedOutputCertificate.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\ImmigrationEligibility.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\LicensedDynamics.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\SupervisorState.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\TenantPolicy.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\TestEngineR3Reach.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\TryBarrierCatalog.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\TryDPConfession.lean` | NDA-controlled, excluded |
| `OperatorKO7\SupervisoryEngine\W0BaseClassifier.lean` | NDA-controlled, excluded |

### Supervisory Engine Bridge Dependencies (3)

| Path | Status |
|---|---|
| `OperatorKO7\Meta\Physics\ConfessionLandauerExact.lean` | Public manuscript-overlap copy; private product variants remain NDA-controlled |
| `OperatorKO7\Meta\UniversalBoundary\BoundaryGeneralBridge.lean` | Public manuscript-overlap copy; private product variants remain NDA-controlled |
| `OperatorKO7\Meta\Universal\ClassifyUniversal.lean` | Public manuscript-overlap copy; private product variants remain NDA-controlled |

### Operational-Inexpressibility Legacy Files (26)

| Path | Status |
|---|---|
| `OperatorKO7\Meta\MetaHalt_Fracture.lean` | NDA-controlled, excluded |
| `OperatorKO7\Meta\MetaHalt_PaperInterface.lean` | NDA-controlled, excluded |
| `OperatorKO7\Meta\MetaHalt_Soundness.lean` | NDA-controlled, excluded |
| `OperatorKO7\Meta\RecordEmissionNecessity_BeyondFirstOrder.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\ConfessionMethodFutureRouteSchemaReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\ConfessionMethodOptimalityBoundaryReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\ConfessionMethodUniversalAPIReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\ConfessionMethodUniversalInstancesReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\ConfessionMethodUniversalRouteLedgerReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\ConfessionMethodUniversalUsableRulesReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\ConfessionMethodUsableRulesBridgeAttemptReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\ConfessionMethodUsableRulesFinalStatusReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\ConfessionMethodUsableRulesReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\GenericConfessionMoveReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\LCELP4CCanonicalInstancesReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\LCELP4CCloseoutReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\LCELP4CFinalStatusReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\LCELP4CResidualObligationReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\LCELP4CUniversalBlueprintReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\LCELP4CUniversalCertificationReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\LCELRoadmapFinalReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\LCELRouteSemanticsClassificationReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\MetaHalt.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\RecursorTRSEquivalenceReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\UniversalFirstOrderDichotomyReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\UsableRulesBridgeReach.lean` | NDA-controlled, excluded |

### Confluence-Preservation Boundary Reviewer Files (12)

| Path | Status |
|---|---|
| `OperatorKO7\Meta\BoundaryOperator\TypedRefusalCompleteness.lean` | Public manuscript-overlap copy; private product variants remain NDA-controlled |
| `OperatorKO7\Meta\InformationalIncompleteness\CarrierCapacity.lean` | NDA-controlled, excluded |
| `OperatorKO7\Meta\InformationalIncompleteness\ForcedTrilemma.lean` | NDA-controlled, excluded |
| `OperatorKO7\Meta\InformationalIncompleteness\LicensedFactorisation.lean` | NDA-controlled, excluded |
| `OperatorKO7\Meta\InformationalIncompleteness\RecursorPayloadErasure.lean` | Public manuscript-overlap copy; private product variants remain NDA-controlled |
| `OperatorKO7\Meta\InformationalIncompleteness\SemanticWitnessBridge.lean` | NDA-controlled, excluded |
| `OperatorKO7\Meta\InformationalIncompleteness\SharpnessCounterexample.lean` | Public manuscript-overlap copy; private product variants remain NDA-controlled |
| `OperatorKO7\Meta\InformationalIncompleteness\UnivDeficitViaChar.lean` | NDA-controlled, excluded |
| `OperatorKO7\Meta\InformationalIncompleteness\UniversalDeficit.lean` | NDA-controlled, excluded |
| `OperatorKO7\Meta\SafeStep\GaugeFixingGuardMetaHalt.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\DistinctionBoundaryReach.lean` | NDA-controlled, excluded |
| `OperatorKO7\Test\InformationalIncompletenessReach.lean` | NDA-controlled, excluded |
