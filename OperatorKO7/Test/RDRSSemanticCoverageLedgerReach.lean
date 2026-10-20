import OperatorKO7.Meta.RDRSSemanticCoverageLedger

set_option autoImplicit false

/-!
# Reach and axiom gate: S7 semantic coverage ledger

Mechanical parity gate for `Meta/RDRSSemanticCoverageLedger.lean`. Every
explicit public source declaration of that module, including every inductive
constructor, every structure projection, and every structure constructor,
appears once in the `#check` block and once in the `#print axioms` block:

```text
source declarations minus reach #check names   = 0
reach #check names minus #print axioms names   = 0
```

The WP-10 section adds the row-indexed evidence surface: `SemanticRowClaim`
computed per row, `SemanticCuratedReason` indexed by `CoverageRowId` with
constructors only at the four curated rows, and the full partition of
`allCoverageRowIds` into the twelve typed-payload and four curated rows
(membership equivalence, both subset directions, disjointness, permutation,
and exact counts).

Expected axiom ceiling: a subset of `{propext, Classical.choice, Quot.sound}`.
-/

namespace OperatorKO7.RDRSSemanticCoverageLedgerReach

open OperatorKO7.RDRSSemanticCoverageLedger

/-! ### Source-to-reach surface: 218 declarations -/

#check @DirectnessStatus
#check @DirectnessStatus.direct
#check @DirectnessStatus.notDirect
#check @DirectnessStatus.notApplicable
#check @DirectnessStatus.adjudicatedRefuted
#check @RowStatus
#check @RowStatus.yes
#check @RowStatus.no
#check @RowStatus.notApplicable
#check @PaperAClaim
#check @PaperAClaim.s0_adjudication
#check @PaperAClaim.s2_payload_sensitivity_split
#check @PaperAClaim.s3_lens_pump_barrier
#check @PaperAClaim.s4_projection_transaction
#check @PaperAClaim.s5_classifier
#check @PaperAClaim.s6_counterexample_audit
#check @PaperAClaim.s6p5_projection_transaction_hardening
#check @PaperAClaim.notApplicable
#check @ClassificationAnchor
#check @ClassificationAnchor.s0_naive_raw_semantic_universal_adjudicated
#check @ClassificationAnchor.s2_payload_sensitive_decisive_not_counter_forgetting
#check @ClassificationAnchor.s2_counter_first_lex_raw_not_decisive
#check @ClassificationAnchor.s3_semantic_lens_pump_no_orients
#check @ClassificationAnchor.s3_no_orients_of_semantic_payload_sensitive_decisive_descent
#check @ClassificationAnchor.s4_semantic_projection_escape_requires_sigma
#check @ClassificationAnchor.s4_semantic_projection_escape_requires_seed_collapse
#check @ClassificationAnchor.s4_semantic_projection_escape_requires_projected_orientation
#check @ClassificationAnchor.s4_semantic_projection_escape_requires_wellFounded
#check @ClassificationAnchor.s5_semantic_classifier_total
#check @ClassificationAnchor.s5_semantic_temporary_unclassified_count_is_zero
#check @ClassificationAnchor.s5_semantic_projection_transaction_escape_sound
#check @ClassificationAnchor.s6_audit_classify_total
#check @ClassificationAnchor.s6_audit_no_temporary_unclassified
#check @ClassificationAnchor.s6_semantic_counterexample_audit_closed
#check @ClassificationAnchor.s6p5_semantic_projection_escape_not_plain_erasure
#check @ClassificationAnchor.s6p5_semantic_projection_transaction_escape_sound_hardened
#check @ClassificationAnchor.s6p5_semantic_dp_projection_transaction_canonical
#check @ClassificationAnchor.s6p5_semantic_projection_escape_retained_factors_through_counter
#check @ClassificationAnchor.s6p5_semantic_boundary_bottleneck_w0_blocked_w2_succeeds
#check @ClassificationAnchor.s6p5_semantic_search_budget_invariance
#check @CoverageRow
#check @CoverageRow.familyLabel
#check @CoverageRow.directness
#check @CoverageRow.rawPayloadSensitive
#check @CoverageRow.decisivePayloadSensitive
#check @CoverageRow.projectionTransaction
#check @CoverageRow.classificationAnchor
#check @CoverageRow.classifierLabel
#check @CoverageRow.axiomFootprint
#check @CoverageRow.paperAClaim
#check @CoverageRow.mk
#check @s0_adjudication_row
#check @s3_lens_pump_row
#check @s5_classifier_row
#check @s6p5_hardening_row
#check @s6p5_dp_canonical_row
#check @s6p5_bottleneck_row
#check @s6p5_search_invariance_row
#check @s6_counterFirstLex_row
#check @s6_termAlgebraRewriteClosure_row
#check @s6_nonlinearCounterPayloadCoupling_row
#check @s6_dpProjection_row
#check @s6_argumentFiltering_row
#check @s6_fullMonotoneAlgebra_row
#check @s6_mspoWitness_row
#check @s6_fullWpoGwpoWitness_row
#check @s6_semanticLabeling_row
#check @semanticCoverageLedger
#check @semanticCounterFirstLexStep
#check @SemanticProjectionHardeningReceipt
#check @SemanticCanonicalDPReceipt
#check @SemanticBoundaryBottleneckReceipt
#check @SemanticSearchBudgetReceipt
#check @CanonicalSemanticProjectionWitness
#check @CanonicalSemanticProjectionWitness.escape
#check @CanonicalSemanticProjectionWitness.payloadForgetting
#check @CanonicalSemanticProjectionWitness.hardening
#check @CanonicalSemanticProjectionWitness.mk
#check @canonicalSemanticProjectionWitness
#check @TypedProjectionAnchorEvidence
#check @TypedProjectionAnchorEvidence.hardened
#check @TypedProjectionAnchorEvidence.dpCanonical
#check @TypedProjectionAnchorEvidence.bottleneck
#check @TypedProjectionAnchorEvidence.searchBudget
#check @TypedProjectionAnchorEvidence.notPlainErasure
#check @typed_hardened_projection_evidence
#check @typed_dp_canonical_projection_evidence
#check @typed_bottleneck_projection_evidence
#check @typed_search_budget_projection_evidence
#check @typed_not_plain_erasure_projection_evidence
#check @EvidenceBackedCoverageRow
#check @EvidenceBackedCoverageRow.row
#check @EvidenceBackedCoverageRow.projectionEvidence
#check @EvidenceBackedCoverageRow.mk
#check @evidenceBackedNonProjectionRow
#check @evidenceBackedProjectionRow
#check @typed_s0_adjudication_row
#check @typed_s3_lens_pump_row
#check @typed_s5_classifier_row
#check @typed_s6_counterFirstLex_row
#check @typed_s6_termAlgebraRewriteClosure_row
#check @typed_s6_nonlinearCounterPayloadCoupling_row
#check @typed_s6_dpProjection_row
#check @typed_s6_argumentFiltering_row
#check @typed_s6_fullMonotoneAlgebra_row
#check @typed_s6_mspoWitness_row
#check @typed_s6_fullWpoGwpoWitness_row
#check @typed_s6_semanticLabeling_row
#check @typed_s6p5_hardening_row
#check @typed_s6p5_dp_canonical_row
#check @typed_s6p5_bottleneck_row
#check @typed_s6p5_search_invariance_row
#check @semanticCoverageEvidenceLedger
#check @semanticCoverageEvidenceLedger_length
#check @semanticCoverageEvidenceLedger_rows
#check @semanticCoverageRow_has_evidence_backing
#check @semantic_projection_escape_row_has_typed_evidence
#check @blocked_rows
#check @projection_escape_rows
#check @construction_escape_rows
#check @transform_escape_rows
#check @not_direct_rows
#check @temporary_unclassified_rows
#check @zero_axiom_rows
#check @coverage_ledger_length
#check @coverage_blocked_count
#check @coverage_projection_escape_count
#check @coverage_construction_escape_count
#check @coverage_transform_escape_count
#check @coverage_not_direct_count
#check @coverage_no_temporary_unclassified
#check @coverage_partition_total
#check @coverage_zero_axiom_footprint
#check @coverage_counterFirstLex_classifier_agrees
#check @coverage_termAlgebraRewriteClosure_classifier_agrees
#check @coverage_nonlinearCounterPayloadCoupling_classifier_agrees
#check @coverage_dpProjection_classifier_agrees
#check @coverage_argumentFiltering_classifier_agrees
#check @coverage_fullMonotoneAlgebra_classifier_agrees
#check @coverage_mspoWitness_classifier_agrees
#check @coverage_fullWpoGwpoWitness_classifier_agrees
#check @coverage_semanticLabeling_classifier_agrees
#check @coverage_no_plain_erasure_projection_escape
#check @SemanticCoverageLedgerClosed
#check @SemanticCoverageLedgerClosed.rowCount
#check @SemanticCoverageLedgerClosed.blockedCount
#check @SemanticCoverageLedgerClosed.projectionEscapeCount
#check @SemanticCoverageLedgerClosed.constructionEscapeCount
#check @SemanticCoverageLedgerClosed.transformEscapeCount
#check @SemanticCoverageLedgerClosed.notDirectCount
#check @SemanticCoverageLedgerClosed.temporaryUnclassifiedCount
#check @SemanticCoverageLedgerClosed.zeroAxiomFootprintRows
#check @SemanticCoverageLedgerClosed.partitionTotal
#check @SemanticCoverageLedgerClosed.noPlainErasureProjectionEscape
#check @SemanticCoverageLedgerClosed.evidenceRowCount
#check @SemanticCoverageLedgerClosed.evidenceRowsExact
#check @SemanticCoverageLedgerClosed.projectionEscapeTypedEvidence
#check @SemanticCoverageLedgerClosed.mk
#check @semantic_coverage_ledger_closed
#check @rdrs_semantic_coverage_ledger_anchor
#check @S0AdjudicationPayload
#check @S3LensPumpPayload
#check @S5ClassifierPayload
#check @AuditRowClaim
#check @ProjectionRowClaim
#check @CoverageRowId
#check @CoverageRowId.s0Adjudication
#check @CoverageRowId.s3LensPump
#check @CoverageRowId.s5Classifier
#check @CoverageRowId.s6CounterFirstLex
#check @CoverageRowId.s6TermAlgebraRewriteClosure
#check @CoverageRowId.s6NonlinearCounterPayloadCoupling
#check @CoverageRowId.s6DpProjection
#check @CoverageRowId.s6ArgumentFiltering
#check @CoverageRowId.s6FullMonotoneAlgebra
#check @CoverageRowId.s6MspoWitness
#check @CoverageRowId.s6FullWpoGwpoWitness
#check @CoverageRowId.s6SemanticLabeling
#check @CoverageRowId.s6p5Hardening
#check @CoverageRowId.s6p5DpCanonical
#check @CoverageRowId.s6p5Bottleneck
#check @CoverageRowId.s6p5SearchInvariance
#check @coverageRowOf
#check @allCoverageRowIds
#check @allCoverageRowIds_length
#check @allCoverageRowIds_nodup
#check @mem_allCoverageRowIds
#check @allCoverageRowIds_reproduce_ledger
#check @SemanticRowClaim
#check @SemanticCuratedReason
#check @SemanticCuratedReason.fullMonotoneAlgebraNoConstructionCarrier
#check @SemanticCuratedReason.mspoWitnessNoConstructionCarrier
#check @SemanticCuratedReason.fullWpoGwpoNoConstructionCarrier
#check @SemanticCuratedReason.semanticLabelingNoTransformCarrier
#check @SemanticRowEvidence
#check @SemanticRowEvidence.typedClaim
#check @SemanticRowEvidence.curated
#check @rowIsTypedPayload
#check @typedPayloadCoverageRowIds
#check @curatedCoverageRowIds
#check @typedPayloadCoverageRowIds_length
#check @curatedCoverageRowIds_length
#check @typedPayloadCoverageRowIds_nodup
#check @curatedCoverageRowIds_nodup
#check @curatedCoverageRowIds_eq
#check @coverage_row_membership_equiv
#check @typedPayloadCoverageRowIds_subset
#check @curatedCoverageRowIds_subset
#check @coverage_row_split_disjoint
#check @coverage_row_partition_perm
#check @coverage_row_split_total
#check @semanticRowClaim_only_at_typed_rows
#check @curatedReason_only_at_curated_rows
#check @curatedReason_rows
#check @semanticRowEvidence_shapes_exclusive
#check @semanticRowEvidence_total
#check @semantic_coverage_zero_string_only_evidence_rows
#check @semantic_coverage_sixteen_row_evidence_closed

/-! ### Reach-to-axiom surface: 218 declarations -/

#print axioms DirectnessStatus
#print axioms DirectnessStatus.direct
#print axioms DirectnessStatus.notDirect
#print axioms DirectnessStatus.notApplicable
#print axioms DirectnessStatus.adjudicatedRefuted
#print axioms RowStatus
#print axioms RowStatus.yes
#print axioms RowStatus.no
#print axioms RowStatus.notApplicable
#print axioms PaperAClaim
#print axioms PaperAClaim.s0_adjudication
#print axioms PaperAClaim.s2_payload_sensitivity_split
#print axioms PaperAClaim.s3_lens_pump_barrier
#print axioms PaperAClaim.s4_projection_transaction
#print axioms PaperAClaim.s5_classifier
#print axioms PaperAClaim.s6_counterexample_audit
#print axioms PaperAClaim.s6p5_projection_transaction_hardening
#print axioms PaperAClaim.notApplicable
#print axioms ClassificationAnchor
#print axioms ClassificationAnchor.s0_naive_raw_semantic_universal_adjudicated
#print axioms ClassificationAnchor.s2_payload_sensitive_decisive_not_counter_forgetting
#print axioms ClassificationAnchor.s2_counter_first_lex_raw_not_decisive
#print axioms ClassificationAnchor.s3_semantic_lens_pump_no_orients
#print axioms ClassificationAnchor.s3_no_orients_of_semantic_payload_sensitive_decisive_descent
#print axioms ClassificationAnchor.s4_semantic_projection_escape_requires_sigma
#print axioms ClassificationAnchor.s4_semantic_projection_escape_requires_seed_collapse
#print axioms ClassificationAnchor.s4_semantic_projection_escape_requires_projected_orientation
#print axioms ClassificationAnchor.s4_semantic_projection_escape_requires_wellFounded
#print axioms ClassificationAnchor.s5_semantic_classifier_total
#print axioms ClassificationAnchor.s5_semantic_temporary_unclassified_count_is_zero
#print axioms ClassificationAnchor.s5_semantic_projection_transaction_escape_sound
#print axioms ClassificationAnchor.s6_audit_classify_total
#print axioms ClassificationAnchor.s6_audit_no_temporary_unclassified
#print axioms ClassificationAnchor.s6_semantic_counterexample_audit_closed
#print axioms ClassificationAnchor.s6p5_semantic_projection_escape_not_plain_erasure
#print axioms ClassificationAnchor.s6p5_semantic_projection_transaction_escape_sound_hardened
#print axioms ClassificationAnchor.s6p5_semantic_dp_projection_transaction_canonical
#print axioms ClassificationAnchor.s6p5_semantic_projection_escape_retained_factors_through_counter
#print axioms ClassificationAnchor.s6p5_semantic_boundary_bottleneck_w0_blocked_w2_succeeds
#print axioms ClassificationAnchor.s6p5_semantic_search_budget_invariance
#print axioms CoverageRow
#print axioms CoverageRow.familyLabel
#print axioms CoverageRow.directness
#print axioms CoverageRow.rawPayloadSensitive
#print axioms CoverageRow.decisivePayloadSensitive
#print axioms CoverageRow.projectionTransaction
#print axioms CoverageRow.classificationAnchor
#print axioms CoverageRow.classifierLabel
#print axioms CoverageRow.axiomFootprint
#print axioms CoverageRow.paperAClaim
#print axioms CoverageRow.mk
#print axioms s0_adjudication_row
#print axioms s3_lens_pump_row
#print axioms s5_classifier_row
#print axioms s6p5_hardening_row
#print axioms s6p5_dp_canonical_row
#print axioms s6p5_bottleneck_row
#print axioms s6p5_search_invariance_row
#print axioms s6_counterFirstLex_row
#print axioms s6_termAlgebraRewriteClosure_row
#print axioms s6_nonlinearCounterPayloadCoupling_row
#print axioms s6_dpProjection_row
#print axioms s6_argumentFiltering_row
#print axioms s6_fullMonotoneAlgebra_row
#print axioms s6_mspoWitness_row
#print axioms s6_fullWpoGwpoWitness_row
#print axioms s6_semanticLabeling_row
#print axioms semanticCoverageLedger
#print axioms semanticCounterFirstLexStep
#print axioms SemanticProjectionHardeningReceipt
#print axioms SemanticCanonicalDPReceipt
#print axioms SemanticBoundaryBottleneckReceipt
#print axioms SemanticSearchBudgetReceipt
#print axioms CanonicalSemanticProjectionWitness
#print axioms CanonicalSemanticProjectionWitness.escape
#print axioms CanonicalSemanticProjectionWitness.payloadForgetting
#print axioms CanonicalSemanticProjectionWitness.hardening
#print axioms CanonicalSemanticProjectionWitness.mk
#print axioms canonicalSemanticProjectionWitness
#print axioms TypedProjectionAnchorEvidence
#print axioms TypedProjectionAnchorEvidence.hardened
#print axioms TypedProjectionAnchorEvidence.dpCanonical
#print axioms TypedProjectionAnchorEvidence.bottleneck
#print axioms TypedProjectionAnchorEvidence.searchBudget
#print axioms TypedProjectionAnchorEvidence.notPlainErasure
#print axioms typed_hardened_projection_evidence
#print axioms typed_dp_canonical_projection_evidence
#print axioms typed_bottleneck_projection_evidence
#print axioms typed_search_budget_projection_evidence
#print axioms typed_not_plain_erasure_projection_evidence
#print axioms EvidenceBackedCoverageRow
#print axioms EvidenceBackedCoverageRow.row
#print axioms EvidenceBackedCoverageRow.projectionEvidence
#print axioms EvidenceBackedCoverageRow.mk
#print axioms evidenceBackedNonProjectionRow
#print axioms evidenceBackedProjectionRow
#print axioms typed_s0_adjudication_row
#print axioms typed_s3_lens_pump_row
#print axioms typed_s5_classifier_row
#print axioms typed_s6_counterFirstLex_row
#print axioms typed_s6_termAlgebraRewriteClosure_row
#print axioms typed_s6_nonlinearCounterPayloadCoupling_row
#print axioms typed_s6_dpProjection_row
#print axioms typed_s6_argumentFiltering_row
#print axioms typed_s6_fullMonotoneAlgebra_row
#print axioms typed_s6_mspoWitness_row
#print axioms typed_s6_fullWpoGwpoWitness_row
#print axioms typed_s6_semanticLabeling_row
#print axioms typed_s6p5_hardening_row
#print axioms typed_s6p5_dp_canonical_row
#print axioms typed_s6p5_bottleneck_row
#print axioms typed_s6p5_search_invariance_row
#print axioms semanticCoverageEvidenceLedger
#print axioms semanticCoverageEvidenceLedger_length
#print axioms semanticCoverageEvidenceLedger_rows
#print axioms semanticCoverageRow_has_evidence_backing
#print axioms semantic_projection_escape_row_has_typed_evidence
#print axioms blocked_rows
#print axioms projection_escape_rows
#print axioms construction_escape_rows
#print axioms transform_escape_rows
#print axioms not_direct_rows
#print axioms temporary_unclassified_rows
#print axioms zero_axiom_rows
#print axioms coverage_ledger_length
#print axioms coverage_blocked_count
#print axioms coverage_projection_escape_count
#print axioms coverage_construction_escape_count
#print axioms coverage_transform_escape_count
#print axioms coverage_not_direct_count
#print axioms coverage_no_temporary_unclassified
#print axioms coverage_partition_total
#print axioms coverage_zero_axiom_footprint
#print axioms coverage_counterFirstLex_classifier_agrees
#print axioms coverage_termAlgebraRewriteClosure_classifier_agrees
#print axioms coverage_nonlinearCounterPayloadCoupling_classifier_agrees
#print axioms coverage_dpProjection_classifier_agrees
#print axioms coverage_argumentFiltering_classifier_agrees
#print axioms coverage_fullMonotoneAlgebra_classifier_agrees
#print axioms coverage_mspoWitness_classifier_agrees
#print axioms coverage_fullWpoGwpoWitness_classifier_agrees
#print axioms coverage_semanticLabeling_classifier_agrees
#print axioms coverage_no_plain_erasure_projection_escape
#print axioms SemanticCoverageLedgerClosed
#print axioms SemanticCoverageLedgerClosed.rowCount
#print axioms SemanticCoverageLedgerClosed.blockedCount
#print axioms SemanticCoverageLedgerClosed.projectionEscapeCount
#print axioms SemanticCoverageLedgerClosed.constructionEscapeCount
#print axioms SemanticCoverageLedgerClosed.transformEscapeCount
#print axioms SemanticCoverageLedgerClosed.notDirectCount
#print axioms SemanticCoverageLedgerClosed.temporaryUnclassifiedCount
#print axioms SemanticCoverageLedgerClosed.zeroAxiomFootprintRows
#print axioms SemanticCoverageLedgerClosed.partitionTotal
#print axioms SemanticCoverageLedgerClosed.noPlainErasureProjectionEscape
#print axioms SemanticCoverageLedgerClosed.evidenceRowCount
#print axioms SemanticCoverageLedgerClosed.evidenceRowsExact
#print axioms SemanticCoverageLedgerClosed.projectionEscapeTypedEvidence
#print axioms SemanticCoverageLedgerClosed.mk
#print axioms semantic_coverage_ledger_closed
#print axioms rdrs_semantic_coverage_ledger_anchor
#print axioms S0AdjudicationPayload
#print axioms S3LensPumpPayload
#print axioms S5ClassifierPayload
#print axioms AuditRowClaim
#print axioms ProjectionRowClaim
#print axioms CoverageRowId
#print axioms CoverageRowId.s0Adjudication
#print axioms CoverageRowId.s3LensPump
#print axioms CoverageRowId.s5Classifier
#print axioms CoverageRowId.s6CounterFirstLex
#print axioms CoverageRowId.s6TermAlgebraRewriteClosure
#print axioms CoverageRowId.s6NonlinearCounterPayloadCoupling
#print axioms CoverageRowId.s6DpProjection
#print axioms CoverageRowId.s6ArgumentFiltering
#print axioms CoverageRowId.s6FullMonotoneAlgebra
#print axioms CoverageRowId.s6MspoWitness
#print axioms CoverageRowId.s6FullWpoGwpoWitness
#print axioms CoverageRowId.s6SemanticLabeling
#print axioms CoverageRowId.s6p5Hardening
#print axioms CoverageRowId.s6p5DpCanonical
#print axioms CoverageRowId.s6p5Bottleneck
#print axioms CoverageRowId.s6p5SearchInvariance
#print axioms coverageRowOf
#print axioms allCoverageRowIds
#print axioms allCoverageRowIds_length
#print axioms allCoverageRowIds_nodup
#print axioms mem_allCoverageRowIds
#print axioms allCoverageRowIds_reproduce_ledger
#print axioms SemanticRowClaim
#print axioms SemanticCuratedReason
#print axioms SemanticCuratedReason.fullMonotoneAlgebraNoConstructionCarrier
#print axioms SemanticCuratedReason.mspoWitnessNoConstructionCarrier
#print axioms SemanticCuratedReason.fullWpoGwpoNoConstructionCarrier
#print axioms SemanticCuratedReason.semanticLabelingNoTransformCarrier
#print axioms SemanticRowEvidence
#print axioms SemanticRowEvidence.typedClaim
#print axioms SemanticRowEvidence.curated
#print axioms rowIsTypedPayload
#print axioms typedPayloadCoverageRowIds
#print axioms curatedCoverageRowIds
#print axioms typedPayloadCoverageRowIds_length
#print axioms curatedCoverageRowIds_length
#print axioms typedPayloadCoverageRowIds_nodup
#print axioms curatedCoverageRowIds_nodup
#print axioms curatedCoverageRowIds_eq
#print axioms coverage_row_membership_equiv
#print axioms typedPayloadCoverageRowIds_subset
#print axioms curatedCoverageRowIds_subset
#print axioms coverage_row_split_disjoint
#print axioms coverage_row_partition_perm
#print axioms coverage_row_split_total
#print axioms semanticRowClaim_only_at_typed_rows
#print axioms curatedReason_only_at_curated_rows
#print axioms curatedReason_rows
#print axioms semanticRowEvidence_shapes_exclusive
#print axioms semanticRowEvidence_total
#print axioms semantic_coverage_zero_string_only_evidence_rows
#print axioms semantic_coverage_sixteen_row_evidence_closed

/-! ## Concrete reach examples -/

/-- Every one of the sixteen rows carries typed, non-String evidence. -/
theorem reach_semantic_coverage_all_rows_typed :
    ∀ id : CoverageRowId, SemanticRowEvidence id :=
  semanticRowEvidence_total

/-- No row admits both evidence shapes, so evidence for one row cannot be used
at another. -/
theorem reach_semantic_coverage_no_cross_row_borrowing (id : CoverageRowId) :
    ¬ (SemanticRowClaim id ∧ Nonempty (SemanticCuratedReason id)) :=
  semanticRowEvidence_shapes_exclusive id

/-- The typed-payload and curated sublists permute the ledger identifier list. -/
theorem reach_semantic_coverage_partition_perm :
    (typedPayloadCoverageRowIds ++ curatedCoverageRowIds).Perm allCoverageRowIds :=
  coverage_row_partition_perm

/-- The manuscript-facing semantic coverage ledger has sixteen rows. -/
theorem reach_semantic_coverage_ledger_length :
    semanticCoverageLedger.length = 16 :=
  coverage_ledger_length

/-- The full semantic partition also records zero temporary-unclassified rows. -/
theorem reach_semantic_coverage_full_partition :
    blocked_rows.length + projection_escape_rows.length
      + construction_escape_rows.length + transform_escape_rows.length
      + not_direct_rows.length + temporary_unclassified_rows.length = 16 :=
  coverage_partition_total

end OperatorKO7.RDRSSemanticCoverageLedgerReach
