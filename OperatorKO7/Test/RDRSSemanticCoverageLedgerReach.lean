import OperatorKO7.Meta.RDRSSemanticCoverageLedger

/-!
# Reachability test for the S7 semantic coverage ledger surface

References each public ledger theorem plus the capstone. Compilation
of this file is the reachability witness that the ledger module is
wired into the build tree.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSSemanticCoverageLedgerReach

open OperatorKO7.RDRSSemanticCoverageLedger

/-! ### Ledger row counts and bucket partition -/

#check @coverage_ledger_length
#check @coverage_blocked_count
#check @coverage_projection_escape_count
#check @coverage_construction_escape_count
#check @coverage_transform_escape_count
#check @coverage_not_direct_count
#check @coverage_no_temporary_unclassified
#check @coverage_partition_total
#check @coverage_zero_axiom_footprint

/-- The manuscript-facing semantic coverage ledger has sixteen rows. -/
theorem reach_semantic_coverage_ledger_length :
    semanticCoverageLedger.length = 16 :=
  coverage_ledger_length

/-- The five productive semantic buckets partition the sixteen ledger rows. -/
theorem reach_semantic_coverage_productive_partition :
    blocked_rows.length + projection_escape_rows.length
      + construction_escape_rows.length + transform_escape_rows.length
      + not_direct_rows.length = 16 := by
  rw [coverage_blocked_count, coverage_projection_escape_count,
    coverage_construction_escape_count, coverage_transform_escape_count,
    coverage_not_direct_count]

/-- The full semantic partition also records zero temporary-unclassified rows. -/
theorem reach_semantic_coverage_full_partition :
    blocked_rows.length + projection_escape_rows.length
      + construction_escape_rows.length + transform_escape_rows.length
      + not_direct_rows.length + temporary_unclassified_rows.length = 16 :=
  coverage_partition_total

/-! ### Per-row agreement with the S6 audit -/

#check @coverage_counterFirstLex_classifier_agrees
#check @coverage_termAlgebraRewriteClosure_classifier_agrees
#check @coverage_nonlinearCounterPayloadCoupling_classifier_agrees
#check @coverage_dpProjection_classifier_agrees
#check @coverage_argumentFiltering_classifier_agrees
#check @coverage_fullMonotoneAlgebra_classifier_agrees
#check @coverage_mspoWitness_classifier_agrees
#check @coverage_fullWpoGwpoWitness_classifier_agrees
#check @coverage_semanticLabeling_classifier_agrees

/-! ### No-plain-erasure on projection-escape rows + capstone -/

#check @coverage_no_plain_erasure_projection_escape
#check @semantic_coverage_ledger_closed
#check @SemanticCoverageLedgerClosed

/-! ### Audit anchor -/

#check @rdrs_semantic_coverage_ledger_anchor

end OperatorKO7.RDRSSemanticCoverageLedgerReach
