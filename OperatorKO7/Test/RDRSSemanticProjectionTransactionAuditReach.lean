import OperatorKO7.Meta.RDRSSemanticProjectionTransactionAudit

/-!
# Reachability test for the S6.5 projection-transaction hardening surface

References each of the eight required S6.5 theorems plus the bridge
and the concrete `counterFirstLex_R` real payload-forgetting projection.
Compilation of this file is the reachability witness that the audit
module is wired into the build tree.

The reachability checks use `#check` (no `example :` or `theorem`
declarations), per the no-production-`example :` discipline of the
Lean Development Bible.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSSemanticProjectionTransactionAuditReach

open OperatorKO7.RDRSSemanticProjectionTransactionAudit

/-! ### Eight required S6.5 theorems / definitions -/

#check @semantic_projection_escape_factors_through_seed_collapse
#check @semantic_projection_escape_retained_factors_through_counter
#check @semantic_projection_escape_has_witness_transport
#check @semantic_dp_projection_transaction_canonical
#check @semantic_projection_escape_not_plain_erasure
#check @semantic_projection_transaction_escape_sound_hardened
#check @semantic_boundary_bottleneck_w0_blocked_w2_succeeds
#check @semantic_search_budget_invariance

/-! ### Concrete real payload-forgetting projection witnesses -/

#check @counterFirstLex_seedCollapse
#check @counterFirstLex_Rproj
#check @counterFirstLex_semanticMeasure
#check @counterFirstLex_dpSemanticTransaction
#check @counterFirstLex_dpSemanticTransactionEscape
#check @counterFirstLex_dpProjectionEscape

/-! ### Legacy bridge -/

#check
  @OperatorKO7.RDRSSemanticProjectionTransaction.SemanticProjectionTransactionEscape.toLegacy

/-! ### Audit anchor String -/

#check @rdrs_semantic_projection_transaction_audit_anchor

end OperatorKO7.RDRSSemanticProjectionTransactionAuditReach
