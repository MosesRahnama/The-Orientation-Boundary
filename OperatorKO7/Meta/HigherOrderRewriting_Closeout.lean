import OperatorKO7.Meta.HigherOrderSharingBoundary_FinalCatalog
import OperatorKO7.Meta.HigherOrderRewriting_PolicyAudit
import OperatorKO7.Meta.HigherOrderRewriting_FullCaptureBoundary

/-!
# Higher-Order Rewriting Closeout

This module turns the accepted M2 theorem surface into a single closeout catalog.
It reuses the finite policy-row taxonomy, adds the new full-capture boundary row
evidence, and keeps the unrestricted lift nonclaim theorem-visible.

The full-capture row is `.theoremBlocked`, matching the policy-audit assignment, and the closeout
layer carries the full justification: the refuted capture-avoidance law, the body-fresh obligation
that does hold, the refuted target interface, and the direct-measure no-gos. The closeout also
projects the indexed evidence family and proves it total. Blocked names a refuted target interface
and nothing wider: `closeout_no_unrestricted_higher_order_impossibility` records that the
unrestricted universal nonorientation claim is itself false.
-/

namespace OperatorKO7.HigherOrderRewritingCloseout

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderNoSharingBoundary
open OperatorKO7.HigherOrderSharingBoundaryFinalCatalog
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBoundary
open OperatorKO7.HigherOrderRewritingBetaBinder
open OperatorKO7.HigherOrderRewritingCaptureSubfamilies
open OperatorKO7.HigherOrderRewritingDecidableClassifiers
open OperatorKO7.HigherOrderRewritingCaptureDecidable
open OperatorKO7.HigherOrderRewritingPolicyAudit
open OperatorKO7.HigherOrderRewritingFullCaptureBoundary

/-- Stable closeout-row alias for the accepted M2 policy audit taxonomy. -/
abbrev HOCloseoutRow := HOPolicyRow

/-- Stable closeout-row status alias for the accepted M2 policy audit taxonomy. -/
abbrev HOCloseoutRowStatus := HOPolicyRowStatus

/-- Canonical M2 closeout rows. -/
abbrev hoCloseoutRows : List HOCloseoutRow :=
  hoPolicyRows

/-- Status projection for the canonical M2 closeout rows. -/
abbrev hoCloseoutRowStatus : HOCloseoutRow → HOCloseoutRowStatus :=
  hoPolicyRowStatus

theorem hoCloseoutRows_length : hoCloseoutRows.length = 8 :=
  hoPolicyRows_length

theorem hoCloseoutRows_mem_iff {row : HOCloseoutRow} :
    row ∈ hoCloseoutRows ↔
      row = .tree ∨
      row = .sharedSurrogate ∨
      row = .explicitSharing ∨
      row = .betaCompatible ∨
      row = .binderAware ∨
      row = .captureSafe ∨
      row = .fullCapture ∨
      row = .unrestrictedHigherOrder :=
  hoPolicyRows_mem_iff

theorem hoCloseoutRows_nodup : hoCloseoutRows.Nodup :=
  hoPolicyRows_nodup

@[simp] theorem hoCloseoutRowStatus_tree :
    hoCloseoutRowStatus .tree = .theoremCovered :=
  hoPolicyRowStatus_tree

@[simp] theorem hoCloseoutRowStatus_sharedSurrogate :
    hoCloseoutRowStatus .sharedSurrogate = .theoremBlocked :=
  hoPolicyRowStatus_sharedSurrogate

@[simp] theorem hoCloseoutRowStatus_explicitSharing :
    hoCloseoutRowStatus .explicitSharing = .theoremBlocked :=
  hoPolicyRowStatus_explicitSharing

@[simp] theorem hoCloseoutRowStatus_betaCompatible :
    hoCloseoutRowStatus .betaCompatible = .theoremBlocked :=
  hoPolicyRowStatus_betaCompatible

@[simp] theorem hoCloseoutRowStatus_binderAware :
    hoCloseoutRowStatus .binderAware = .obligationScoped :=
  hoPolicyRowStatus_binderAware

@[simp] theorem hoCloseoutRowStatus_captureSafe :
    hoCloseoutRowStatus .captureSafe = .certifiedFragment :=
  hoPolicyRowStatus_captureSafe

@[simp] theorem hoCloseoutRowStatus_fullCapture :
    hoCloseoutRowStatus .fullCapture = .theoremBlocked :=
  hoPolicyRowStatus_fullCapture

@[simp] theorem hoCloseoutRowStatus_unrestrictedHigherOrder :
    hoCloseoutRowStatus .unrestrictedHigherOrder = .theoremBlocked :=
  hoPolicyRowStatus_unrestrictedHigherOrder

/-- No closeout row carries the `.open` tag. -/
theorem hoCloseoutRowStatus_never_open :
    ∀ row : HOCloseoutRow, hoCloseoutRowStatus row ≠ .open :=
  hoPolicyRowStatus_never_open

/-! ## Closeout row evidence

The closeout layer projects the same indexed evidence family as the policy audit, and adds the
full-capture bundle that is only visible once `HigherOrderRewriting_FullCaptureBoundary` is in
scope. Status tags remain data at this layer too. -/

/-- Stable closeout alias for the indexed policy-row evidence family. -/
abbrev HOCloseoutRowEvidence : HOCloseoutRow → Prop :=
  HOPolicyRowEvidence

/-- Closeout evidence is total: every row carries its proposition. -/
theorem hoCloseoutRowEvidence_total : ∀ row : HOCloseoutRow, HOCloseoutRowEvidence row :=
  hoPolicyRowEvidence_total

/-- The closeout full-capture row is theorem-blocked on the same justification proved one layer
down, including the capture-avoidance refutation and the target-interface refutation. -/
theorem hoCloseoutRowStatus_fullCapture_is_evidence_backed :
    hoCloseoutRowStatus .fullCapture = .theoremBlocked ∧
      HOCloseoutRowEvidence .fullCapture ∧
      FullCaptureRowBlockedJustification :=
  ⟨hoCloseoutRowStatus_fullCapture,
    hoPolicyRowEvidence_fullCapture,
    full_capture_row_blocked_justification⟩

/-- Preserved: the capture-avoidance law as stated is refuted. -/
theorem closeout_full_capture_avoidance_law_blocked :
    ¬ FullCaptureAvoidanceLaw :=
  fullCaptureAvoidanceLaw_blocked

/-- Preserved: the body-fresh repaired obligation, which is the statement that does hold. -/
theorem closeout_full_capture_avoidance_law_body_fresh_obligation :
    FullCaptureAvoidanceLawUpstreamObligation :=
  fullCaptureAvoidanceLaw_requiresBodyFreshness

/-- Preserved and explicit: no unrestricted higher-order impossibility theorem follows from the
blocked full-capture row. The universal nonorientation claim is refuted, so any such theorem would
be false, not merely unproved. -/
theorem closeout_no_unrestricted_higher_order_impossibility :
    ¬ UnqualifiedHigherOrderRewritingLiftClaim :=
  shared_policy_blocks_unqualified_higher_order_rewriting_lift

/-- Paper-facing closeout catalog for the accepted M2 higher-order rewriting surface. -/
structure HigherOrderRewritingCloseoutCatalog : Prop where
  rowCount : hoCloseoutRows.length = 8
  membershipIff :
    ∀ {row : HOCloseoutRow},
      row ∈ hoCloseoutRows ↔
        row = .tree ∨
        row = .sharedSurrogate ∨
        row = .explicitSharing ∨
        row = .betaCompatible ∨
        row = .binderAware ∨
        row = .captureSafe ∨
        row = .fullCapture ∨
        row = .unrestrictedHigherOrder
  noDupRows : hoCloseoutRows.Nodup
  treeRowEvidence : NoSharingBoundaryStatus
  sharedSurrogateRowEvidence : PolicyOrientsStep sharedPolicy
  explicitSharingRowEvidence : PolicyOrientsStep explicitSharingPolicy
  betaCompatibleRowEvidence : BetaCounterexamplePackage
  binderAwareRowEvidence :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      BinderAwareSubstitutionObligation name binderName arg body →
        FreshFor binderName arg
  captureSafeRowEvidence : HigherOrderCaptureDecidableCatalog
  fullCaptureRowEvidence : HigherOrderFullCaptureBoundaryCatalog
  unrestrictedHigherOrderRowEvidence : ¬ UnqualifiedHigherOrderRewritingLiftClaim
  policyAuditCatalog : HigherOrderPolicyAuditCatalog

/-- Canonical closeout catalog for the accepted M2 higher-order rewriting surface. -/
theorem higher_order_rewriting_closeout_catalog :
    HigherOrderRewritingCloseoutCatalog := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hoCloseoutRows_length
  · intro row
    exact hoCloseoutRows_mem_iff
  · exact hoCloseoutRows_nodup
  · exact catalog_transports_no_sharing_boundary higher_order_sharing_boundary_final_catalog
  · exact shared_policy_counter_orients_step
  · exact explicit_sharing_counter_orients_step
  · exact beta_compatible_counterexample_package
  · intro name binderName arg body h
    exact binderAwareSubstitutionObligation_requires_freshness h
  · exact higher_order_capture_decidable_catalog
  · exact higher_order_full_capture_boundary_catalog
  · exact shared_policy_blocks_unqualified_higher_order_rewriting_lift
  · exact higher_order_policy_audit_catalog

end OperatorKO7.HigherOrderRewritingCloseout
