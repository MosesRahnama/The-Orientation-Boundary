import OperatorKO7.Meta.HigherOrderSharingBoundary_FinalCatalog
import OperatorKO7.Meta.HigherOrderRewriting_PolicyAudit
import OperatorKO7.Meta.HigherOrderRewriting_FullCaptureBoundary

/-!
# Higher-Order Rewriting Closeout

This module turns the accepted M2 theorem surface into a single closeout catalog.
It reuses the finite policy-row taxonomy, adds the new full-capture boundary row
evidence, and keeps the unrestricted lift nonclaim theorem-visible.
-/

namespace OperatorKO7.HigherOrderRewritingCloseout

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderNoSharingBoundary
open OperatorKO7.HigherOrderSharingBoundaryFinalCatalog
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBoundary
open OperatorKO7.HigherOrderRewritingBetaBinder
open OperatorKO7.HigherOrderRewritingCaptureSubfamilies
open OperatorKO7.HigherOrderRewritingDecidableClassifications
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
    hoCloseoutRowStatus .fullCapture = .open :=
  hoPolicyRowStatus_fullCapture

@[simp] theorem hoCloseoutRowStatus_unrestrictedHigherOrder :
    hoCloseoutRowStatus .unrestrictedHigherOrder = .theoremBlocked :=
  hoPolicyRowStatus_unrestrictedHigherOrder

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
