import OperatorKO7.Meta.HigherOrderRewriting_CaptureDecidable

/-!
# Higher-Order Rewriting Policy Audit

This module turns the current higher-order rewriting theorem surface into a
finite, theorem-visible audit. The rows stay exact: theorem-covered branches,
blocked branches, obligation-scoped branches, certified fragments, and open
surfaces are recorded without upgrading any claim beyond what Lean proves.
-/

namespace OperatorKO7.HigherOrderRewritingPolicyAudit

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderNoSharingBoundary
open OperatorKO7.HigherOrderSharingBoundaryFinalCatalog
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBoundary
open OperatorKO7.HigherOrderRewritingBetaBinder
open OperatorKO7.HigherOrderRewritingCaptureSubfamilies
open OperatorKO7.HigherOrderRewritingDecidableClassifications
open OperatorKO7.HigherOrderRewritingCaptureDecidable

/-- Finite policy-row taxonomy for the current higher-order rewriting audit. -/
inductive HOPolicyRow
  | tree
  | sharedSurrogate
  | explicitSharing
  | betaCompatible
  | binderAware
  | captureSafe
  | fullCapture
  | unrestrictedHigherOrder
  deriving DecidableEq, Repr

/-- Finite status labels for the current higher-order rewriting audit rows. -/
inductive HOPolicyRowStatus
  | theoremBlocked
  | theoremCovered
  | obligationScoped
  | certifiedFragment
  | open
  deriving DecidableEq, Repr

/-- Canonical finite list of the currently audited higher-order policy rows. -/
def hoPolicyRows : List HOPolicyRow :=
  [ .tree
  , .sharedSurrogate
  , .explicitSharing
  , .betaCompatible
  , .binderAware
  , .captureSafe
  , .fullCapture
  , .unrestrictedHigherOrder
  ]

/-- Status projection for the current higher-order policy audit. -/
def hoPolicyRowStatus : HOPolicyRow → HOPolicyRowStatus
  | .tree => .theoremCovered
  | .sharedSurrogate => .theoremBlocked
  | .explicitSharing => .theoremBlocked
  | .betaCompatible => .theoremBlocked
  | .binderAware => .obligationScoped
  | .captureSafe => .certifiedFragment
  | .fullCapture => .open
  | .unrestrictedHigherOrder => .theoremBlocked

theorem hoPolicyRows_length : hoPolicyRows.length = 8 := by
  rfl

theorem hoPolicyRows_mem_iff {row : HOPolicyRow} :
    row ∈ hoPolicyRows ↔
      row = .tree ∨
      row = .sharedSurrogate ∨
      row = .explicitSharing ∨
      row = .betaCompatible ∨
      row = .binderAware ∨
      row = .captureSafe ∨
      row = .fullCapture ∨
      row = .unrestrictedHigherOrder := by
  cases row <;> simp [hoPolicyRows]

theorem hoPolicyRows_nodup : hoPolicyRows.Nodup := by
  decide

@[simp] theorem hoPolicyRowStatus_tree :
    hoPolicyRowStatus .tree = .theoremCovered := rfl

@[simp] theorem hoPolicyRowStatus_sharedSurrogate :
    hoPolicyRowStatus .sharedSurrogate = .theoremBlocked := rfl

@[simp] theorem hoPolicyRowStatus_explicitSharing :
    hoPolicyRowStatus .explicitSharing = .theoremBlocked := rfl

@[simp] theorem hoPolicyRowStatus_betaCompatible :
    hoPolicyRowStatus .betaCompatible = .theoremBlocked := rfl

@[simp] theorem hoPolicyRowStatus_binderAware :
    hoPolicyRowStatus .binderAware = .obligationScoped := rfl

@[simp] theorem hoPolicyRowStatus_captureSafe :
    hoPolicyRowStatus .captureSafe = .certifiedFragment := rfl

@[simp] theorem hoPolicyRowStatus_fullCapture :
    hoPolicyRowStatus .fullCapture = .open := rfl

@[simp] theorem hoPolicyRowStatus_unrestrictedHigherOrder :
    hoPolicyRowStatus .unrestrictedHigherOrder = .theoremBlocked := rfl

/-- Paper-facing finite audit catalog for the current higher-order policy surface. -/
structure HigherOrderPolicyAuditCatalog : Prop where
  rowCount : hoPolicyRows.length = 8
  membershipIff :
    ∀ {row : HOPolicyRow},
      row ∈ hoPolicyRows ↔
        row = .tree ∨
        row = .sharedSurrogate ∨
        row = .explicitSharing ∨
        row = .betaCompatible ∨
        row = .binderAware ∨
        row = .captureSafe ∨
        row = .fullCapture ∨
        row = .unrestrictedHigherOrder
  noDupRows : hoPolicyRows.Nodup
  treeRowEvidence : NoSharingBoundaryStatus
  sharedSurrogateRowEvidence : PolicyOrientsStep sharedPolicy
  explicitSharingRowEvidence : PolicyOrientsStep explicitSharingPolicy
  betaCompatibleRowEvidence : BetaCounterexamplePackage
  binderAwareRowEvidence :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      BinderAwareSubstitutionObligation name binderName arg body →
        FreshFor binderName arg
  captureSafeRowEvidence :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      CaptureSafeSubstitutionObligation name binderName arg body →
        FreshFor binderName arg
  decidableClassificationRowEvidence : HigherOrderDecidableClassificationCatalog
  captureDecisionRowEvidence : HigherOrderCaptureDecidableCatalog
  fullCaptureRowEvidence : FullCaptureSemanticsStatus
  unrestrictedHigherOrderRowEvidence : ¬ UnqualifiedHigherOrderRewritingLiftClaim

/-- Canonical finite audit catalog for the current higher-order policy surface. -/
theorem higher_order_policy_audit_catalog : HigherOrderPolicyAuditCatalog := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hoPolicyRows_length
  · intro row
    exact hoPolicyRows_mem_iff
  · exact hoPolicyRows_nodup
  · exact catalog_transports_no_sharing_boundary higher_order_sharing_boundary_final_catalog
  · exact shared_policy_counter_orients_step
  · exact explicit_sharing_counter_orients_step
  · exact beta_compatible_counterexample_package
  · intro name binderName arg body h
    exact binderAwareSubstitutionObligation_requires_freshness h
  · intro name binderName arg body h
    exact captureSafeSubstitutionObligation_requires_freshness h
  · exact higher_order_decidable_classification_catalog
  · exact higher_order_capture_decidable_catalog
  · exact full_capture_semantics_open
  · exact shared_policy_blocks_unqualified_higher_order_rewriting_lift

end OperatorKO7.HigherOrderRewritingPolicyAudit
