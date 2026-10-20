import OperatorKO7.Meta.HigherOrderRewriting_CaptureDecidable

/-!
This module stores policies, evidence fields, and assigned status tags in a finite catalog.
Status values are defined by row; their relationship to theorem evidence is carried by the separate
indexed predicate `HOPolicyRowEvidence`, which is proved total. Status tags remain data: they carry
no mathematical content on their own, and every semantic claim about a row is the corresponding
member of the indexed family.

The `.fullCapture` row is `.theoremBlocked` rather than `.open`. The blocking content is the exact
counterexample boundary `FullCaptureSemanticsStatus`, the unconditional universal no-go for every
`DirectHOMeasure`, and the stronger unconditional no-go for the parameterized variable-constant family
(with its premise-bearing version retained); the
capture-avoidance refutation `fullCaptureAvoidanceLaw_blocked` and the target-interface refutation
`full_capture_target_interface_blocked` live one layer up in
`OperatorKO7.Meta.HigherOrderRewriting_FullCaptureBoundary` and are carried at the closeout layer.
Blocked means a named target interface is refuted; it does not assert an unrestricted higher-order
impossibility theorem, and the `.unrestrictedHigherOrder` row records the refutation of that
overclaim explicitly.
-/

namespace OperatorKO7.HigherOrderRewritingPolicyAudit

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderNoSharingBoundary
open OperatorKO7.HigherOrderSharingBoundaryFinalCatalog
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBoundary
open OperatorKO7.HigherOrderRewritingBetaBinder
open OperatorKO7.HigherOrderRewritingCaptureSubfamilies
open OperatorKO7.HigherOrderRewritingDecidableClassifiers
open OperatorKO7.HigherOrderRewritingCaptureDecidable

/-- Carrier with the constructors displayed below. -/
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

/-- Carrier with the constructors displayed below. -/
inductive HOPolicyRowStatus
  | theoremBlocked
  | theoremCovered
  | obligationScoped
  | certifiedFragment
  | open
  deriving DecidableEq, Repr

/-- Definition with formal content given by the displayed type and body. -/
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

/-- Definition with formal content given by the displayed type and body. -/
def hoPolicyRowStatus : HOPolicyRow → HOPolicyRowStatus
  | .tree => .theoremCovered
  | .sharedSurrogate => .theoremBlocked
  | .explicitSharing => .theoremBlocked
  | .betaCompatible => .theoremBlocked
  | .binderAware => .obligationScoped
  | .captureSafe => .certifiedFragment
  | .fullCapture => .theoremBlocked
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
    hoPolicyRowStatus .fullCapture = .theoremBlocked := rfl

@[simp] theorem hoPolicyRowStatus_unrestrictedHigherOrder :
    hoPolicyRowStatus .unrestrictedHigherOrder = .theoremBlocked := rfl

/-- No row carries the `.open` tag. The constructor is retained in the enumeration so the status
type is unchanged, but the assignment no longer uses it. -/
theorem hoPolicyRowStatus_never_open :
    ∀ row : HOPolicyRow, hoPolicyRowStatus row ≠ .open := by
  intro row
  cases row <;> decide

/-! ## Indexed row evidence

`hoPolicyRowStatus` is data. `HOPolicyRowEvidence` is the semantic content: an indexed family
assigning each row the exact proposition its status is claimed on, proved for every row by
`hoPolicyRowEvidence_total`. Reading a status tag alone establishes nothing. -/

/-- The proposition carrying each policy row's semantic content. -/
def HOPolicyRowEvidence : HOPolicyRow → Prop
  | .tree => NoSharingBoundaryStatus
  | .sharedSurrogate => PolicyOrientsStep sharedPolicy
  | .explicitSharing => PolicyOrientsStep explicitSharingPolicy
  | .betaCompatible =>
      BetaCounterexamplePackage ∧ ¬ BetaStepOrientsPolicyCounter betaCompatiblePolicy
  | .binderAware =>
      ∀ {name binderName : Nat} {arg body : HOTerm},
        BinderAwareSubstitutionObligation name binderName arg body →
          FreshFor binderName arg
  | .captureSafe => HigherOrderCaptureDecidableCatalog
  | .fullCapture =>
      FullCaptureSemanticsStatus ∧
        (∀ M : DirectHOMeasure, ¬ OrientsDuplicatingBeta M) ∧
        (∀ (c : Nat) (M : VarConstantDirectHOMeasure c),
          ¬ VarConstantOrientsDuplicatingBeta M) ∧
        (∀ (c : Nat) (M : VarConstantDirectHOMeasure c),
          UnboundedRange M → ¬ VarConstantOrientsDuplicatingBeta M)
  | .unrestrictedHigherOrder => ¬ UnqualifiedHigherOrderRewritingLiftClaim

/-- Tree row: the transported no-sharing boundary status. -/
theorem hoPolicyRowEvidence_tree : HOPolicyRowEvidence .tree :=
  catalog_transports_no_sharing_boundary higher_order_sharing_boundary_final_catalog

/-- Shared-surrogate row: the shared policy counter orients its step. -/
theorem hoPolicyRowEvidence_sharedSurrogate : HOPolicyRowEvidence .sharedSurrogate :=
  shared_policy_counter_orients_step

/-- Explicit-sharing row: the explicit-sharing policy counter orients its step. -/
theorem hoPolicyRowEvidence_explicitSharing : HOPolicyRowEvidence .explicitSharing :=
  explicit_sharing_counter_orients_step

/-- Beta-compatible row: a concrete non-oriented beta step, and the resulting refutation of
policy-counter orientation over beta steps. -/
theorem hoPolicyRowEvidence_betaCompatible : HOPolicyRowEvidence .betaCompatible :=
  ⟨beta_compatible_counterexample_package,
    beta_compatible_policy_does_not_orient_beta_steps⟩

/-- Binder-aware row: the named obligation exposes the required argument freshness. -/
theorem hoPolicyRowEvidence_binderAware : HOPolicyRowEvidence .binderAware := by
  show ∀ {name binderName : Nat} {arg body : HOTerm},
      BinderAwareSubstitutionObligation name binderName arg body →
        FreshFor binderName arg
  intro name binderName arg body h
  exact binderAwareSubstitutionObligation_requires_freshness h

/-- Capture-safe row: the executable capture-decision catalog. -/
theorem hoPolicyRowEvidence_captureSafe : HOPolicyRowEvidence .captureSafe :=
  higher_order_capture_decidable_catalog

/-- Full-capture row: the exact counterexample boundary, the unconditional universal no-go over
every `DirectHOMeasure`, the unconditional no-go over the parameterized variable-constant family, and its
premise-bearing version. This is the content the `.theoremBlocked` tag stands on. -/
theorem hoPolicyRowEvidence_fullCapture : HOPolicyRowEvidence .fullCapture :=
  ⟨full_capture_semantics_exact_boundary,
    no_directHOMeasure_orients_duplicating_beta,
    fun _ M => no_varConstantDirectHOMeasure_orients_duplicating_beta M,
    fun _ M hUnbounded =>
      no_unbounded_varConstantDirectHOMeasure_orients_duplicating_beta M hUnbounded⟩

/-- Unrestricted higher-order row: the shared orienter refutes the universal nonorientation claim,
so no unrestricted higher-order impossibility theorem is available. -/
theorem hoPolicyRowEvidence_unrestrictedHigherOrder :
    HOPolicyRowEvidence .unrestrictedHigherOrder :=
  shared_policy_blocks_unqualified_higher_order_rewriting_lift

/-- Evidence is total: every row of the finite taxonomy carries its proposition. -/
theorem hoPolicyRowEvidence_total : ∀ row : HOPolicyRow, HOPolicyRowEvidence row := by
  intro row
  cases row with
  | tree => exact hoPolicyRowEvidence_tree
  | sharedSurrogate => exact hoPolicyRowEvidence_sharedSurrogate
  | explicitSharing => exact hoPolicyRowEvidence_explicitSharing
  | betaCompatible => exact hoPolicyRowEvidence_betaCompatible
  | binderAware => exact hoPolicyRowEvidence_binderAware
  | captureSafe => exact hoPolicyRowEvidence_captureSafe
  | fullCapture => exact hoPolicyRowEvidence_fullCapture
  | unrestrictedHigherOrder => exact hoPolicyRowEvidence_unrestrictedHigherOrder

/-- The `.theoremBlocked` tag on the full-capture row is backed by the indexed evidence, not
asserted. -/
theorem hoPolicyRowStatus_fullCapture_is_evidence_backed :
    hoPolicyRowStatus .fullCapture = .theoremBlocked ∧ HOPolicyRowEvidence .fullCapture :=
  ⟨hoPolicyRowStatus_fullCapture, hoPolicyRowEvidence_fullCapture⟩

/-- Data record whose requirements are the fields displayed below. -/
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
  decidableClassifierRowEvidence : HigherOrderDecidableClassifierCatalog
  captureDecisionRowEvidence : HigherOrderCaptureDecidableCatalog
  fullCaptureRowEvidence : FullCaptureSemanticsStatus
  unrestrictedHigherOrderRowEvidence : ¬ UnqualifiedHigherOrderRewritingLiftClaim

/-- The displayed proposition follows from the stated hypotheses. -/
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
  · exact higher_order_decidable_classifier_catalog
  · exact higher_order_capture_decidable_catalog
  · exact full_capture_semantics_exact_boundary
  · exact shared_policy_blocks_unqualified_higher_order_rewriting_lift

end OperatorKO7.HigherOrderRewritingPolicyAudit
