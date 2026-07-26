import OperatorKO7.Meta.HigherOrderRewriting_CaptureDecidable

/-!
# Higher-Order Rewriting Full-Capture Boundary

This module records seven requirement labels and their declared statuses. It proves a body-fresh
substitution law, a counterexample to the stronger capture-avoidance proposition, success of a
binder-free and share-free checker fragment, and two obstruction propositions. The final catalog
packages those results together with an imported `FullCaptureSemanticsStatus` value.
-/

namespace OperatorKO7.HigherOrderRewritingFullCaptureBoundary

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBoundary
open OperatorKO7.HigherOrderRewritingBetaBinder
open OperatorKO7.HigherOrderRewritingCaptureSubfamilies
open OperatorKO7.HigherOrderRewritingDecidableClassifiers
open OperatorKO7.HigherOrderRewritingCaptureDecidable

/-- Seven requirement labels used by the full-capture catalog. -/
inductive FullCaptureBoundaryRow
  | syntaxCarrier
  | substitutionSemantics
  | captureAvoidanceLaw
  | sharingPolicy
  | orientationInterface
  | blockerTransport
  | certifiedFragmentSuccess
  deriving DecidableEq, Repr

/-- Status labels assigned to full-capture catalog rows. -/
inductive FullCaptureBoundaryRowStatus
  | theoremCovered
  | theoremBlocked
  | typedBoundary
  | certifiedFragment
  deriving DecidableEq, Repr

/-- Enumeration of the seven full-capture catalog rows. -/
def fullCaptureBoundaryRows : List FullCaptureBoundaryRow :=
  [ .syntaxCarrier
  , .substitutionSemantics
  , .captureAvoidanceLaw
  , .sharingPolicy
  , .orientationInterface
  , .blockerTransport
  , .certifiedFragmentSuccess
  ]

/-- Declared status for each full-capture catalog row. -/
def fullCaptureBoundaryRowStatus : FullCaptureBoundaryRow → FullCaptureBoundaryRowStatus
  | .syntaxCarrier => .theoremCovered
  | .substitutionSemantics => .theoremCovered
  | .captureAvoidanceLaw => .typedBoundary
  | .sharingPolicy => .theoremCovered
  | .orientationInterface => .theoremBlocked
  | .blockerTransport => .theoremCovered
  | .certifiedFragmentSuccess => .certifiedFragment

theorem fullCaptureBoundaryRows_length : fullCaptureBoundaryRows.length = 7 := by
  rfl

theorem fullCaptureBoundaryRows_mem_iff {row : FullCaptureBoundaryRow} :
    row ∈ fullCaptureBoundaryRows ↔
      row = .syntaxCarrier ∨
      row = .substitutionSemantics ∨
      row = .captureAvoidanceLaw ∨
      row = .sharingPolicy ∨
      row = .orientationInterface ∨
      row = .blockerTransport ∨
      row = .certifiedFragmentSuccess := by
  cases row <;> simp [fullCaptureBoundaryRows]

theorem fullCaptureBoundaryRows_nodup : fullCaptureBoundaryRows.Nodup := by
  decide

@[simp] theorem fullCaptureBoundaryRowStatus_syntaxCarrier :
    fullCaptureBoundaryRowStatus .syntaxCarrier = .theoremCovered := rfl

@[simp] theorem fullCaptureBoundaryRowStatus_substitutionSemantics :
    fullCaptureBoundaryRowStatus .substitutionSemantics = .theoremCovered := rfl

@[simp] theorem fullCaptureBoundaryRowStatus_captureAvoidanceLaw :
    fullCaptureBoundaryRowStatus .captureAvoidanceLaw = .typedBoundary := rfl

@[simp] theorem fullCaptureBoundaryRowStatus_sharingPolicy :
    fullCaptureBoundaryRowStatus .sharingPolicy = .theoremCovered := rfl

@[simp] theorem fullCaptureBoundaryRowStatus_orientationInterface :
    fullCaptureBoundaryRowStatus .orientationInterface = .theoremBlocked := rfl

@[simp] theorem fullCaptureBoundaryRowStatus_blockerTransport :
    fullCaptureBoundaryRowStatus .blockerTransport = .theoremCovered := rfl

@[simp] theorem fullCaptureBoundaryRowStatus_certifiedFragmentSuccess :
    fullCaptureBoundaryRowStatus .certifiedFragmentSuccess = .certifiedFragment := rfl

/-- Alias for `binderAwareSubstitute`. -/
def binderAwareSubstitutionSemantics : Nat → HOTerm → HOTerm → HOTerm :=
  binderAwareSubstitute

/-- Capture-avoidance proposition requiring freshness after substitution from the two fields of
`BinderAwareSubstitutionObligation`. -/
abbrev FullCaptureAvoidanceLaw : Prop :=
  ∀ {name binderName : Nat} {arg body : HOTerm},
    BinderAwareSubstitutionObligation name binderName arg body →
      FreshFor binderName (binderAwareSubstitute name arg body)

/-- Body-fresh variant of `FullCaptureAvoidanceLaw`. -/
abbrev FullCaptureAvoidanceLawUpstreamObligation : Prop :=
  ∀ {name binderName : Nat} {arg body : HOTerm},
    BinderAwareSubstitutionObligation name binderName arg body →
      FreshFor binderName body →
        FreshFor binderName (binderAwareSubstitute name arg body)

/-- Prove the body-fresh variant using `binderAwareSubstitute_preserves_freshness`. -/
theorem fullCaptureAvoidanceLaw_requiresBodyFreshness :
    FullCaptureAvoidanceLawUpstreamObligation := by
  intro name binderName arg body h hBodyFresh
  exact binderAwareSubstitute_preserves_freshness h.freshArgument hBodyFresh

/-- Counterexample where a free occurrence of the tracked binder name remains in the body. -/
theorem fullCaptureAvoidanceLaw_counterexample :
    ∃ (name binderName : Nat) (arg body : HOTerm),
      BinderAwareSubstitutionObligation name binderName arg body ∧
        ¬ FreshFor binderName (binderAwareSubstitute name arg body) := by
  refine ⟨0, 1, HOTerm.atom, HOTerm.var 1, ?_⟩
  refine ⟨?_, ?_⟩
  · exact {
      binderDistinct := by decide
      freshArgument := by simp [FreshFor, FreeVarOccurs]
    }
  · simp [FreshFor, binderAwareSubstitute, substitute, FreeVarOccurs]

/-- Refute `FullCaptureAvoidanceLaw` with `fullCaptureAvoidanceLaw_counterexample`. -/
theorem fullCaptureAvoidanceLaw_blocked :
    ¬ FullCaptureAvoidanceLaw := by
  intro hLaw
  rcases fullCaptureAvoidanceLaw_counterexample with
    ⟨name, binderName, arg, body, hObligation, hNotFresh⟩
  exact hNotFresh <|
    hLaw (name := name) (binderName := binderName) (arg := arg) (body := body) hObligation

/-- Checker-success proposition under binder-distinctness, freshness, binder-free, and share-free
premises for both argument and body. -/
abbrev FullCaptureCertifiedFragmentSuccessInterface : Prop :=
  ∀ {name binderName : Nat} {arg body : HOTerm},
    binderName ≠ name → FreshFor binderName arg →
      BinderFreeHOTerm arg → ShareFreeHOTerm arg →
      BinderFreeHOTerm body → ShareFreeHOTerm body →
        ∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert

/-- Conjunction-like interface containing syntax, substitution, capture, sharing, orientation, and
checker-success fields. -/
structure FullCaptureTargetInterface : Prop where
  syntaxCarrier : Nonempty HOTerm
  substitutionSemantics : Nonempty (Nat → HOTerm → HOTerm → HOTerm)
  captureAvoidanceLaw : FullCaptureAvoidanceLaw
  sharingPolicy : PolicyOrientsStep sharedPolicy
  orientationInterface : UnqualifiedHigherOrderRewritingLiftClaim
  certifiedFragmentSuccess : FullCaptureCertifiedFragmentSuccessInterface

/-- Inhabit `HOTerm` with `HOTerm.atom`. -/
theorem full_capture_syntax_carrier : Nonempty HOTerm :=
  ⟨HOTerm.atom⟩

/-- Inhabit the substitution-function type with `binderAwareSubstitutionSemantics`. -/
theorem full_capture_substitution_semantics :
    Nonempty (Nat → HOTerm → HOTerm → HOTerm) :=
  ⟨binderAwareSubstitutionSemantics⟩

/-- Project freshness and derive binder-free, share-free, and beta-free conclusions from a
`CaptureSafeSubstitutionObligation`. -/
theorem binder_aware_substitution_exact_capture_fragment
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    FreshFor binderName arg ∧
      BinderFreeHOTerm (binderAwareSubstitute name arg body) ∧
      ShareFreeHOTerm (binderAwareSubstitute name arg body) ∧
      BetaFreeHOTerm (binderAwareSubstitute name arg body) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact binderAwareSubstitutionObligation_requires_freshness h.binderAware
  · exact captureSafeSubstitutionObligation_preserves_binder_free h
  · exact captureSafeSubstitutionObligation_preserves_share_free h
  · exact binderFree_implies_betaFree
      (captureSafeSubstitutionObligation_preserves_binder_free h)

/-- Prove checker success under the premises of `FullCaptureCertifiedFragmentSuccessInterface`. -/
theorem binder_aware_substitution_certified_fragment_success :
    FullCaptureCertifiedFragmentSuccessInterface := by
  intro name binderName arg body hDistinct hFresh hArgBinder hArgShare hBodyBinder hBodyShare
  simpa [binderAwareSubstitutionSemantics] using
    captureSafeSubstitutionCheck_succeeds_of_binderFree_shareFree
      (name := name) (binderName := binderName) (arg := arg) (body := body)
      hDistinct hFresh hArgBinder hArgShare hBodyBinder hBodyShare

/-- Reuse `shared_policy_counter_orients_step` as a `PolicyOrientsStep` witness. -/
theorem full_capture_sharing_policy_evidence :
    PolicyOrientsStep sharedPolicy :=
  shared_policy_counter_orients_step

/-- Refute `UnqualifiedHigherOrderRewritingLiftClaim` using the shared-policy witness. -/
theorem full_capture_orientation_interface_blocked :
    ¬ UnqualifiedHigherOrderRewritingLiftClaim := by
  intro h
  exact h sharedPolicy shared_policy_counter_orients_step

/-- Refute `FullCaptureTargetInterface` through its `captureAvoidanceLaw` field. -/
theorem full_capture_target_interface_blocked :
    ¬ FullCaptureTargetInterface := by
  intro h
  exact fullCaptureAvoidanceLaw_blocked h.captureAvoidanceLaw

/-- Re-export the proved counterexample boundary status. -/
theorem full_capture_exact_boundary_status :
    FullCaptureSemanticsStatus :=
  capture_decision_full_capture_semantics_exact_boundary

/-- Record packaging row enumeration, fixture evidence, fragment results, obstructions, and status. -/
structure HigherOrderFullCaptureBoundaryCatalog : Prop where
  rowCount : fullCaptureBoundaryRows.length = 7
  membershipIff :
    ∀ {row : FullCaptureBoundaryRow},
      row ∈ fullCaptureBoundaryRows ↔
        row = .syntaxCarrier ∨
        row = .substitutionSemantics ∨
        row = .captureAvoidanceLaw ∨
        row = .sharingPolicy ∨
        row = .orientationInterface ∨
        row = .blockerTransport ∨
        row = .certifiedFragmentSuccess
  noDupRows : fullCaptureBoundaryRows.Nodup
  syntaxCarrierEvidence : Nonempty HOTerm
  substitutionSemanticsEvidence : Nonempty (Nat → HOTerm → HOTerm → HOTerm)
  exactCaptureFragment :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      CaptureSafeSubstitutionObligation name binderName arg body →
        FreshFor binderName arg ∧
          BinderFreeHOTerm (binderAwareSubstitute name arg body) ∧
          ShareFreeHOTerm (binderAwareSubstitute name arg body) ∧
          BetaFreeHOTerm (binderAwareSubstitute name arg body)
  sharingPolicyEvidence : PolicyOrientsStep sharedPolicy
  orientationInterfaceBlocked : ¬ UnqualifiedHigherOrderRewritingLiftClaim
  targetInterfaceBlocked : ¬ FullCaptureTargetInterface
  certifiedFragmentSuccess : FullCaptureCertifiedFragmentSuccessInterface
  exactBoundaryStatus : FullCaptureSemanticsStatus

/-- Populate `HigherOrderFullCaptureBoundaryCatalog` from the declarations above. -/
theorem higher_order_full_capture_boundary_catalog :
    HigherOrderFullCaptureBoundaryCatalog := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fullCaptureBoundaryRows_length
  · intro row
    exact fullCaptureBoundaryRows_mem_iff
  · exact fullCaptureBoundaryRows_nodup
  · exact full_capture_syntax_carrier
  · exact full_capture_substitution_semantics
  · intro name binderName arg body h
    exact binder_aware_substitution_exact_capture_fragment h
  · exact full_capture_sharing_policy_evidence
  · exact full_capture_orientation_interface_blocked
  · exact full_capture_target_interface_blocked
  · exact binder_aware_substitution_certified_fragment_success
  · exact full_capture_exact_boundary_status

end OperatorKO7.HigherOrderRewritingFullCaptureBoundary
