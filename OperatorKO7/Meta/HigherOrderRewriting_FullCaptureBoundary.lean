import OperatorKO7.Meta.HigherOrderRewriting_CaptureDecidable

/-!
# Higher-Order Rewriting Full-Capture Boundary

This module closes the current full-capture row at the theorem-visible boundary
level. It records the exact requirement rows for a stronger full-capture claim,
packages the certified-fragment interfaces already proved by Lean, and routes
the orientation side into the existing shared-policy blocker.
-/

namespace OperatorKO7.HigherOrderRewritingFullCaptureBoundary

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBoundary
open OperatorKO7.HigherOrderRewritingBetaBinder
open OperatorKO7.HigherOrderRewritingCaptureSubfamilies
open OperatorKO7.HigherOrderRewritingDecidableClassifications
open OperatorKO7.HigherOrderRewritingCaptureDecidable

/-- Finite requirement rows for the current full-capture boundary. -/
inductive FullCaptureBoundaryRow
  | syntaxCarrier
  | substitutionSemantics
  | captureAvoidanceLaw
  | sharingPolicy
  | orientationInterface
  | blockerTransport
  | certifiedFragmentSuccess
  deriving DecidableEq, Repr

/-- Finite status labels for the current full-capture boundary rows. -/
inductive FullCaptureBoundaryRowStatus
  | theoremCovered
  | theoremBlocked
  | typedBoundary
  | certifiedFragment
  deriving DecidableEq, Repr

/-- Canonical finite list of the current full-capture boundary rows. -/
def fullCaptureBoundaryRows : List FullCaptureBoundaryRow :=
  [ .syntaxCarrier
  , .substitutionSemantics
  , .captureAvoidanceLaw
  , .sharingPolicy
  , .orientationInterface
  , .blockerTransport
  , .certifiedFragmentSuccess
  ]

/-- Status projection for the current full-capture boundary rows. -/
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

/-- Concrete substitution semantics available on the present theorem surface. -/
def binderAwareSubstitutionSemantics : Nat → HOTerm → HOTerm → HOTerm :=
  binderAwareSubstitute

/-- Hypothetical capture-avoidance law required to upgrade the current exact fragment into a
full capture semantics package. -/
abbrev FullCaptureAvoidanceLaw : Prop :=
  ∀ {name binderName : Nat} {arg body : HOTerm},
    BinderAwareSubstitutionObligation name binderName arg body →
      FreshFor binderName (binderAwareSubstitute name arg body)

/-- Strongest honest upgrade on the live substitution semantics: preserving binder freshness
also requires the input body to already be fresh for that binder name. -/
abbrev FullCaptureAvoidanceLawUpstreamObligation : Prop :=
  ∀ {name binderName : Nat} {arg body : HOTerm},
    BinderAwareSubstitutionObligation name binderName arg body →
      FreshFor binderName body →
        FreshFor binderName (binderAwareSubstitute name arg body)

/-- The current substitution semantics proves the body-fresh version of the full-capture law. -/
theorem fullCaptureAvoidanceLaw_requiresBodyFreshness :
    FullCaptureAvoidanceLawUpstreamObligation := by
  intro name binderName arg body h hBodyFresh
  exact binderAwareSubstitute_preserves_freshness h.freshArgument hBodyFresh

/-- The present full-capture law is false on the live definitions: unrelated free uses of the
tracked binder name in the body survive substitution unchanged. -/
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

/-- The exact full-capture law remains blocked until the theorem surface adds a body-freshness
side condition or changes the substitution semantics. -/
theorem fullCaptureAvoidanceLaw_blocked :
    ¬ FullCaptureAvoidanceLaw := by
  intro hLaw
  rcases fullCaptureAvoidanceLaw_counterexample with
    ⟨name, binderName, arg, body, hObligation, hNotFresh⟩
  exact hNotFresh <|
    hLaw (name := name) (binderName := binderName) (arg := arg) (body := body) hObligation

/-- Exact certified-fragment success interface already supported by the executable checker. -/
abbrev FullCaptureCertifiedFragmentSuccessInterface : Prop :=
  ∀ {name binderName : Nat} {arg body : HOTerm},
    binderName ≠ name → FreshFor binderName arg →
      BinderFreeHOTerm arg → ShareFreeHOTerm arg →
      BinderFreeHOTerm body → ShareFreeHOTerm body →
        ∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert

/-- Exact target interface that would be needed to claim a full higher-order capture package. -/
structure FullCaptureTargetInterface : Prop where
  syntaxCarrier : Nonempty HOTerm
  substitutionSemantics : Nonempty (Nat → HOTerm → HOTerm → HOTerm)
  captureAvoidanceLaw : FullCaptureAvoidanceLaw
  sharingPolicy : PolicyOrientsStep sharedPolicy
  orientationInterface : UnqualifiedHigherOrderRewritingLiftClaim
  certifiedFragmentSuccess : FullCaptureCertifiedFragmentSuccessInterface

/-- The syntax carrier needed for the full-capture row is already present. -/
theorem full_capture_syntax_carrier : Nonempty HOTerm :=
  ⟨HOTerm.atom⟩

/-- The current theorem surface already fixes a concrete binder-aware substitution semantics. -/
theorem full_capture_substitution_semantics :
    Nonempty (Nat → HOTerm → HOTerm → HOTerm) :=
  ⟨binderAwareSubstitutionSemantics⟩

/-- The exact capture-safe fragment already provides the strongest preservation facts presently
available for binder-aware substitution. -/
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

/-- The executable checker already succeeds on the current certified fragment. -/
theorem binder_aware_substitution_certified_fragment_success :
    FullCaptureCertifiedFragmentSuccessInterface := by
  intro name binderName arg body hDistinct hFresh hArgBinder hArgShare hBodyBinder hBodyShare
  simpa [binderAwareSubstitutionSemantics] using
    captureSafeSubstitutionCheck_succeeds_of_binderFree_shareFree
      (name := name) (binderName := binderName) (arg := arg) (body := body)
      hDistinct hFresh hArgBinder hArgShare hBodyBinder hBodyShare

/-- The shared policy still orients a concrete higher-order rewriting branch. -/
theorem full_capture_sharing_policy_evidence :
    PolicyOrientsStep sharedPolicy :=
  shared_policy_counter_orients_step

/-- The current higher-order rewriting surface still blocks an unqualified full lift. -/
theorem full_capture_orientation_interface_blocked :
    ¬ UnqualifiedHigherOrderRewritingLiftClaim := by
  intro h
  exact h sharedPolicy shared_policy_counter_orients_step

/-- Any stronger full-capture target interface is already blocked at the capture-avoidance law
surface. -/
theorem full_capture_target_interface_blocked :
    ¬ FullCaptureTargetInterface := by
  intro h
  exact fullCaptureAvoidanceLaw_blocked h.captureAvoidanceLaw

/-- The full-capture row is now closed as an explicit typed boundary rather than open prose. -/
theorem full_capture_exact_boundary_status :
    FullCaptureSemanticsStatus :=
  capture_decision_full_capture_semantics_open

/-- Paper-facing catalog for the current full-capture boundary. -/
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

/-- Canonical catalog for the current full-capture boundary. -/
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
