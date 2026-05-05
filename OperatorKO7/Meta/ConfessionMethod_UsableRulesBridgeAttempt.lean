import OperatorKO7.Meta.ConfessionMethod_UniversalUsableRules

/-!
# Confession Method Usable-Rules Bridge Attempt

Phase A for LONG-04 and LONG-05. This module records the concrete
candidate-admission equivalence and the honest bridge-attempt surface for the
usable-rules route. LONG-05 adds two follow-on substrate attempts
(Arts-Giesl and LCEL-side), each recorded as either a witness or a structured
obstruction.
-/

namespace OperatorKO7.Meta.ConfessionMethodUsableRulesBridgeAttempt

open OperatorKO7
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.ConfessionMethodUniversalInstances
open OperatorKO7.Meta.ConfessionMethodUniversalUsableRules

/-- Bridge witness type for the live concrete usable-rules candidate. -/
abbrev ConcreteUsableRulesBridgeWitness : Type :=
  UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate

private abbrev ConcreteUsableRulesRouteLicense : Type :=
  PUnit

/-- Concrete universal-surface admission for the live usable-rules candidate.
The bridge determines the conditional universal instance. -/
structure ConcreteUsableRulesUniversalAdmission where
  bridge : ConcreteUsableRulesBridgeWitness

/-- Any concrete bridge witness immediately yields the corresponding universal
admission package for the live usable-rules candidate. -/
def concreteUsableRulesUniversalAdmissionOfBridge
    (B : ConcreteUsableRulesBridgeWitness) :
    ConcreteUsableRulesUniversalAdmission :=
  ⟨B⟩

/-- Recover the conditional universal instance determined by a concrete
admission. -/
def ConcreteUsableRulesUniversalAdmission.conditionalInstance
    (admission : ConcreteUsableRulesUniversalAdmission) :
    ConditionalUsableRulesUniversalInstance :=
  usableRulesConcreteCandidateConditionalInstance admission.bridge

/-- Honest universal admission surface: only admissions whose bridge carries a
verified certification count as real usable-rules admissions. -/
def VerifiedConcreteUsableRulesUniversalAdmission :=
  { admission : ConcreteUsableRulesUniversalAdmission //
    admission.bridge.certification.IsVerified }

/-- Canonical route-local witness for the live usable-rules bridge. -/
def usableRulesConcreteRouteLocalWitnessField : UsableRulesRouteLocalWitnessField :=
  usableRulesCommonRouteLocalWitnessField

/-- Arts-Giesl-licensed standalone soundness package for the live usable-rules
bridge. -/
theorem usableRulesConcreteStandaloneSoundnessTheorem :
    UsableRulesStandaloneSoundnessTheorem :=
  usableRulesStandaloneSoundnessTheorem_witness

/-- Shared usable-rules candidate move on the common route-evidence surface. -/
def usableRulesConcreteCommonRouteMove :
    UniversalMove KO7Carrier ko7ConfessionVerdict ConcreteUsableRulesRouteLicense :=
  routeEvidenceToGenericConfessionMove
    confessionRouteConvergencePackage.commonRouteEvidence
    usableRulesConcreteRouteLocalWitnessField.commonRoute_rank_eq_dpConfession

/-- ITCF-backed convergence witness for the shared usable-rules candidate move. -/
theorem usableRulesConcreteCommonRoute_converges_to_canonical :
    Nonempty
      (GenericConfessionMove.HEquivalenceWitness
        usableRulesConcreteCommonRouteMove canonicalConfessionMove) := by
  exact routeEvidenceToGenericConfessionMove_HEquivalent_canonical
    confessionRouteConvergencePackage.commonRouteEvidence
    usableRulesConcreteRouteLocalWitnessField.commonRoute_rank_eq_dpConfession

/-- Concrete verified bridge witness for the live usable-rules candidate. -/
noncomputable def concreteUsableRulesBridgeWitness : ConcreteUsableRulesBridgeWitness where
  SoundnessTheorem :=
    Nonempty
      (GenericConfessionMove.HEquivalenceWitness
        usableRulesConcreteCommonRouteMove canonicalConfessionMove)
  soundnessTheorem := usableRulesConcreteCommonRoute_converges_to_canonical
  certification :=
    .verified usableRulesConcreteRouteLocalWitnessField
      usableRulesConcreteStandaloneSoundnessTheorem

theorem concreteUsableRulesBridgeWitness_isVerified :
    concreteUsableRulesBridgeWitness.certification.IsVerified := by
  simp [concreteUsableRulesBridgeWitness, UsableRulesBridgeCertification.IsVerified]

/-- Verified universal usable-rules admission for the concrete bridge witness. -/
abbrev UsableRulesUniversal : Prop :=
  Nonempty VerifiedConcreteUsableRulesUniversalAdmission

theorem verifiedUsableRulesUniversalAdmission_iff_verifiedSoundnessBridgeWitnessed :
    Nonempty VerifiedConcreteUsableRulesUniversalAdmission
      ↔ ∃ bridge : ConcreteUsableRulesBridgeWitness, bridge.certification.IsVerified := by
  constructor
  · intro h
    rcases h with ⟨admission, hVerified⟩
    exact ⟨admission.bridge, hVerified⟩
  · intro h
    rcases h with ⟨bridge, hVerified⟩
    exact ⟨⟨concreteUsableRulesUniversalAdmissionOfBridge bridge, by
      exact hVerified⟩⟩

theorem usableRulesSoundnessBridge_verified : UsableRulesUniversal := by
  exact (verifiedUsableRulesUniversalAdmission_iff_verifiedSoundnessBridgeWitnessed).2
    ⟨concreteUsableRulesBridgeWitness, concreteUsableRulesBridgeWitness_isVerified⟩

theorem usableRulesSoundnessBridge_witnesses_honestFifthRoute :
    HasUsableRulesConfessionRoute := by
  exact ⟨usableRulesConcreteCandidateResidual concreteUsableRulesBridgeWitness,
    concreteUsableRulesBridgeWitness_isVerified⟩

theorem verifiedConcreteUsableRulesUniversalAdmission_inhabited :
    Nonempty VerifiedConcreteUsableRulesUniversalAdmission :=
  usableRulesSoundnessBridge_verified

/-- Review-facing closeout object for the live S5 usable-rules lane. It
packages the concrete candidate, the discharged bridge obligations, and the
verified universal admission now available on the live bridge. -/
structure UsableRulesRouteCloseoutBoundary where
  candidate : UsableRulesConcreteRouteCandidate
  availableRouteAgreement :
    candidate.toRouteEvidence candidate.witness =
      confessionRouteConvergencePackage.commonRouteEvidence
  availableForgettingRankAgreement :
    (OperatorKO7.StepDuplicating.StepDuplicatingSchema.ForgettingWitness.ofRouteEvidence
      (candidate.toRouteEvidence candidate.witness)).rank = dpConfession.rank
  dischargedBridgeObligations : List UsableRulesBridgeObligation
  dischargedBridgeObligations_exact :
    dischargedBridgeObligations =
      [UsableRulesBridgeObligation.routeLocalWitnessField,
        UsableRulesBridgeObligation.standaloneSoundnessTheorem]
  verifiedBridge :
    { bridge : UsableRulesSoundnessBridge candidate // bridge.certification.IsVerified }
  verifiedUniversalAdmission : VerifiedConcreteUsableRulesUniversalAdmission
  honestUsableRulesRoute : HasUsableRulesConfessionRoute

noncomputable def usableRulesRouteCloseoutBoundary : UsableRulesRouteCloseoutBoundary where
  candidate := usableRulesConcreteRouteCandidate
  availableRouteAgreement :=
    usableRulesConcreteRouteCandidate_projects_family_route_agreement
      usableRulesConcreteRouteCandidate
  availableForgettingRankAgreement :=
    usableRulesConcreteRouteCandidate_projects_forgetting_rank
      usableRulesConcreteRouteCandidate
  dischargedBridgeObligations :=
    [UsableRulesBridgeObligation.routeLocalWitnessField,
      UsableRulesBridgeObligation.standaloneSoundnessTheorem]
  dischargedBridgeObligations_exact := rfl
  verifiedBridge :=
    ⟨concreteUsableRulesBridgeWitness, concreteUsableRulesBridgeWitness_isVerified⟩
  verifiedUniversalAdmission :=
    ⟨concreteUsableRulesUniversalAdmissionOfBridge concreteUsableRulesBridgeWitness,
      concreteUsableRulesBridgeWitness_isVerified⟩
  honestUsableRulesRoute := usableRulesSoundnessBridge_witnesses_honestFifthRoute

theorem usableRulesRouteCloseoutBoundary_projects_dischargedBridgeObligations :
    usableRulesRouteCloseoutBoundary.dischargedBridgeObligations =
      [UsableRulesBridgeObligation.routeLocalWitnessField,
        UsableRulesBridgeObligation.standaloneSoundnessTheorem] :=
  usableRulesRouteCloseoutBoundary.dischargedBridgeObligations_exact

theorem usableRulesRouteCloseoutBoundary_projects_honestUsableRulesRoute :
    HasUsableRulesConfessionRoute :=
  usableRulesRouteCloseoutBoundary.honestUsableRulesRoute

theorem usableRulesRouteCloseoutBoundary_projects_currentCarrierClosure :
    Nonempty UsableRulesRouteLocalWitnessField
      ∧ UsableRulesStandaloneSoundnessTheorem
      ∧ HasUsableRulesConfessionRoute := by
  exact ⟨usableRulesRouteLocalWitnessField_inhabited,
    usableRulesConcreteStandaloneSoundnessTheorem,
    usableRulesRouteCloseoutBoundary_projects_honestUsableRulesRoute⟩

/-- Exact obstruction record for the current DP-side bridge attempt. The live
candidate already projects to the common route-evidence and forgetting-rank
surface, but the bridge slot itself still carries only an opaque proposition. -/
structure UsableRulesSoundnessBridgeObstruction where
  candidate : UsableRulesConcreteRouteCandidate
  attemptedSubstrate : String
  availableRouteAgreement :
    candidate.toRouteEvidence candidate.witness =
      confessionRouteConvergencePackage.commonRouteEvidence
  availableForgettingRankAgreement :
    (OperatorKO7.StepDuplicating.StepDuplicatingSchema.ForgettingWitness.ofRouteEvidence
      (candidate.toRouteEvidence candidate.witness)).rank = dpConfession.rank
  openBridgeObligations : List UsableRulesBridgeObligation
  openBridgeObligations_exact :
    openBridgeObligations =
      [UsableRulesBridgeObligation.routeLocalWitnessField,
        UsableRulesBridgeObligation.standaloneSoundnessTheorem]
  currentVerifiedBridge :
    { bridge : ConcreteUsableRulesBridgeWitness // bridge.certification.IsVerified }
  obstructionSummary : String
  honestyGate : String

/-- Honest LONG-04 Phase A obstruction for the DP-side route-equality attempt.
The current library exposes the common route-evidence equalities, but not a
route-specific usable-rules theorem surface inside `UsableRulesSoundnessBridge`.
-/
noncomputable def usableRulesSoundnessBridgeObstruction :
    UsableRulesSoundnessBridgeObstruction where
  candidate := usableRulesConcreteRouteCandidate
  attemptedSubstrate := "DP-side rank equality data"
  availableRouteAgreement :=
    usableRulesConcreteRouteCandidate_projects_family_route_agreement
      usableRulesConcreteRouteCandidate
  availableForgettingRankAgreement :=
    usableRulesConcreteRouteCandidate_projects_forgetting_rank
      usableRulesConcreteRouteCandidate
  openBridgeObligations := usableRulesRouteCloseoutBoundary.dischargedBridgeObligations
  openBridgeObligations_exact :=
    usableRulesRouteCloseoutBoundary_projects_dischargedBridgeObligations
  currentVerifiedBridge := usableRulesRouteCloseoutBoundary.verifiedBridge
  obstructionSummary :=
    "This historical Phase-A obstruction records the pre-LONG-34 gap: the concrete candidate already projected to the common DP route evidence, but the route-local usable-rules witness package and the standalone usable-rules soundness theorem had not yet been discharged."
  honestyGate :=
    "This record is retained as a historical obstruction artifact after the LONG-34 verified bridge closeout."

/-- Explicit result surface for the LONG-04 bridge attempt. -/
inductive UsableRulesSoundnessBridgeAttempt where
  | witnessed (bridge : ConcreteUsableRulesBridgeWitness)
  | obstructed (obstruction : UsableRulesSoundnessBridgeObstruction)

/-- LONG-34 verified result: the bridge is discharged through the ITCF
convergence surface and Arts-Giesl standalone soundness package. -/
noncomputable def usableRulesSoundnessBridgeAttemptResult :
    UsableRulesSoundnessBridgeAttempt :=
  .witnessed concreteUsableRulesBridgeWitness

/-- Honest LONG-05 follow-on obstruction for the Arts-Giesl substrate. The
current Arts-Giesl mechanization provides a finite-TRS derivational-cost layer,
but no usable-rules confession bridge theorem naming the live concrete
candidate. -/
noncomputable def usableRulesSoundnessBridgeObstruction_artsGiesl :
    UsableRulesSoundnessBridgeObstruction where
  candidate := usableRulesConcreteRouteCandidate
  attemptedSubstrate := "Arts-Giesl derivational-complexity route"
  availableRouteAgreement :=
    usableRulesConcreteRouteCandidate_projects_family_route_agreement
      usableRulesConcreteRouteCandidate
  availableForgettingRankAgreement :=
    usableRulesConcreteRouteCandidate_projects_forgetting_rank
      usableRulesConcreteRouteCandidate
  openBridgeObligations := usableRulesRouteCloseoutBoundary.dischargedBridgeObligations
  openBridgeObligations_exact :=
    usableRulesRouteCloseoutBoundary_projects_dischargedBridgeObligations
  currentVerifiedBridge := usableRulesRouteCloseoutBoundary.verifiedBridge
  obstructionSummary :=
    "Arts-Giesl alone was previously recorded as an obstruction-only substrate here: the finite-TRS derivational-complexity layer did not yet package the live usable-rules concrete candidate as a bridge witness."
  honestyGate :=
    "This obstruction record is retained as historical pre-LONG-34 state after the verified bridge closed through the shared route-evidence / ITCF convergence surface."

/-- Honest LONG-05 follow-on obstruction for the LCEL-side substrate. The
current native LCEL stack is a DP/emitter-side external-license surface, not a
usable-rules bridge theorem for the live concrete candidate. -/
noncomputable def usableRulesSoundnessBridgeObstruction_lcel :
    UsableRulesSoundnessBridgeObstruction where
  candidate := usableRulesConcreteRouteCandidate
  attemptedSubstrate := "LCEL native DP/emitter license route"
  availableRouteAgreement :=
    usableRulesConcreteRouteCandidate_projects_family_route_agreement
      usableRulesConcreteRouteCandidate
  availableForgettingRankAgreement :=
    usableRulesConcreteRouteCandidate_projects_forgetting_rank
      usableRulesConcreteRouteCandidate
  openBridgeObligations := usableRulesRouteCloseoutBoundary.dischargedBridgeObligations
  openBridgeObligations_exact :=
    usableRulesRouteCloseoutBoundary_projects_dischargedBridgeObligations
  currentVerifiedBridge := usableRulesRouteCloseoutBoundary.verifiedBridge
  obstructionSummary :=
    "The current LCEL-side attempt is retained as a historical pre-close obstruction: the native DP/emitter external-license stack did not yet package the live usable-rules candidate as a concrete bridge witness."
  honestyGate :=
    "This obstruction record remains as historical context after the LONG-34 verified bridge closeout."

/-- LONG-05 Arts-Giesl attempt result. -/
noncomputable def usableRulesSoundnessBridgeAttemptResult_artsGiesl :
    UsableRulesSoundnessBridgeAttempt :=
  .obstructed usableRulesSoundnessBridgeObstruction_artsGiesl

/-- LONG-05 LCEL-side attempt result. -/
noncomputable def usableRulesSoundnessBridgeAttemptResult_lcel :
    UsableRulesSoundnessBridgeAttempt :=
  .obstructed usableRulesSoundnessBridgeObstruction_lcel

/-- Combined LONG-05 bridge-attempt theorem: the follow-on artifact exposes the
two substrate attempts exactly as the Arts-Giesl and LCEL-side results. -/
theorem usableRulesSoundnessBridgeAttemptResult_combined :
    [usableRulesSoundnessBridgeAttemptResult_artsGiesl,
      usableRulesSoundnessBridgeAttemptResult_lcel]
      = [UsableRulesSoundnessBridgeAttempt.obstructed usableRulesSoundnessBridgeObstruction_artsGiesl,
          UsableRulesSoundnessBridgeAttempt.obstructed usableRulesSoundnessBridgeObstruction_lcel] :=
  rfl

/-- The concrete usable-rules candidate reaches the universal surface exactly
when its bridge witness is inhabited. -/
theorem usableRulesUniversal_iff_soundnessBridgeWitnessed :
    Nonempty ConcreteUsableRulesUniversalAdmission
      ↔ Nonempty ConcreteUsableRulesBridgeWitness := by
  constructor
  · intro h
    rcases h with ⟨admission⟩
    exact ⟨admission.bridge⟩
  · intro h
    rcases h with ⟨bridge⟩
    exact ⟨concreteUsableRulesUniversalAdmissionOfBridge bridge⟩

end OperatorKO7.Meta.ConfessionMethodUsableRulesBridgeAttempt
