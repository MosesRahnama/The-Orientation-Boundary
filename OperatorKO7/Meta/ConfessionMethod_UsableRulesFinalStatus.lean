import OperatorKO7.Meta.ConfessionMethod_UsableRulesBridgeAttempt

/-!
# Confession Method Usable-Rules Final Status

This module records the final theorem-facing S5 usable-rules status honestly.

The live tree now contains a concrete verified usable-rules bridge and a
theorem-backed honest fifth route. The earlier unavailable rows are retained as
historical, superseded status rows rather than erased.
-/

namespace OperatorKO7.Meta.ConfessionMethodUsableRulesFinalStatus

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.ConfessionMethodUniversalUsableRules
open OperatorKO7.Meta.ConfessionMethodUsableRulesBridgeAttempt

inductive UsableRulesFinalStatusKind where
  | concreteCandidateAvailable
  | conditionalUniversalWrapperAvailable
  | obstructionRecorded
  | verifiedBridgeUnavailable
  | verifiedBridgeAvailable
  | verifiedUniversalAdmissionUnavailable
  | verifiedUniversalAdmissionAvailable
  | honestFifthRouteUnavailable
  | honestFifthRouteAvailable
  deriving DecidableEq, Repr

inductive UsableRulesFinalStatusRowId where
  | concreteCandidate
  | conditionalUniversalWrapper
  | obstruction
  | verifiedBridgeHistorical
  | verifiedBridge
  | verifiedUniversalAdmissionHistorical
  | verifiedUniversalAdmission
  | honestFifthRouteHistorical
  | honestFifthRoute
  deriving DecidableEq, Repr

def usableRules_final_status_kind :
    UsableRulesFinalStatusRowId → UsableRulesFinalStatusKind
  | .concreteCandidate => .concreteCandidateAvailable
  | .conditionalUniversalWrapper => .conditionalUniversalWrapperAvailable
  | .obstruction => .obstructionRecorded
  | .verifiedBridgeHistorical => .verifiedBridgeUnavailable
  | .verifiedBridge => .verifiedBridgeAvailable
  | .verifiedUniversalAdmissionHistorical => .verifiedUniversalAdmissionUnavailable
  | .verifiedUniversalAdmission => .verifiedUniversalAdmissionAvailable
  | .honestFifthRouteHistorical => .honestFifthRouteUnavailable
  | .honestFifthRoute => .honestFifthRouteAvailable

def usableRules_final_status_label : UsableRulesFinalStatusRowId → String
  | .concreteCandidate => "Concrete usable-rules candidate"
  | .conditionalUniversalWrapper => "Conditional universal usable-rules wrapper"
  | .obstruction => "Usable-rules obstruction record"
  | .verifiedBridgeHistorical => "Verified usable-rules bridge (historical unavailable row; superseded)"
  | .verifiedBridge => "Verified usable-rules bridge"
  | .verifiedUniversalAdmissionHistorical =>
      "Verified usable-rules universal admission (historical unavailable row; superseded)"
  | .verifiedUniversalAdmission => "Verified usable-rules universal admission"
  | .honestFifthRouteHistorical =>
      "Honest fifth-route availability (historical unavailable row; superseded)"
  | .honestFifthRoute => "Honest fifth-route availability"

structure UsableRulesFinalStatusRow where
  id : UsableRulesFinalStatusRowId
  label : String
  kind : UsableRulesFinalStatusKind
  deriving DecidableEq, Repr

def usableRules_final_status_row
    (rowId : UsableRulesFinalStatusRowId) : UsableRulesFinalStatusRow :=
  {
    id := rowId
    label := usableRules_final_status_label rowId
    kind := usableRules_final_status_kind rowId
  }

def usableRules_final_status_rows : List UsableRulesFinalStatusRow :=
  [usableRules_final_status_row .concreteCandidate,
    usableRules_final_status_row .conditionalUniversalWrapper,
    usableRules_final_status_row .obstruction,
    usableRules_final_status_row .verifiedBridgeHistorical,
    usableRules_final_status_row .verifiedBridge,
    usableRules_final_status_row .verifiedUniversalAdmissionHistorical,
    usableRules_final_status_row .verifiedUniversalAdmission,
    usableRules_final_status_row .honestFifthRouteHistorical,
    usableRules_final_status_row .honestFifthRoute]

structure UsableRulesFinalStatusCatalog : Type 1 where
  rows : List UsableRulesFinalStatusRow
  closeoutBoundary : UsableRulesRouteCloseoutBoundary
  obstruction : UsableRulesSoundnessBridgeObstruction
  bridgeAttempt : UsableRulesSoundnessBridgeAttempt
  rows_exact : rows = usableRules_final_status_rows

noncomputable def usableRules_final_status_catalog : UsableRulesFinalStatusCatalog where
  rows := usableRules_final_status_rows
  closeoutBoundary := usableRulesRouteCloseoutBoundary
  obstruction := usableRulesSoundnessBridgeObstruction
  bridgeAttempt := usableRulesSoundnessBridgeAttemptResult
  rows_exact := rfl

def UsableRulesFinalStatusCatalog.HasRow
    (catalog : UsableRulesFinalStatusCatalog)
    (rowId : UsableRulesFinalStatusRowId)
    (kind : UsableRulesFinalStatusKind) : Prop :=
  ∃ row ∈ catalog.rows, row.id = rowId ∧ row.kind = kind

theorem usableRules_final_status_catalog_rows_exact :
    usableRules_final_status_catalog.rows = usableRules_final_status_rows :=
  usableRules_final_status_catalog.rows_exact

private theorem usableRules_final_status_catalog_covers_row
    (rowId : UsableRulesFinalStatusRowId) :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      rowId
      (usableRules_final_status_kind rowId) := by
  refine ⟨usableRules_final_status_row rowId, ?_, rfl, rfl⟩
  cases rowId <;>
    simp [usableRules_final_status_catalog, usableRules_final_status_rows,
      usableRules_final_status_row,
      usableRules_final_status_label, usableRules_final_status_kind]

theorem usableRules_final_status_catalog_covers_candidate :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .concreteCandidate
      .concreteCandidateAvailable :=
  usableRules_final_status_catalog_covers_row .concreteCandidate

theorem usableRules_final_status_catalog_marks_conditionalUniversalWrapper_available :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .conditionalUniversalWrapper
      .conditionalUniversalWrapperAvailable :=
  usableRules_final_status_catalog_covers_row .conditionalUniversalWrapper

theorem usableRules_final_status_catalog_marks_obstruction_recorded :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .obstruction
      .obstructionRecorded :=
  usableRules_final_status_catalog_covers_row .obstruction

theorem usableRules_final_status_catalog_marks_verifiedBridge_unavailable :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .verifiedBridgeHistorical
      .verifiedBridgeUnavailable :=
  usableRules_final_status_catalog_covers_row .verifiedBridgeHistorical

theorem usableRules_final_status_catalog_marks_verifiedBridge_available :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .verifiedBridge
      .verifiedBridgeAvailable :=
  usableRules_final_status_catalog_covers_row .verifiedBridge

theorem usableRules_final_status_catalog_marks_verifiedUniversalAdmission_unavailable :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .verifiedUniversalAdmissionHistorical
      .verifiedUniversalAdmissionUnavailable :=
  usableRules_final_status_catalog_covers_row .verifiedUniversalAdmissionHistorical

theorem usableRules_final_status_catalog_marks_verifiedUniversalAdmission_available :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .verifiedUniversalAdmission
      .verifiedUniversalAdmissionAvailable :=
  usableRules_final_status_catalog_covers_row .verifiedUniversalAdmission

theorem usableRules_final_status_catalog_marks_honestFifthRoute_unavailable :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .honestFifthRouteHistorical
      .honestFifthRouteUnavailable :=
  usableRules_final_status_catalog_covers_row .honestFifthRouteHistorical

theorem usableRules_final_status_catalog_marks_honestFifthRoute_available :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .honestFifthRoute
      .honestFifthRouteAvailable :=
  usableRules_final_status_catalog_covers_row .honestFifthRoute

theorem usableRules_final_status_catalog_projects_candidate :
    usableRules_final_status_catalog.closeoutBoundary.candidate =
      usableRulesConcreteRouteCandidate :=
  rfl

theorem usableRules_final_status_catalog_projects_route_agreement :
    usableRules_final_status_catalog.closeoutBoundary.candidate.toRouteEvidence
        usableRules_final_status_catalog.closeoutBoundary.candidate.witness =
      confessionRouteConvergencePackage.commonRouteEvidence :=
  usableRules_final_status_catalog.closeoutBoundary.availableRouteAgreement

theorem usableRules_final_status_catalog_projects_forgetting_rank :
    (ForgettingWitness.ofRouteEvidence
      (usableRules_final_status_catalog.closeoutBoundary.candidate.toRouteEvidence
        usableRules_final_status_catalog.closeoutBoundary.candidate.witness)).rank =
      dpConfession.rank :=
  usableRules_final_status_catalog.closeoutBoundary.availableForgettingRankAgreement

def usableRules_final_status_catalog_projects_conditionalResidualPackage
    (B : ConcreteUsableRulesBridgeWitness) :
    UsableRulesConfessionRouteResidualObligation :=
  usableRulesConcreteCandidateResidual B

def usableRules_final_status_catalog_projects_conditionalUniversalWrapper
    (B : ConcreteUsableRulesBridgeWitness) :
    ConditionalUsableRulesUniversalInstance :=
  usableRulesConcreteCandidateConditionalInstance B

theorem usableRules_final_status_catalog_projects_conditionalUniversalAdmission_iff_bridgeWitnessed :
    Nonempty ConcreteUsableRulesUniversalAdmission ↔
      Nonempty ConcreteUsableRulesBridgeWitness :=
  usableRulesUniversal_iff_soundnessBridgeWitnessed

theorem usableRules_final_status_catalog_projects_verifiedUniversalAdmission_iff_verifiedBridgeWitnessed :
    Nonempty VerifiedConcreteUsableRulesUniversalAdmission ↔
      ∃ bridge : ConcreteUsableRulesBridgeWitness, bridge.certification.IsVerified :=
  verifiedUsableRulesUniversalAdmission_iff_verifiedSoundnessBridgeWitnessed

theorem usableRules_final_status_catalog_projects_verifiedUniversalAdmission_iff_nonempty_verifiedBridgeWitness :
    Nonempty VerifiedConcreteUsableRulesUniversalAdmission ↔
      Nonempty { bridge : ConcreteUsableRulesBridgeWitness // bridge.certification.IsVerified } := by
  constructor
  · intro h
    rcases (usableRules_final_status_catalog_projects_verifiedUniversalAdmission_iff_verifiedBridgeWitnessed).1 h with
      ⟨bridge, hVerified⟩
    exact ⟨⟨bridge, hVerified⟩⟩
  · intro h
    rcases h with ⟨⟨bridge, hVerified⟩⟩
    exact (usableRules_final_status_catalog_projects_verifiedUniversalAdmission_iff_verifiedBridgeWitnessed).2
      ⟨bridge, hVerified⟩

noncomputable def usableRules_final_status_catalog_projects_verifiedBridge :
    { bridge : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate //
      bridge.certification.IsVerified } := by
  simpa [usableRules_final_status_catalog, usableRulesRouteCloseoutBoundary]
    using usableRules_final_status_catalog.closeoutBoundary.verifiedBridge

theorem usableRules_final_status_catalog_projects_verifiedBridgeWitness :
    Nonempty { bridge : ConcreteUsableRulesBridgeWitness // bridge.certification.IsVerified } := by
  exact ⟨by
    simpa [ConcreteUsableRulesBridgeWitness] using
      usableRules_final_status_catalog_projects_verifiedBridge⟩

theorem usableRules_final_status_catalog_projects_dischargedBridgeObligations :
    usableRules_final_status_catalog.closeoutBoundary.dischargedBridgeObligations =
      [UsableRulesBridgeObligation.routeLocalWitnessField,
        UsableRulesBridgeObligation.standaloneSoundnessTheorem] :=
  usableRulesRouteCloseoutBoundary_projects_dischargedBridgeObligations

noncomputable def usableRules_final_status_catalog_projects_verifiedUniversalAdmission :
    VerifiedConcreteUsableRulesUniversalAdmission :=
  usableRules_final_status_catalog.closeoutBoundary.verifiedUniversalAdmission

theorem usableRules_final_status_catalog_projects_verifiedUniversalAdmission_iff_verifiedBridgeWitness :
    Nonempty VerifiedConcreteUsableRulesUniversalAdmission ↔
      Nonempty { bridge : ConcreteUsableRulesBridgeWitness // bridge.certification.IsVerified } := by
  constructor
  · intro _
    exact usableRules_final_status_catalog_projects_verifiedBridgeWitness
  · intro _
    exact ⟨usableRules_final_status_catalog_projects_verifiedUniversalAdmission⟩

theorem usableRules_final_status_catalog_projects_honestFifthRoute :
    HasUsableRulesConfessionRoute :=
  usableRules_final_status_catalog.closeoutBoundary.honestUsableRulesRoute

abbrev UsableRulesS5CurrentCarrierClosure : Prop :=
  Nonempty UsableRulesRouteLocalWitnessField
    ∧ UsableRulesStandaloneSoundnessTheorem
    ∧ Nonempty { bridge : ConcreteUsableRulesBridgeWitness // bridge.certification.IsVerified }
    ∧ Nonempty VerifiedConcreteUsableRulesUniversalAdmission
    ∧ HasUsableRulesConfessionRoute

theorem usableRules_final_status_catalog_projects_currentCarrierClosure :
    UsableRulesS5CurrentCarrierClosure := by
  exact ⟨usableRulesRouteLocalWitnessField_inhabited,
    usableRulesConcreteStandaloneSoundnessTheorem,
    usableRules_final_status_catalog_projects_verifiedBridgeWitness,
    ⟨usableRules_final_status_catalog_projects_verifiedUniversalAdmission⟩,
    usableRules_final_status_catalog_projects_honestFifthRoute⟩

theorem usableRules_final_status_catalog_projects_verifiedBridgeAttempt :
    usableRules_final_status_catalog.bridgeAttempt =
      UsableRulesSoundnessBridgeAttempt.witnessed
        concreteUsableRulesBridgeWitness :=
  rfl

abbrev UsableRulesS5ExactCloseout : Prop :=
  Nonempty UsableRulesConcreteRouteCandidate
    ∧ (Nonempty ConcreteUsableRulesUniversalAdmission ↔
        Nonempty ConcreteUsableRulesBridgeWitness)
    ∧ Nonempty UsableRulesSoundnessBridgeObstruction
    ∧ Nonempty { bridge : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate //
        bridge.certification.IsVerified }
    ∧ Nonempty VerifiedConcreteUsableRulesUniversalAdmission
    ∧ HasUsableRulesConfessionRoute

theorem usableRules_s5_final_status_closes_as_verified_fifthRoute :
    UsableRulesS5ExactCloseout := by
  refine ⟨⟨usableRulesConcreteRouteCandidate⟩,
    usableRules_final_status_catalog_projects_conditionalUniversalAdmission_iff_bridgeWitnessed,
    ⟨usableRules_final_status_catalog.obstruction⟩,
    ⟨usableRules_final_status_catalog_projects_verifiedBridge⟩,
    ⟨usableRules_final_status_catalog_projects_verifiedUniversalAdmission⟩,
    usableRules_final_status_catalog_projects_honestFifthRoute⟩

theorem usableRules_s5_current_carrier_closes_as_verified_bridge :
    UsableRulesS5CurrentCarrierClosure :=
  usableRules_final_status_catalog_projects_currentCarrierClosure

end OperatorKO7.Meta.ConfessionMethodUsableRulesFinalStatus
