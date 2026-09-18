import OperatorKO7.Meta.ConfessionMethod_UsableRulesBridgeAttempt

/-!
# Confession Method Usable-Rules Closure Status

This module records the fully closed five-row usable-rules surface.  The
canonical candidate, source-termination bridge, universal wrapper, and fifth
route are all inhabited.  Historical obstruction data are retained only as a
diagnostic account of narrower construction attempts and are not the live
status of the route.
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
  | universalWrapperAvailable
  | historicalDiagnosticRecorded
  | verifiedBridgeAvailable
  | theoremBackedFifthRouteAvailable
  deriving DecidableEq, Repr

inductive UsableRulesFinalStatusRowId where
  | concreteCandidate
  | universalWrapper
  | historicalDiagnostic
  | verifiedBridge
  | theoremBackedFifthRoute
  deriving DecidableEq, Repr

def usableRules_final_status_kind :
    UsableRulesFinalStatusRowId → UsableRulesFinalStatusKind
  | .concreteCandidate => .concreteCandidateAvailable
  | .universalWrapper => .universalWrapperAvailable
  | .historicalDiagnostic => .historicalDiagnosticRecorded
  | .verifiedBridge => .verifiedBridgeAvailable
  | .theoremBackedFifthRoute => .theoremBackedFifthRouteAvailable

def usableRules_final_status_label : UsableRulesFinalStatusRowId → String
  | .concreteCandidate => "Concrete usable-rules candidate"
  | .universalWrapper => "Universal usable-rules wrapper"
  | .historicalDiagnostic => "Historical usable-rules construction diagnostic"
  | .verifiedBridge => "Verified usable-rules bridge"
  | .theoremBackedFifthRoute => "Theorem-backed fifth confession route"

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
    usableRules_final_status_row .universalWrapper,
    usableRules_final_status_row .historicalDiagnostic,
    usableRules_final_status_row .verifiedBridge,
    usableRules_final_status_row .theoremBackedFifthRoute]

structure UsableRulesFinalStatusCatalog : Type 1 where
  rows : List UsableRulesFinalStatusRow
  boundaryCatalog : UsableRulesConcreteRouteBoundaryCatalog
  bridge : ConcreteUsableRulesBridgeWitness
  universalAdmission : ConcreteUsableRulesUniversalAdmission
  historicalDiagnostic : UsableRulesSoundnessBridgeObstruction
  bridgeAttempt : UsableRulesSoundnessBridgeAttempt
  rows_exact : rows = usableRules_final_status_rows

def usableRules_final_status_catalog : UsableRulesFinalStatusCatalog where
  rows := usableRules_final_status_rows
  boundaryCatalog := usableRulesConcreteRouteBoundaryCatalog
  bridge := concreteUsableRulesBridgeWitness
  universalAdmission := concreteUsableRulesUniversalAdmission
  historicalDiagnostic := usableRulesSoundnessBridgeObstruction
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

theorem usableRules_final_status_rows_length :
    usableRules_final_status_rows.length = 5 := by
  rfl

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

theorem usableRules_final_status_catalog_marks_universalWrapper_available :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .universalWrapper
      .universalWrapperAvailable :=
  usableRules_final_status_catalog_covers_row .universalWrapper

theorem usableRules_final_status_catalog_marks_historicalDiagnostic_recorded :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .historicalDiagnostic
      .historicalDiagnosticRecorded :=
  usableRules_final_status_catalog_covers_row .historicalDiagnostic

theorem usableRules_final_status_catalog_marks_verifiedBridge_available :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .verifiedBridge
      .verifiedBridgeAvailable :=
  usableRules_final_status_catalog_covers_row .verifiedBridge

theorem usableRules_final_status_catalog_marks_theoremBackedFifthRoute_available :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .theoremBackedFifthRoute
      .theoremBackedFifthRouteAvailable :=
  usableRules_final_status_catalog_covers_row .theoremBackedFifthRoute

theorem usableRules_final_status_catalog_projects_candidate :
    usableRules_final_status_catalog.boundaryCatalog.candidate =
      usableRulesConcreteRouteCandidate :=
  rfl

theorem usableRules_final_status_catalog_projects_route_agreement :
    usableRules_final_status_catalog.boundaryCatalog.candidate.toRouteEvidence
        usableRules_final_status_catalog.boundaryCatalog.candidate.witness =
      confessionRouteConvergencePackage.commonRouteEvidence :=
  usableRulesConcreteRouteCandidate_projects_family_route_agreement
    usableRules_final_status_catalog.boundaryCatalog.candidate

theorem usableRules_final_status_catalog_projects_forgetting_rank :
    (ForgettingWitness.ofRouteEvidence
      (usableRules_final_status_catalog.boundaryCatalog.candidate.toRouteEvidence
        usableRules_final_status_catalog.boundaryCatalog.candidate.witness)).rank =
      dpConfession.rank :=
  usableRulesConcreteRouteCandidate_projects_forgetting_rank
    usableRules_final_status_catalog.boundaryCatalog.candidate

/-- Closed residual package projected from the catalog bridge. -/
def usableRules_final_status_catalog_projects_residualPackage :
    UsableRulesConfessionRouteResidualObligation :=
  usableRulesConcreteCandidateResidual
    usableRules_final_status_catalog.bridge

/-- Closed universal wrapper projected from the catalog. -/
def usableRules_final_status_catalog_projects_universalWrapper :
    UsableRulesUniversalInstance :=
  usableRulesConcreteCandidateConditionalInstance
    usableRules_final_status_catalog.bridge

/-- The catalog contains an inhabited universal admission. -/
theorem usableRules_final_status_catalog_projects_universalAdmission :
    Nonempty ConcreteUsableRulesUniversalAdmission :=
  ⟨usableRules_final_status_catalog.universalAdmission⟩

/-- The catalog contains an inhabited source-soundness bridge. -/
theorem usableRules_final_status_catalog_projects_bridgeWitnessed :
    Nonempty ConcreteUsableRulesBridgeWitness :=
  ⟨usableRules_final_status_catalog.bridge⟩

/-- Historical diagnostic data do not control the live route status. -/
theorem usableRules_final_status_catalog_projects_historicalDiagnostic :
    usableRules_final_status_catalog.historicalDiagnostic =
      usableRulesSoundnessBridgeObstruction :=
  rfl

/-- The live bridge-attempt result is witnessed. -/
theorem usableRules_final_status_catalog_projects_witnessedBridgeAttempt :
    usableRules_final_status_catalog.bridgeAttempt =
      UsableRulesSoundnessBridgeAttempt.witnessed
        concreteUsableRulesBridgeWitness :=
  rfl

/-- Fully closed S5 usable-rules package. -/
abbrev UsableRulesS5FullClosure : Prop :=
  Nonempty UsableRulesConcreteRouteCandidate
    ∧ Nonempty ConcreteUsableRulesBridgeWitness
    ∧ Nonempty ConcreteUsableRulesUniversalAdmission
    ∧ HasUsableRulesConfessionRoute
    ∧ usableRulesSoundnessBridgeAttemptResult =
        UsableRulesSoundnessBridgeAttempt.witnessed
          concreteUsableRulesBridgeWitness

/-- Unconditional closeout theorem for the fifth confession route. -/
theorem usableRules_s5_full_closure : UsableRulesS5FullClosure := by
  exact ⟨⟨usableRulesConcreteRouteCandidate⟩,
    ⟨concreteUsableRulesBridgeWitness⟩,
    concreteUsableRulesUniversalAdmission_inhabited,
    usableRules_fifth_route_closed,
    usableRulesSoundnessBridgeAttemptResult_witnessed⟩

end OperatorKO7.Meta.ConfessionMethodUsableRulesFinalStatus
