import OperatorKO7.Meta.ConfessionMethod_UsableRulesFinalStatus

namespace ConfessionMethodUsableRulesFinalStatusReach

open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.ConfessionMethodUniversalUsableRules
open OperatorKO7.Meta.ConfessionMethodUsableRulesBridgeAttempt
open OperatorKO7.Meta.ConfessionMethodUsableRulesFinalStatus

#check UsableRulesFinalStatusKind
#check UsableRulesFinalStatusRowId
#check UsableRulesFinalStatusRow
#check usableRules_final_status_kind
#check usableRules_final_status_label
#check usableRules_final_status_row
#check usableRules_final_status_rows
#check UsableRulesFinalStatusCatalog
#check usableRules_final_status_catalog
#check UsableRulesFinalStatusCatalog.HasRow
#check usableRules_final_status_catalog_rows_exact
#check usableRules_final_status_rows_length
#check usableRules_final_status_catalog_covers_candidate
#check usableRules_final_status_catalog_marks_universalWrapper_available
#check usableRules_final_status_catalog_marks_historicalDiagnostic_recorded
#check usableRules_final_status_catalog_marks_verifiedBridge_available
#check usableRules_final_status_catalog_marks_theoremBackedFifthRoute_available
#check usableRules_final_status_catalog_projects_candidate
#check usableRules_final_status_catalog_projects_route_agreement
#check usableRules_final_status_catalog_projects_forgetting_rank
#check usableRules_final_status_catalog_projects_residualPackage
#check usableRules_final_status_catalog_projects_universalWrapper
#check usableRules_final_status_catalog_projects_universalAdmission
#check usableRules_final_status_catalog_projects_bridgeWitnessed
#check usableRules_final_status_catalog_projects_historicalDiagnostic
#check usableRules_final_status_catalog_projects_witnessedBridgeAttempt
#check UsableRulesS5FullClosure
#check usableRules_s5_full_closure

example :
    usableRules_final_status_catalog.rows = usableRules_final_status_rows :=
  usableRules_final_status_catalog_rows_exact

example : usableRules_final_status_rows.length = 5 :=
  usableRules_final_status_rows_length

example :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .concreteCandidate
      .concreteCandidateAvailable :=
  usableRules_final_status_catalog_covers_candidate

example :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .universalWrapper
      .universalWrapperAvailable :=
  usableRules_final_status_catalog_marks_universalWrapper_available

example :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .historicalDiagnostic
      .historicalDiagnosticRecorded :=
  usableRules_final_status_catalog_marks_historicalDiagnostic_recorded

example :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .verifiedBridge
      .verifiedBridgeAvailable :=
  usableRules_final_status_catalog_marks_verifiedBridge_available

example :
    UsableRulesFinalStatusCatalog.HasRow
      usableRules_final_status_catalog
      .theoremBackedFifthRoute
      .theoremBackedFifthRouteAvailable :=
  usableRules_final_status_catalog_marks_theoremBackedFifthRoute_available

example :
    usableRules_final_status_catalog.boundaryCatalog.candidate =
      usableRulesConcreteRouteCandidate :=
  usableRules_final_status_catalog_projects_candidate

example :
    usableRules_final_status_catalog.boundaryCatalog.candidate.toRouteEvidence
        usableRules_final_status_catalog.boundaryCatalog.candidate.witness =
      confessionRouteConvergencePackage.commonRouteEvidence :=
  usableRules_final_status_catalog_projects_route_agreement

example :
    (OperatorKO7.StepDuplicating.StepDuplicatingSchema.ForgettingWitness.ofRouteEvidence
      (usableRules_final_status_catalog.boundaryCatalog.candidate.toRouteEvidence
        usableRules_final_status_catalog.boundaryCatalog.candidate.witness)).rank =
      dpConfession.rank :=
  usableRules_final_status_catalog_projects_forgetting_rank

example : UsableRulesConfessionRouteResidualObligation :=
  usableRules_final_status_catalog_projects_residualPackage

example : UsableRulesUniversalInstance :=
  usableRules_final_status_catalog_projects_universalWrapper

example : Nonempty ConcreteUsableRulesUniversalAdmission :=
  usableRules_final_status_catalog_projects_universalAdmission

example : Nonempty ConcreteUsableRulesBridgeWitness :=
  usableRules_final_status_catalog_projects_bridgeWitnessed

example :
    usableRules_final_status_catalog.bridgeAttempt =
      UsableRulesSoundnessBridgeAttempt.witnessed
        concreteUsableRulesBridgeWitness :=
  usableRules_final_status_catalog_projects_witnessedBridgeAttempt

example : UsableRulesS5FullClosure :=
  usableRules_s5_full_closure

end ConfessionMethodUsableRulesFinalStatusReach
