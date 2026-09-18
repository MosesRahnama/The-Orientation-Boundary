import OperatorKO7.Meta.ConfessionMethod_FutureRouteSchema
import OperatorKO7.Meta.ConfessionMethod_OptimalityBoundary
import OperatorKO7.Meta.ConfessionMethod_UsableRulesBridgeAttempt

/-!
# Confession Method Universal API

This module provides a stable import boundary for universal-confession route
identifiers, theorem identifiers, boundary records, admission criteria, and
ledger-derived status counts.
-/

namespace OperatorKO7.Meta.ConfessionMethodUniversalAPI

open OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger
open OperatorKO7.Meta.ConfessionMethodOptimalityBoundary
open OperatorKO7.Meta.ConfessionMethodFutureRouteSchema
open OperatorKO7.Meta.ConfessionMethodUsableRulesBridgeAttempt

/-- API alias for universal-confession route identifiers. -/
abbrev UniversalRouteId : Type :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalRouteId

/-- API alias for universal-confession route statuses. -/
abbrev UniversalRouteStatus : Type :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalRouteStatus

/-- API alias for universal-confession theorem identifiers. -/
abbrev UniversalTheoremId : Type :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremId

/-- API alias for universal-confession theorem statuses. -/
abbrev UniversalTheoremStatus : Type :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremStatus

namespace UniversalTheoremStatus

/-- API alias for an unconditionally theorem-projected entry. -/
abbrev theoremProjected : UniversalTheoremStatus :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremStatus.theoremProjected

/-- API alias for an entry conditional on an optimality payload. -/
abbrev conditionalOnOptimalityPayload : UniversalTheoremStatus :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremStatus.conditionalOnOptimalityPayload

/-- API alias for an entry conditional on an information payload. -/
abbrev conditionalOnInformationPayload : UniversalTheoremStatus :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremStatus.conditionalOnInformationPayload

/-- API alias for an entry conditional on information and Landauer payloads. -/
abbrev conditionalOnInformationAndLandauerPayload : UniversalTheoremStatus :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremStatus.conditionalOnInformationAndLandauerPayload

end UniversalTheoremStatus

/-- API alias for optional supporting-module tags in theorem-boundary entries. -/
abbrev SupportingPhaseModule : Type :=
  OperatorKO7.Meta.ConfessionMethodOptimalityBoundary.SupportingPhaseModule

/-- API alias for the proof-bearing input vocabulary documented by the theorem ledger. -/
abbrev UniversalBoundaryHypothesis : Type :=
  OperatorKO7.Meta.ConfessionMethodOptimalityBoundary.UniversalBoundaryHypothesis

/-- API alias for one theorem-boundary entry. -/
abbrev OptimalityBoundaryEntry : Type :=
  OperatorKO7.Meta.ConfessionMethodOptimalityBoundary.OptimalityBoundaryEntry

/-- API alias for the requirements imposed on a future route. -/
abbrev FutureRouteRequirements : Type 1 :=
  OperatorKO7.Meta.ConfessionMethodFutureRouteSchema.FutureRouteRequirements

/-- API alias for the proposition that a future route satisfies all requirements. -/
abbrev FutureRouteUniversalAdmission
  (R : FutureRouteRequirements) : Prop :=
  OperatorKO7.Meta.ConfessionMethodFutureRouteSchema.FutureRouteUniversalAdmission R

/-- API re-export of the theorem-boundary lookup. -/
abbrev optimalityBoundary : UniversalTheoremId → OptimalityBoundaryEntry :=
  OperatorKO7.Meta.ConfessionMethodOptimalityBoundary.optimalityBoundary

/-- API re-export of the theorem-boundary ledger. -/
abbrev optimalityBoundaryLedger : List OptimalityBoundaryEntry :=
  OperatorKO7.Meta.ConfessionMethodOptimalityBoundary.optimalityBoundaryLedger

/-- API re-export of the future-route admission equivalence. -/
abbrev future_route_admits_universal_surface_iff_requirements_met :=
  OperatorKO7.Meta.ConfessionMethodFutureRouteSchema.future_route_admits_universal_surface_iff_requirements_met

namespace UniversalTheoremId

abbrev universalConfessionCharacterization : UniversalTheoremId :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremId.universalConfessionCharacterization

abbrev confessionCostFloor : UniversalTheoremId :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremId.confessionCostFloor

abbrev confessionConvergenceIffHEquivalent : UniversalTheoremId :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremId.confessionConvergenceIffHEquivalent

abbrev optimalConfessionUniversalProperty : UniversalTheoremId :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremId.optimalConfessionUniversalProperty

abbrev canonicalConfessionMinimizesDiscardedInformation : UniversalTheoremId :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremId.canonicalConfessionMinimizesDiscardedInformation

abbrev gaugeFixingIdentity : UniversalTheoremId :=
  OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger.UniversalTheoremId.gaugeFixingIdentity

end UniversalTheoremId

namespace SupportingPhaseModule

abbrev L1RecordFormation : SupportingPhaseModule :=
  OperatorKO7.Meta.ConfessionMethodOptimalityBoundary.SupportingPhaseModule.L1RecordFormation

abbrev L2LandauerHeatBound : SupportingPhaseModule :=
  OperatorKO7.Meta.ConfessionMethodOptimalityBoundary.SupportingPhaseModule.L2LandauerHeatBound

abbrev L3BornRuleFromLandauer : SupportingPhaseModule :=
  OperatorKO7.Meta.ConfessionMethodOptimalityBoundary.SupportingPhaseModule.L3BornRuleFromLandauer

abbrev L4HawkingLandauerCycle : SupportingPhaseModule :=
  OperatorKO7.Meta.ConfessionMethodOptimalityBoundary.SupportingPhaseModule.L4HawkingLandauerCycle

abbrev L5QECSyndromeAsStage2 : SupportingPhaseModule :=
  OperatorKO7.Meta.ConfessionMethodOptimalityBoundary.SupportingPhaseModule.L5QECSyndromeAsStage2

end SupportingPhaseModule

/-- Number of theorem-backed routes in the universal route ledger. -/
def theoremBackedRouteCount : Nat :=
  theoremBackedRoutes.length

/-- Number of non-theorem-backed routes in the legacy conditional bucket. -/
def conditionalRouteCount : Nat :=
  conditionalRoutes.length

/-- Number of blocked routes in the universal route ledger. -/
def blockedRouteCount : Nat :=
  blockedRoutes.length

/-- Number of theorem identifiers in the theorem-projected ledger bucket. -/
def theoremProjectedCount : Nat :=
  theoremProjectedTheorems.length

/-- Number of theorem identifiers in the legacy optimality-payload bucket. -/
def optimalityStatusCount : Nat :=
  conditionalOnOptimalityPayloadTheorems.length

/-- Number of theorem identifiers in the legacy information-payload bucket. -/
def informationStatusCount : Nat :=
  conditionalOnInformationPayloadTheorems.length

/-- Number of theorem identifiers in the legacy information-and-Landauer bucket. -/
def costStatusCount : Nat :=
  conditionalOnInformationAndLandauerPayloadTheorems.length

/-- Number of recorded usable-rules bridge-attempt results. -/
noncomputable def bridgeAttemptResultCount : Nat :=
  [usableRulesSoundnessBridgeAttemptResult_artsGiesl,
    usableRulesSoundnessBridgeAttemptResult_lcel].length

/-- Number of theorem identifiers whose ledger status is payload-independent. -/
def unconditionallyTheoremBackedTheoremCount : Nat :=
  unconditionallyTheoremBackedTheorems.length

/-- Number of theorem identifiers outside the theorem-projected bucket. -/
def conditionalTheoremCount : Nat :=
  conditionalTheorems.length

/-- Number of theorem-boundary entries carrying a supporting-module tag. -/
def supportingPhaseModuleTaggedCount : Nat :=
  (optimalityBoundaryLedger.filterMap fun entry =>
    entry.supportingPhaseModule?.map fun _ => entry.theoremId).length

structure UniversalRouteStatusCounts where
  theoremBacked : Nat
  conditional : Nat
  blocked : Nat

structure UniversalCostStatusCounts where
  theoremProjected : Nat
  conditionalOnOptimalityPayload : Nat
  conditionalOnInformationPayload : Nat
  conditionalOnInformationAndLandauerPayload : Nat

/-- Route-status counts derived from the universal route ledger. -/
def universalRouteStatusCounts : UniversalRouteStatusCounts := {
  theoremBacked := theoremBackedRouteCount
  conditional := conditionalRouteCount
  blocked := blockedRouteCount
}

/-- Theorem-status counts derived from the theorem-boundary ledger. -/
def universalCostStatusCounts : UniversalCostStatusCounts := {
  theoremProjected := theoremProjectedCount
  conditionalOnOptimalityPayload := optimalityStatusCount
  conditionalOnInformationPayload := informationStatusCount
  conditionalOnInformationAndLandauerPayload := costStatusCount
}

/-- All five canonical routes are theorem-backed. -/
theorem theoremBackedRouteCount_exact : theoremBackedRouteCount = 5 :=
  theoremBackedRoutes_length

/-- The conditional route bucket is empty. -/
theorem conditionalRouteCount_exact : conditionalRouteCount = 0 :=
  conditionalRoutes_length

/-- The blocked route count is zero. -/
theorem blockedRouteCount_exact : blockedRouteCount = 0 :=
  blockedRoutes_length

/-- All six theorem identifiers are theorem-projected. -/
theorem theoremProjectedCount_exact : theoremProjectedCount = 6 :=
  theoremProjectedTheorems_length

/-- The optimality-payload subset of theorem identifiers is empty. -/
theorem optimalityStatusCount_exact : optimalityStatusCount = 0 :=
  rfl

/-- The information-only subset of theorem identifiers is empty. -/
theorem informationStatusCount_exact : informationStatusCount = 0 :=
  rfl

/-- The information-and-Landauer conditional bucket is empty. -/
theorem costStatusCount_exact : costStatusCount = 0 :=
  rfl

/-- The bridge-attempt result list contains two entries. -/
theorem bridgeAttemptResultCount_exact : bridgeAttemptResultCount = 2 :=
  rfl

/-- All six theorem identifiers have theorem-projected ledger status. -/
theorem unconditionallyTheoremBackedTheoremCount_exact :
    unconditionallyTheoremBackedTheoremCount = 6 :=
  theoremProjectedTheorems_length

/-- No theorem identifier remains outside the theorem-projected bucket. -/
theorem conditionalTheoremCount_exact : conditionalTheoremCount = 0 :=
  conditionalTheorems_length

/-- One theorem-boundary entry carries a supporting-module tag. -/
theorem supportingPhaseModuleTaggedCount_exact : supportingPhaseModuleTaggedCount = 1 :=
  rfl

end OperatorKO7.Meta.ConfessionMethodUniversalAPI
