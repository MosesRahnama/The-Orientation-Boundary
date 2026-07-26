import OperatorKO7.Meta.ConfessionMethod_UsableRulesBridgeAttempt

/-!
# Confession Method Universal Route Ledger

This module records the closed universal-route surface exposed by WS-A'.
It keeps two ledgers:
- the route ledger, on which all five canonical routes are theorem-backed;
- the theorem-status ledger, on which all six named theorem interfaces are
  complete on their declared proof-bearing domains.
-/

namespace OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger

open OperatorKO7
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.InformationTheoreticConfession
open OperatorKO7.Meta.ConfessionMethodUniversalInstances
open OperatorKO7.Meta.ConfessionMethodUsableRulesBridgeAttempt
open OperatorKO7.Meta.ConfessionMethodUniversalUsableRules

inductive UniversalRouteId where
  | dp
  | counterProjection
  | sct
  | argumentFiltering
  | usableRules
  deriving DecidableEq, Repr

inductive UniversalRouteStatus where
  | theoremBacked
  | conditional
  | blocked
  deriving DecidableEq, Repr

/-- Stable display names for the universal-route ledger. -/
def universalRouteName : UniversalRouteId → String
  | .dp => "DP"
  | .counterProjection => "CounterProjection"
  | .sct => "SCT"
  | .argumentFiltering => "ArgumentFiltering"
  | .usableRules => "UsableRules"

/-- Status of each universal-route entry. -/
def universalRouteStatus : UniversalRouteId → UniversalRouteStatus
  | .dp => .theoremBacked
  | .counterProjection => .theoremBacked
  | .sct => .theoremBacked
  | .argumentFiltering => .theoremBacked
  | .usableRules => .theoremBacked

structure UniversalRouteLedgerEntry where
  route : UniversalRouteId
  name : String
  status : UniversalRouteStatus

/-- Stable route ledger for the WS-A' surface. -/
def universalRouteLedger : List UniversalRouteLedgerEntry :=
  [⟨.dp, universalRouteName .dp, universalRouteStatus .dp⟩,
    ⟨.counterProjection, universalRouteName .counterProjection, universalRouteStatus .counterProjection⟩,
    ⟨.sct, universalRouteName .sct, universalRouteStatus .sct⟩,
    ⟨.argumentFiltering, universalRouteName .argumentFiltering, universalRouteStatus .argumentFiltering⟩,
    ⟨.usableRules, universalRouteName .usableRules, universalRouteStatus .usableRules⟩]

/-- Explicit route partitions used by the status counts. -/
def theoremBackedRoutes : List UniversalRouteId :=
  [.dp, .counterProjection, .sct, .argumentFiltering, .usableRules]

def conditionalRoutes : List UniversalRouteId :=
  []

def blockedRoutes : List UniversalRouteId :=
  []

inductive UniversalBridgeObligationStatus where
  | open
  | discharged
  deriving DecidableEq, Repr

def universalBridgeObligationName : UsableRulesBridgeObligation → String
  | .routeLocalWitnessField => "routeLocalWitnessField"
  | .sourceSoundnessTransport => "sourceSoundnessTransport"

def universalBridgeObligationStatus : UsableRulesBridgeObligation → UniversalBridgeObligationStatus
  | .routeLocalWitnessField => .discharged
  | .sourceSoundnessTransport => .discharged

structure UniversalBridgeObligationLedgerEntry where
  obligation : UsableRulesBridgeObligation
  name : String
  status : UniversalBridgeObligationStatus

/-- Stable ledger of the exact open usable-rules bridge obligations. -/
def usableRulesBridgeObligationLedger : List UniversalBridgeObligationLedgerEntry :=
  [⟨.routeLocalWitnessField,
      universalBridgeObligationName .routeLocalWitnessField,
      universalBridgeObligationStatus .routeLocalWitnessField⟩,
    ⟨.sourceSoundnessTransport,
      universalBridgeObligationName .sourceSoundnessTransport,
      universalBridgeObligationStatus .sourceSoundnessTransport⟩]

theorem universalRouteLedger_length : universalRouteLedger.length = 5 := by
  rfl

theorem theoremBackedRoutes_length : theoremBackedRoutes.length = 5 := by
  rfl

theorem conditionalRoutes_length : conditionalRoutes.length = 0 := by
  rfl

theorem blockedRoutes_length : blockedRoutes.length = 0 := by
  rfl

theorem usableRulesBridgeObligationLedger_length :
    usableRulesBridgeObligationLedger.length = 2 := by
  rfl

/-- The theorem-backed routes have concrete universal moves in the declared
API. Conditional routes are tracked separately. -/
noncomputable def theoremBackedRouteMove? : UniversalRouteId → Option
    (UniversalMove KO7Carrier
      OperatorKO7.Meta.InformationTheoreticConfession.ko7ConfessionVerdict
      SoundnessLicense)
  | .dp => some dpUniversalInstance.move
  | .counterProjection => some counterProjectionUniversalInstance.move
  | .sct => some sctUniversalInstance.move
  | .argumentFiltering => some argumentFilteringUniversalInstance.move
  | .usableRules => some usableRulesConcreteCandidateUniversalInstance.move

/-- Every theorem-backed route ledger entry exposes a universal move. -/
theorem theoremBackedRoute_has_universal_move
    {route : UniversalRouteId}
    (h : route ∈ theoremBackedRoutes) :
    ∃ move : UniversalMove KO7Carrier
      OperatorKO7.Meta.InformationTheoreticConfession.ko7ConfessionVerdict
      SoundnessLicense,
      theoremBackedRouteMove? route = some move := by
  cases route with
  | dp =>
      exact ⟨dpUniversalInstance.move, rfl⟩
  | counterProjection =>
      exact ⟨counterProjectionUniversalInstance.move, rfl⟩
  | sct =>
      exact ⟨sctUniversalInstance.move, rfl⟩
  | argumentFiltering =>
      exact ⟨argumentFilteringUniversalInstance.move, rfl⟩
  | usableRules =>
      exact ⟨usableRulesConcreteCandidateUniversalInstance.move, rfl⟩

/-- Every theorem-backed route ledger entry is H-equivalent to the canonical
confession move. -/
theorem theoremBackedRoute_has_canonical_HEquivalence
    {route : UniversalRouteId}
    (h : route ∈ theoremBackedRoutes) :
    ∃ move : UniversalMove KO7Carrier
      OperatorKO7.Meta.InformationTheoreticConfession.ko7ConfessionVerdict
      SoundnessLicense,
      theoremBackedRouteMove? route = some move
        ∧ GenericConfessionMove.HEquivalent move canonicalConfessionMove := by
  cases route with
  | dp =>
      exact ⟨dpUniversalInstance.move, rfl,
        methodToGenericConfessionMove_HEquivalent_canonical dpConfession rfl⟩
  | counterProjection =>
      exact ⟨counterProjectionUniversalInstance.move, rfl,
        methodToGenericConfessionMove_HEquivalent_canonical
          counterProjectionConfession counterProjection_eq_dp_rank⟩
  | sct =>
      exact ⟨sctUniversalInstance.move, rfl,
        methodToGenericConfessionMove_HEquivalent_canonical sctConfession sct_eq_dp_rank⟩
  | argumentFiltering =>
      exact ⟨argumentFilteringUniversalInstance.move, rfl,
        methodToGenericConfessionMove_HEquivalent_canonical
          argumentFilteringConfession argumentFiltering_eq_dp_rank⟩
  | usableRules =>
      exact ⟨usableRulesConcreteCandidateUniversalInstance.move, rfl,
        usableRulesConcreteCandidate_is_HEquivalent_canonical⟩

/-- The usable-rules route is unconditionally H-equivalent to the canonical rank map. -/
theorem usableRules_route_is_theoremBacked :
    GenericConfessionMove.HEquivalent
      usableRulesConcreteCandidateUniversalInstance.move
      canonicalConfessionMove :=
  usableRulesConcreteCandidate_is_HEquivalent_canonical

/-- Closed ledger status of the usable-rules row. -/
theorem usableRules_route_closed_status :
    universalRouteStatus UniversalRouteId.usableRules = UniversalRouteStatus.theoremBacked
    ∧ universalBridgeObligationStatus .routeLocalWitnessField =
        UniversalBridgeObligationStatus.discharged
    ∧ universalBridgeObligationStatus .sourceSoundnessTransport =
        UniversalBridgeObligationStatus.discharged := by
  exact ⟨rfl, rfl, rfl⟩

inductive UniversalTheoremId where
  | universalConfessionCharacterization
  | confessionCostFloor
  | confessionConvergenceIffHEquivalent
  | optimalConfessionUniversalProperty
  | canonicalConfessionMinimizesDiscardedInformation
  | gaugeFixingIdentity
  deriving DecidableEq, Repr

inductive UniversalTheoremStatus where
  | theoremProjected
  | conditionalOnOptimalityPayload
  | conditionalOnInformationPayload
  | conditionalOnInformationAndLandauerPayload
  deriving DecidableEq, Repr

/-- Stable theorem names for the WS-A' theorem-status ledger. -/
def universalTheoremName : UniversalTheoremId → String
  | .universalConfessionCharacterization => "universal_confession_characterization"
  | .confessionCostFloor => "confession_cost_floor"
  | .confessionConvergenceIffHEquivalent => "confession_convergence_iff_H_equivalent"
  | .optimalConfessionUniversalProperty => "optimal_confession_universal_property"
  | .canonicalConfessionMinimizesDiscardedInformation =>
      "canonical_confession_minimizes_discarded_information"
  | .gaugeFixingIdentity => "gauge_fixing_identity"

/-- Status of each named theorem on the declared theorem surface. -/
def universalTheoremStatus : UniversalTheoremId → UniversalTheoremStatus
  | .universalConfessionCharacterization => .theoremProjected
  | .confessionCostFloor => .theoremProjected
  | .confessionConvergenceIffHEquivalent => .theoremProjected
  | .optimalConfessionUniversalProperty => .theoremProjected
  | .canonicalConfessionMinimizesDiscardedInformation => .theoremProjected
  | .gaugeFixingIdentity => .theoremProjected

structure UniversalTheoremLedgerEntry where
  theoremId : UniversalTheoremId
  name : String
  status : UniversalTheoremStatus

/-- Stable theorem-status ledger for the WS-A' theorem surface. -/
def universalTheoremLedger : List UniversalTheoremLedgerEntry :=
  [⟨.universalConfessionCharacterization,
      universalTheoremName .universalConfessionCharacterization,
      universalTheoremStatus .universalConfessionCharacterization⟩,
    ⟨.confessionCostFloor,
      universalTheoremName .confessionCostFloor,
      universalTheoremStatus .confessionCostFloor⟩,
    ⟨.confessionConvergenceIffHEquivalent,
      universalTheoremName .confessionConvergenceIffHEquivalent,
      universalTheoremStatus .confessionConvergenceIffHEquivalent⟩,
    ⟨.optimalConfessionUniversalProperty,
      universalTheoremName .optimalConfessionUniversalProperty,
      universalTheoremStatus .optimalConfessionUniversalProperty⟩,
    ⟨.canonicalConfessionMinimizesDiscardedInformation,
      universalTheoremName .canonicalConfessionMinimizesDiscardedInformation,
      universalTheoremStatus .canonicalConfessionMinimizesDiscardedInformation⟩,
    ⟨.gaugeFixingIdentity,
      universalTheoremName .gaugeFixingIdentity,
      universalTheoremStatus .gaugeFixingIdentity⟩]

def theoremProjectedTheorems : List UniversalTheoremId :=
  [.universalConfessionCharacterization,
    .confessionCostFloor,
    .optimalConfessionUniversalProperty,
    .canonicalConfessionMinimizesDiscardedInformation,
    .confessionConvergenceIffHEquivalent,
    .gaugeFixingIdentity]

def conditionalTheorems : List UniversalTheoremId :=
  []

theorem universalTheoremLedger_length : universalTheoremLedger.length = 6 := by
  rfl

theorem theoremProjectedTheorems_length : theoremProjectedTheorems.length = 6 := by
  rfl

theorem conditionalTheorems_length : conditionalTheorems.length = 0 := by
  rfl


/-- The generic cost-floor theorem is complete on its applicability carrier,
while the canonical KO7 zero-bit profile has no inhabitant of that carrier. -/
theorem canonicalKO7_costFloor_applicability_closed :
    IsEmpty
      (ConfessionCostFloorData ko7CanonicalInformationTheoreticConfession) :=
  ko7CanonicalConfessionCostFloorData_empty

end OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger
