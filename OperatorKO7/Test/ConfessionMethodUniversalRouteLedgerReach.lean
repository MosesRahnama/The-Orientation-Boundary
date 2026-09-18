import OperatorKO7.Meta.ConfessionMethod_UniversalRouteLedger

namespace ConfessionMethodUniversalRouteLedgerReach

open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.ConfessionMethodUniversalInstances
open OperatorKO7.Meta.ConfessionMethodUniversalUsableRules
open OperatorKO7.Meta.ConfessionMethodUniversalRouteLedger

#check UniversalRouteId
#check UniversalRouteStatus
#check universalRouteName
#check universalRouteStatus
#check UniversalRouteLedgerEntry
#check universalRouteLedger
#check theoremBackedRoutes
#check conditionalRoutes
#check blockedRoutes
#check universalRouteLedger_length
#check theoremBackedRoutes_length
#check conditionalRoutes_length
#check blockedRoutes_length
#check UniversalBridgeObligationStatus
#check universalBridgeObligationName
#check universalBridgeObligationStatus
#check UniversalBridgeObligationLedgerEntry
#check usableRulesBridgeObligationLedger
#check usableRulesBridgeObligationLedger_length
#check theoremBackedRouteMove?
#check theoremBackedRoute_has_universal_move
#check theoremBackedRoute_has_canonical_HEquivalence
#check usableRules_route_is_theoremBacked
#check usableRules_route_closed_status
#check UniversalTheoremId
#check UniversalTheoremStatus
#check universalTheoremName
#check universalTheoremStatus
#check UniversalTheoremLedgerEntry
#check universalTheoremLedger
#check theoremProjectedTheorems
#check conditionalTheorems
#check universalTheoremLedger_length
#check theoremProjectedTheorems_length
#check conditionalTheorems_length

example : universalRouteLedger.length = 5 :=
  universalRouteLedger_length

example : theoremBackedRoutes.length = 5 :=
  theoremBackedRoutes_length

example : conditionalRoutes.length = 0 :=
  conditionalRoutes_length

example : blockedRoutes.length = 0 :=
  blockedRoutes_length

example : usableRulesBridgeObligationLedger.length = 2 :=
  usableRulesBridgeObligationLedger_length

example : universalRouteStatus UniversalRouteId.usableRules = UniversalRouteStatus.theoremBacked :=
  rfl

example :
    universalBridgeObligationStatus UsableRulesBridgeObligation.routeLocalWitnessField
      = UniversalBridgeObligationStatus.discharged :=
  rfl

example :
    universalBridgeObligationStatus UsableRulesBridgeObligation.sourceSoundnessTransport
      = UniversalBridgeObligationStatus.discharged :=
  rfl

example :
    theoremBackedRouteMove? UniversalRouteId.usableRules =
      some usableRulesConcreteCandidateUniversalInstance.move :=
  rfl

example :
    ∃ move : UniversalMove KO7Carrier ko7ConfessionVerdict SoundnessLicense,
      theoremBackedRouteMove? UniversalRouteId.usableRules = some move :=
  theoremBackedRoute_has_universal_move
    (route := UniversalRouteId.usableRules) (by simp [theoremBackedRoutes])

example :
    ∃ move : UniversalMove KO7Carrier ko7ConfessionVerdict SoundnessLicense,
      theoremBackedRouteMove? UniversalRouteId.usableRules = some move
        ∧ GenericConfessionMove.HEquivalent move canonicalConfessionMove :=
  theoremBackedRoute_has_canonical_HEquivalence
    (route := UniversalRouteId.usableRules) (by simp [theoremBackedRoutes])

example :
    GenericConfessionMove.HEquivalent
      usableRulesConcreteCandidateUniversalInstance.move
      canonicalConfessionMove :=
  usableRules_route_is_theoremBacked

example :
    universalRouteStatus UniversalRouteId.usableRules = UniversalRouteStatus.theoremBacked
      ∧ universalBridgeObligationStatus .routeLocalWitnessField =
          UniversalBridgeObligationStatus.discharged
      ∧ universalBridgeObligationStatus .sourceSoundnessTransport =
          UniversalBridgeObligationStatus.discharged :=
  usableRules_route_closed_status

example : universalTheoremLedger.length = 6 :=
  universalTheoremLedger_length

example : theoremProjectedTheorems.length = 6 :=
  theoremProjectedTheorems_length

example : conditionalTheorems.length = 0 :=
  conditionalTheorems_length

example :
    universalTheoremStatus UniversalTheoremId.confessionCostFloor
      = UniversalTheoremStatus.theoremProjected :=
  rfl

end ConfessionMethodUniversalRouteLedgerReach
