import OperatorKO7.Meta.ConfessionMethod_UsableRulesBridgeAttempt

namespace ConfessionMethodUsableRulesBridgeAttemptReach

open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.ConfessionMethodUniversalUsableRules
open OperatorKO7.Meta.ConfessionMethodUsableRulesBridgeAttempt

#check ConcreteUsableRulesBridgeWitness
#check ConcreteUsableRulesUniversalAdmission
#check concreteUsableRulesBridgeWitness
#check concreteUsableRulesUniversalAdmission
#check concreteUsableRulesUniversalAdmission_inhabited
#check concreteUsableRulesUniversalAdmissionOfBridge
#check ConcreteUsableRulesUniversalAdmission.conditionalInstance
#check usableRulesConcreteRouteLocalWitnessField
#check usableRulesConcreteDPSubstrateEvidence
#check usableRulesConcreteCommonRouteMove
#check usableRulesConcreteCommonRoute_is_HEquivalent_canonical
#check UsableRulesSoundnessBridgeObstruction
#check usableRulesSoundnessBridgeObstruction
#check UsableRulesSoundnessBridgeAttempt
#check usableRulesSoundnessBridgeAttemptResult
#check usableRulesSoundnessBridgeObstruction_artsGiesl
#check usableRulesSoundnessBridgeObstruction_lcel
#check usableRulesSoundnessBridgeAttemptResult_artsGiesl
#check usableRulesSoundnessBridgeAttemptResult_lcel
#check usableRulesSoundnessBridgeAttemptResult_combined
#check usableRulesUniversal_iff_soundnessBridgeWitnessed
#check usableRules_fifth_route_closed
#check usableRulesSoundnessBridgeAttemptResult_witnessed

example :
    usableRulesSoundnessBridgeObstruction.candidate =
      usableRulesConcreteRouteCandidate :=
  rfl

example :
    usableRulesSoundnessBridgeObstruction.attemptedSubstrate =
      "shared dependency-pair route evidence" :=
  rfl

example :
    usableRulesSoundnessBridgeObstruction.openBridgeObligations =
      [UsableRulesBridgeObligation.sourceSoundnessTransport] :=
  usableRulesSoundnessBridgeObstruction.openBridgeObligations_exact

example :
    usableRulesSoundnessBridgeAttemptResult =
      UsableRulesSoundnessBridgeAttempt.witnessed
        concreteUsableRulesBridgeWitness :=
  usableRulesSoundnessBridgeAttemptResult_witnessed

example :
    usableRulesSoundnessBridgeObstruction_artsGiesl.attemptedSubstrate =
      "Arts-Giesl derivational-complexity route" :=
  rfl

example :
    usableRulesSoundnessBridgeObstruction_lcel.attemptedSubstrate =
      "LCEL native DP/emitter license route" :=
  rfl

example :
    usableRulesSoundnessBridgeAttemptResult_artsGiesl =
      UsableRulesSoundnessBridgeAttempt.witnessed
        concreteUsableRulesBridgeWitness :=
  rfl

example :
    usableRulesSoundnessBridgeAttemptResult_lcel =
      UsableRulesSoundnessBridgeAttempt.witnessed
        concreteUsableRulesBridgeWitness :=
  rfl

example :
    [usableRulesSoundnessBridgeAttemptResult_artsGiesl,
      usableRulesSoundnessBridgeAttemptResult_lcel]
      = [UsableRulesSoundnessBridgeAttempt.witnessed
          concreteUsableRulesBridgeWitness,
        UsableRulesSoundnessBridgeAttempt.witnessed
          concreteUsableRulesBridgeWitness] :=
  usableRulesSoundnessBridgeAttemptResult_combined

example : Nonempty ConcreteUsableRulesUniversalAdmission :=
  concreteUsableRulesUniversalAdmission_inhabited

example :
    Nonempty ConcreteUsableRulesUniversalAdmission ↔
      Nonempty ConcreteUsableRulesBridgeWitness :=
  usableRulesUniversal_iff_soundnessBridgeWitnessed

example : HasUsableRulesConfessionRoute :=
  usableRules_fifth_route_closed

end ConfessionMethodUsableRulesBridgeAttemptReach
