import OperatorKO7.Meta.ConfessionMethod_UsableRulesBridgeAttempt

namespace UsableRulesBridgeReach

open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.ConfessionMethodUsableRulesBridgeAttempt

#check usableRulesConcreteDPSubstrateEvidence
#check concreteUsableRulesBridgeWitness
#check concreteUsableRulesUniversalAdmission
#check usableRulesSoundnessBridgeObstruction
#check usableRulesSoundnessBridgeAttemptResult
#check usableRulesUniversal_iff_soundnessBridgeWitnessed
#check usableRules_fifth_route_closed

example :
    usableRulesSoundnessBridgeObstruction.openBridgeObligations =
      [UsableRulesBridgeObligation.sourceSoundnessTransport] :=
  usableRulesSoundnessBridgeObstruction.openBridgeObligations_exact

example :
    usableRulesSoundnessBridgeAttemptResult =
      UsableRulesSoundnessBridgeAttempt.witnessed
        concreteUsableRulesBridgeWitness :=
  usableRulesSoundnessBridgeAttemptResult_witnessed

example : Nonempty ConcreteUsableRulesUniversalAdmission :=
  concreteUsableRulesUniversalAdmission_inhabited

example :
    Nonempty ConcreteUsableRulesUniversalAdmission ↔
      Nonempty ConcreteUsableRulesBridgeWitness :=
  usableRulesUniversal_iff_soundnessBridgeWitnessed

example : HasUsableRulesConfessionRoute :=
  usableRules_fifth_route_closed

end UsableRulesBridgeReach
