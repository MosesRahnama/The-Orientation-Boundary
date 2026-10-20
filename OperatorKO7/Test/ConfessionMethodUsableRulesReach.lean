import OperatorKO7.Meta.ConfessionMethod_UsableRulesBridgeAttempt

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

namespace OperatorKO7.ConfessionMethodFamily

#check usableRulesRouteLocalWitnessField_inhabited
#check usableRulesDPSubstrateEvidence_witness
#check usableRulesResidual_projects_core_agreement
#check usableRulesResidual_projects_route_agreement
#check usableRulesResidual_projects_forgetting_rank
#check usableRulesResidual_requires_explicit_soundnessBridge
#check usableRulesResidual_to_common_route_evidence
#check usableRulesResidual_to_convergence_extension
#check hasUsableRulesConfessionRoute_iff_nonempty_convergence_extension
#check hasUsableRulesConfessionRoute_requires_sourceSoundnessTransport
#check no_usableRules_convergence_extension_without_residual
#check UsableRulesConcreteRouteCandidate
#check UsableRulesBridgeObligation
#check UsableRulesSoundnessBridge
#check usableRulesConcreteRouteCandidate
#check usableRulesConcreteRouteCandidate_to_residual
#check usableRulesConcreteRouteCandidate_projects_family_route_agreement
#check usableRulesConcreteRouteCandidate_projects_forgetting_rank
#check usableRulesConcreteRouteCandidate_soundnessBridge_witnessed
#check UsableRulesConcreteRouteBoundaryCatalog
#check usableRulesConcreteRouteBoundaryCatalog
#check usableRulesConcreteRouteBoundary_requires_soundnessBridge
#check usableRulesConcreteRouteBoundary_no_bridge_without_residual

example : Nonempty UsableRulesRouteLocalWitnessField :=
  usableRulesRouteLocalWitnessField_inhabited

example : UsableRulesDPSubstrateEvidence :=
  usableRulesDPSubstrateEvidence_witness

example (R : UsableRulesConfessionRouteResidualObligation) :
    usableRulesResidual_to_common_route_evidence R =
      confessionRouteConvergencePackage.commonRouteEvidence := by
  simpa using usableRulesResidual_to_common_route_evidence_eq (R := R)

example (R : UsableRulesConfessionRouteResidualObligation) :
    (ForgettingWitness.ofRouteEvidence
        (usableRulesResidual_to_common_route_evidence R)).rank = dpConfession.rank := by
  simpa [usableRulesResidual_to_common_route_evidence] using
    usableRulesResidual_projects_forgetting_rank (R := R)

example (R : UsableRulesConfessionRouteResidualObligation) :
    UsableRulesSourceSoundnessTransport :=
  usableRulesResidual_requires_explicit_soundnessBridge R

example (h : HasUsableRulesConfessionRoute) :
    Nonempty UsableRulesConvergenceExtension :=
  (hasUsableRulesConfessionRoute_iff_nonempty_convergence_extension).1 h

example (h : HasUsableRulesConfessionRoute) :
    UsableRulesSourceSoundnessTransport :=
  hasUsableRulesConfessionRoute_requires_sourceSoundnessTransport h

example (E : UsableRulesConvergenceExtension) :
    HasUsableRulesConfessionRoute :=
  usableRulesConvergenceExtension_requires_residual E

example (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    UsableRulesConfessionRouteResidualObligation :=
  usableRulesConcreteRouteCandidate_to_residual usableRulesConcreteRouteCandidate B

example (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    Nonempty UsableRulesConvergenceExtension :=
  usableRulesResidual_admits_convergence_extension
    (usableRulesConcreteRouteCandidate_to_residual usableRulesConcreteRouteCandidate B)

example :
    usableRulesConcreteRouteCandidate.toRouteEvidence
        usableRulesConcreteRouteCandidate.witness =
      confessionRouteConvergencePackage.commonRouteEvidence :=
  usableRulesConcreteRouteCandidate_projects_family_route_agreement
    usableRulesConcreteRouteCandidate

example :
    (ForgettingWitness.ofRouteEvidence
        (usableRulesConcreteRouteCandidate.toRouteEvidence
          usableRulesConcreteRouteCandidate.witness)).rank = dpConfession.rank :=
  usableRulesConcreteRouteCandidate_projects_forgetting_rank
    usableRulesConcreteRouteCandidate

example (h : usableRulesConcreteRouteBoundaryCatalog.MissingSoundnessBridge) :
    HasUsableRulesConfessionRoute :=
  usableRulesConcreteRouteBoundary_requires_soundnessBridge
    usableRulesConcreteRouteBoundaryCatalog h

example (h : ¬ HasUsableRulesConfessionRoute) :
    IsEmpty
      (UsableRulesSoundnessBridge usableRulesConcreteRouteBoundaryCatalog.candidate) :=
  usableRulesConcreteRouteBoundary_no_bridge_without_residual
    usableRulesConcreteRouteBoundaryCatalog h

example (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    Nonempty (UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :=
  usableRulesConcreteRouteCandidate_soundnessBridge_witnessed B

end OperatorKO7.ConfessionMethodFamily
