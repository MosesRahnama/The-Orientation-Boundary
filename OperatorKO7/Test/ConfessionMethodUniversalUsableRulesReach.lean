import OperatorKO7.Meta.ConfessionMethod_UsableRulesBridgeAttempt

namespace ConfessionMethodUniversalUsableRulesReach

open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.InformationTheoreticConfession
open OperatorKO7.Meta.ConfessionMethodUniversalInstances
open OperatorKO7.Meta.ConfessionMethodUniversalUsableRules

#check usableRulesResidual_routeEvidence_rank_eq_dpConfession
#check canonicalRouteEvidenceConfessionMove
#check canonicalRouteEvidenceInformationTheoreticConfession
#check usableRulesResidualToGenericConfessionMove
#check usableRulesResidualToInformationTheoreticConfession
#check usableRulesResidualToGenericConfessionMove_refines_canonical
#check usableRulesResidualToGenericConfessionMove_HEquivalent_canonical
#check usableRulesResidualUniversalCharacterizationData
#check usableRulesResidualOptimalityData
#check usableRulesResidualDiscardedInformationMinimalityData
#check UsableRulesUniversalInstance
#check usableRulesResidualUniversalInstance
#check usableRulesConcreteCandidateResidual
#check usableRulesConcreteCandidateConditionalInstance
#check usableRulesConcreteCandidate_with_soundnessBridge_projects_to_universal_surface
#check usableRulesConcreteCandidate_with_soundnessBridge_is_HEquivalent_canonical

example (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    ((usableRulesConcreteCandidateResidual B).toRouteEvidence
        (usableRulesConcreteCandidateResidual B).witness).rank = dpConfession.rank :=
  usableRulesResidual_routeEvidence_rank_eq_dpConfession
    (usableRulesConcreteCandidateResidual B)

example (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :=
  universal_confession_characterization_of_data
    (usableRulesResidualUniversalCharacterizationData
      (usableRulesConcreteCandidateResidual B))

example (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    GenericConfessionMove.Refines
      (usableRulesConcreteCandidateConditionalInstance B).move
      canonicalConfessionMove :=
  usableRulesConcreteCandidate_with_soundnessBridge_projects_to_universal_surface B

example (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    GenericConfessionMove.HEquivalent
      (usableRulesConcreteCandidateConditionalInstance B).move
      canonicalConfessionMove :=
  usableRulesConcreteCandidate_with_soundnessBridge_is_HEquivalent_canonical B

example (B : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    canonicalRouteEvidenceInformationTheoreticConfession.canonicalDiscardedBits ≤
      (usableRulesConcreteCandidateConditionalInstance B).informationProfile.canonicalDiscardedBits :=
  canonical_confession_minimizes_discarded_information_of_data
    (usableRulesResidualDiscardedInformationMinimalityData
      (usableRulesConcreteCandidateResidual B))

end ConfessionMethodUniversalUsableRulesReach
