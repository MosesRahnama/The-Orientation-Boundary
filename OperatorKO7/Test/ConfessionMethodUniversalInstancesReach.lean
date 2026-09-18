import OperatorKO7.Meta.ConfessionMethod_UniversalInstances

namespace ConfessionMethodUniversalInstancesReach

open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.ConfessionMethodUniversalInstances
open OperatorKO7.Meta.InformationTheoreticConfession
open OperatorKO7.Meta.GenericConfessionMove

#check ko7ConfessionVerdict
#check methodToGenericConfessionMove
#check canonicalConfessionMove
#check methodToInformationTheoreticConfession
#check canonicalInformationTheoreticConfession
#check routeEvidenceToGenericConfessionMove
#check routeEvidenceToInformationTheoreticConfession
#check dpRouteEvidence_rank_eq_dpConfession
#check counterProjectionRouteEvidence_rank_eq_counterProjectionConfession
#check sctRouteEvidence_rank_eq_sctConfession
#check argumentFilteringRouteEvidence_rank_eq_argumentFilteringConfession
#check methodToGenericConfessionMove_refines_canonical
#check canonical_refines_methodToGenericConfessionMove
#check methodToGenericConfessionMove_HEquivalent_canonical
#check routeEvidenceToGenericConfessionMove_refines_canonical
#check routeEvidenceToGenericConfessionMove_HEquivalent_canonical
#check methodUniversalCharacterizationData
#check methodOptimalityData
#check methodDiscardedInformationMinimalityData
#check ConfessionMethodUniversalInstance
#check futureConfessionMethodUniversalInstance
#check dpUniversalInstance
#check counterProjectionUniversalInstance
#check sctUniversalInstance
#check argumentFilteringUniversalInstance
#check universalInstanceNames
#check universalInstanceNames_length
#check all_existing_confession_routes_are_HEquivalent_to_canonical
#check future_confessionMethod_with_rank_eq_and_routeEvidence_rank_eq_method_projects_to_universal_surface

example : universalInstanceNames.length = 4 :=
  universalInstanceNames_length

example : dpUniversalInstance.routeEvidence.rank = dpUniversalInstance.method.rank :=
  dpRouteEvidence_rank_eq_dpConfession

example : GenericConfessionMove.Refines counterProjectionUniversalInstance.move canonicalConfessionMove :=
  universal_confession_characterization
    (method := counterProjectionConfession)
    (by simp [allConfessionMethods])

example : GenericConfessionMove.HEquivalent sctUniversalInstance.move canonicalConfessionMove :=
  methodToGenericConfessionMove_HEquivalent_canonical sctConfession sct_eq_dp_rank

example : GenericConfessionMove.Refines argumentFilteringUniversalInstance.move canonicalConfessionMove := by
  exact (optimal_confession_universal_property
    (method := argumentFilteringConfession)
    (by simp [allConfessionMethods])).1

example : canonicalInformationTheoreticConfession.canonicalDiscardedBits ≤
    argumentFilteringUniversalInstance.informationProfile.canonicalDiscardedBits :=
  canonical_confession_minimizes_discarded_information
    (method := argumentFilteringConfession)
    (by simp [allConfessionMethods])

example : GenericConfessionMove.HEquivalent dpUniversalInstance.move canonicalConfessionMove
    ∧ GenericConfessionMove.HEquivalent counterProjectionUniversalInstance.move canonicalConfessionMove
    ∧ GenericConfessionMove.HEquivalent sctUniversalInstance.move canonicalConfessionMove
    ∧ GenericConfessionMove.HEquivalent argumentFilteringUniversalInstance.move canonicalConfessionMove :=
  all_existing_confession_routes_are_HEquivalent_to_canonical

example : GenericConfessionMove.Refines sctUniversalInstance.move canonicalConfessionMove
    ∧ GenericConfessionMove.Refines canonicalConfessionMove sctUniversalInstance.move := by
  exact gauge_fixing_identity
    (methodToGenericConfessionMove_HEquivalent_canonical sctConfession sct_eq_dp_rank)

example :
    GenericConfessionMove.Refines
        (routeEvidenceToGenericConfessionMove
          schemaSCTGenericRouteEvidence
          (sctRouteEvidence_rank_eq_sctConfession.trans sct_eq_dp_rank))
        canonicalConfessionMove
      ∧ GenericConfessionMove.HEquivalent
        (futureConfessionMethodUniversalInstance
          "SCT-future"
          sctConfession
          schemaSCTGenericRouteEvidence
          sct_eq_dp_rank).move
        canonicalConfessionMove :=
  future_confessionMethod_with_rank_eq_and_routeEvidence_rank_eq_method_projects_to_universal_surface
    "SCT-future"
    sctConfession
    schemaSCTGenericRouteEvidence
    sct_eq_dp_rank
    sctRouteEvidence_rank_eq_sctConfession

end ConfessionMethodUniversalInstancesReach
