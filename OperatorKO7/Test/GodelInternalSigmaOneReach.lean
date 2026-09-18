import OperatorKO7.Meta.DistinctionBoundary.GodelInternalSigmaOne

namespace OperatorKO7.Test.GodelInternalSigmaOneReach

open OperatorKO7.Meta.DistinctionBoundary.GodelArith

#check @RepresentsCheckerI
#print axioms RepresentsCheckerI
#check @InternalSigmaOneCompleteness
#print axioms InternalSigmaOneCompleteness
#check @InternalSigmaOneRoute
#print axioms InternalSigmaOneRoute
#check @internal_sigma1_route_impossible
#print axioms internal_sigma1_route_impossible
#check @InternalSigmaOneRouteKill
#print axioms InternalSigmaOneRouteKill
#check @internal_sigma1_route_killed
#print axioms internal_sigma1_route_killed
#check @InternalSigmaOneRoute.mk
#print axioms InternalSigmaOneRoute.mk
#check @InternalSigmaOneRoute.externalComplete
#print axioms InternalSigmaOneRoute.externalComplete
#check @InternalSigmaOneRoute.BewI
#print axioms InternalSigmaOneRoute.BewI
#check @InternalSigmaOneRoute.represents
#print axioms InternalSigmaOneRoute.represents
#check @InternalSigmaOneRoute.internalComplete
#print axioms InternalSigmaOneRoute.internalComplete
#check @InternalSigmaOneRouteKill.mk
#print axioms InternalSigmaOneRouteKill.mk
#check @InternalSigmaOneRouteKill.inductionCheckerSound
#print axioms InternalSigmaOneRouteKill.inductionCheckerSound
#check @InternalSigmaOneRouteKill.atomicWitnessSigmaOne
#print axioms InternalSigmaOneRouteKill.atomicWitnessSigmaOne
#check @InternalSigmaOneRouteKill.atomicWitnessTrue
#print axioms InternalSigmaOneRouteKill.atomicWitnessTrue
#check @InternalSigmaOneRouteKill.atomicWitnessUnprovable
#print axioms InternalSigmaOneRouteKill.atomicWitnessUnprovable
#check @InternalSigmaOneRouteKill.routeUninhabited
#print axioms InternalSigmaOneRouteKill.routeUninhabited

end OperatorKO7.Test.GodelInternalSigmaOneReach
