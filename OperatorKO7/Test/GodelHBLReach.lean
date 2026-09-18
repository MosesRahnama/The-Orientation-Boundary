import OperatorKO7.Meta.DistinctionBoundary.GodelHBL

namespace OperatorKO7.Test.GodelHBLReach

open OperatorKO7.Meta.DistinctionBoundary.GodelArith

#check @HBLD1I
#print axioms HBLD1I
#check @HBLD2I
#print axioms HBLD2I
#check @HBLD3I
#print axioms HBLD3I
#check @HBLRouteI
#print axioms HBLRouteI
#check @hbl_routeI_impossible
#print axioms hbl_routeI_impossible
#check @GodelIIRouteDisposition
#print axioms GodelIIRouteDisposition
#check @godelII_routes_terminal
#print axioms godelII_routes_terminal
#check @godelII_live_checker_closed_despite_HBL_kill
#print axioms godelII_live_checker_closed_despite_HBL_kill
#check @HBLRouteI.mk
#print axioms HBLRouteI.mk
#check @HBLRouteI.sigmaRoute
#print axioms HBLRouteI.sigmaRoute
#check @HBLRouteI.d1
#print axioms HBLRouteI.d1
#check @HBLRouteI.d2
#print axioms HBLRouteI.d2
#check @HBLRouteI.d3
#print axioms HBLRouteI.d3
#check @GodelIIRouteDisposition.mk
#print axioms GodelIIRouteDisposition.mk
#check @GodelIIRouteDisposition.routeA
#print axioms GodelIIRouteDisposition.routeA
#check @GodelIIRouteDisposition.routeBImpossible
#print axioms GodelIIRouteDisposition.routeBImpossible
#check @GodelIIRouteDisposition.inductionExtensionConsistent
#print axioms GodelIIRouteDisposition.inductionExtensionConsistent
#check @GodelIIRouteDisposition.sigmaFailureWitness
#print axioms GodelIIRouteDisposition.sigmaFailureWitness

end OperatorKO7.Test.GodelHBLReach
