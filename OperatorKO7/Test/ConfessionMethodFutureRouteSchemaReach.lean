import OperatorKO7.Meta.ConfessionMethod_FutureRouteSchema

namespace ConfessionMethodFutureRouteSchemaReach

open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.ConfessionMethodFutureRouteSchema

#check FutureRouteRequirements
#check FutureRouteRequirements.RequirementsMet
#check FutureRouteUniversalAdmission
#check future_route_admits_universal_surface_iff_requirements_met
#check Future_Route_Schema_Example
#check Future_Route_Schema_Example_2

example
  (method : KO7FutureConfessionMethod)
  (routeEvidence : KO7FutureRouteEvidence)
    (SigmaCarrier : Type)
    (sigmaCandidate sigmaCanonical : SigmaCarrier)
    (methodRankEq : method.rank = dpConfession.rank)
    (routeRankEq : routeEvidence.rank = method.rank)
    (routeProjectionEq : routeEvidence = confessionRouteConvergencePackage.commonRouteEvidence)
    (sigmaEq : sigmaCandidate = sigmaCanonical) :
    let requirements : FutureRouteRequirements := {
      name := "RPO-with-marks"
      method := method
      routeEvidence := routeEvidence
      SigmaCarrier := SigmaCarrier
      sigmaCandidate := sigmaCandidate
      sigmaCanonical := sigmaCanonical
    }
    Nonempty (FutureRouteUniversalAdmission requirements) := by
  let requirements : FutureRouteRequirements := {
    name := "RPO-with-marks"
    method := method
    routeEvidence := routeEvidence
    SigmaCarrier := SigmaCarrier
    sigmaCandidate := sigmaCandidate
    sigmaCanonical := sigmaCanonical
  }
  have hMet : requirements.RequirementsMet :=
    ⟨methodRankEq, routeRankEq, routeProjectionEq, sigmaEq⟩
  exact (future_route_admits_universal_surface_iff_requirements_met requirements).2 hMet

example
  (method : KO7FutureConfessionMethod)
  (routeEvidence : KO7FutureRouteEvidence)
    (SigmaCarrier : Type)
    (sigmaCandidate sigmaCanonical : SigmaCarrier)
    (methodRankEq : method.rank = dpConfession.rank)
    (routeRankEq : routeEvidence.rank = method.rank)
    (routeProjectionEq : routeEvidence = confessionRouteConvergencePackage.commonRouteEvidence)
    (sigmaEq : sigmaCandidate = sigmaCanonical) :
    FutureRouteUniversalAdmission {
      name := "RPO-with-marks"
      method := method
      routeEvidence := routeEvidence
      SigmaCarrier := SigmaCarrier
      sigmaCandidate := sigmaCandidate
      sigmaCanonical := sigmaCanonical
    } :=
  Future_Route_Schema_Example
    method routeEvidence SigmaCarrier sigmaCandidate sigmaCanonical
    methodRankEq routeRankEq routeProjectionEq sigmaEq

example
  (method : KO7FutureConfessionMethod)
  (routeEvidence : KO7FutureRouteEvidence)
    (SigmaCarrier : Type)
    (sigmaCandidate sigmaCanonical : SigmaCarrier)
    (methodRankEq : method.rank = dpConfession.rank)
    (routeRankEq : routeEvidence.rank = method.rank)
    (routeProjectionEq : routeEvidence = confessionRouteConvergencePackage.commonRouteEvidence)
    (sigmaEq : sigmaCandidate = sigmaCanonical) :
    FutureRouteUniversalAdmission {
      name := "Polynomial-interpretation with mark elimination"
      method := method
      routeEvidence := routeEvidence
      SigmaCarrier := SigmaCarrier
      sigmaCandidate := sigmaCandidate
      sigmaCanonical := sigmaCanonical
    } :=
  Future_Route_Schema_Example_2
    method routeEvidence SigmaCarrier sigmaCandidate sigmaCanonical
    methodRankEq routeRankEq routeProjectionEq sigmaEq

end ConfessionMethodFutureRouteSchemaReach
