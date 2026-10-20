import OperatorKO7.Meta.ConfessionMethod_UniversalInstances

/-!
# Confession Method Future Route Schema

This module specifies the data and equalities required to admit an additional
confession route to the universal-instance interface.
-/

namespace OperatorKO7.Meta.ConfessionMethodFutureRouteSchema

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.ConfessionMethodUniversalInstances

abbrev KO7FutureConfessionMethod : Type :=
  ConfessionMethod ko7Schema

abbrev KO7FutureRouteEvidence : Type :=
  RouteEvidence ko7Schema

/-- Data surface for an `(N+1)`-th confession route. The caller supplies the
candidate and canonical sigma-surface values used by the fourth admission
equality. -/
structure FutureRouteRequirements where
  name : String
  method : KO7FutureConfessionMethod
  routeEvidence : KO7FutureRouteEvidence
  SigmaCarrier : Type
  sigmaCandidate : SigmaCarrier
  sigmaCanonical : SigmaCarrier

/-- Named builder for future-route requirements with explicit sigma-carrier
arguments. -/
def mkFutureRouteRequirements
    (name : String)
    (method : KO7FutureConfessionMethod)
    (routeEvidence : KO7FutureRouteEvidence)
    (SigmaCarrier : Type)
    (sigmaCandidate sigmaCanonical : SigmaCarrier) : FutureRouteRequirements :=
  {
    name := name
    method := method
    routeEvidence := routeEvidence
    SigmaCarrier := SigmaCarrier
    sigmaCandidate := sigmaCandidate
    sigmaCanonical := sigmaCanonical
  }

/-- The four equalities required for admission to the universal confession
surface. -/
def FutureRouteRequirements.RequirementsMet
    (R : FutureRouteRequirements) : Prop :=
  R.method.rank = dpConfession.rank
    ∧ R.routeEvidence.rank = R.method.rank
    ∧ R.routeEvidence = confessionRouteConvergencePackage.commonRouteEvidence
    ∧ R.sigmaCandidate = R.sigmaCanonical

/-- Universal-surface admission package carrying the four required equalities. -/
structure FutureRouteUniversalAdmission (R : FutureRouteRequirements) where
  methodRankEq : R.method.rank = dpConfession.rank
  routeRankEq : R.routeEvidence.rank = R.method.rank
  routeProjectionEq : R.routeEvidence = confessionRouteConvergencePackage.commonRouteEvidence
  sigmaEq : R.sigmaCandidate = R.sigmaCanonical

/-- A future route has a universal-surface admission package if and only if the
four schema equalities are witnessed. -/
theorem future_route_admits_universal_surface_iff_requirements_met
    (R : FutureRouteRequirements) :
    Nonempty (FutureRouteUniversalAdmission R) ↔ R.RequirementsMet := by
  constructor
  · intro h
    rcases h with ⟨A⟩
    exact ⟨A.methodRankEq, A.routeRankEq, A.routeProjectionEq, A.sigmaEq⟩
  · intro h
    rcases h with ⟨methodRankEq, routeRankEq, routeProjectionEq, sigmaEq⟩
    refine ⟨{
      methodRankEq := methodRankEq
      routeRankEq := routeRankEq
      routeProjectionEq := routeProjectionEq
      sigmaEq := sigmaEq
    }⟩

/-- Conditional construction of an admission package for an `(N+1)`-th route,
named here as an RPO-with-marks variant. All four admission equalities remain
explicit hypotheses. -/
noncomputable def Future_Route_Schema_Example
    (method : KO7FutureConfessionMethod)
    (routeEvidence : KO7FutureRouteEvidence)
    (SigmaCarrier : Type)
    (sigmaCandidate sigmaCanonical : SigmaCarrier)
    (methodRankEq : method.rank = dpConfession.rank)
    (routeRankEq : routeEvidence.rank = method.rank)
    (routeProjectionEq : routeEvidence = confessionRouteConvergencePackage.commonRouteEvidence)
    (sigmaEq : sigmaCandidate = sigmaCanonical) :
    FutureRouteUniversalAdmission
      (mkFutureRouteRequirements
        "RPO-with-marks"
        method routeEvidence SigmaCarrier sigmaCandidate sigmaCanonical) := by
  let requirements :=
    mkFutureRouteRequirements
      "RPO-with-marks"
      method routeEvidence SigmaCarrier sigmaCandidate sigmaCanonical
  have hMet : requirements.RequirementsMet :=
    ⟨methodRankEq, routeRankEq, routeProjectionEq, sigmaEq⟩
  exact Classical.choice
    ((future_route_admits_universal_surface_iff_requirements_met requirements).2 hMet)

/-- Conditional construction for a polynomial-interpretation route with mark
elimination. All four admission equalities remain explicit hypotheses. -/
noncomputable def Future_Route_Schema_Example_2
    (method : KO7FutureConfessionMethod)
    (routeEvidence : KO7FutureRouteEvidence)
    (SigmaCarrier : Type)
    (sigmaCandidate sigmaCanonical : SigmaCarrier)
    (methodRankEq : method.rank = dpConfession.rank)
    (routeRankEq : routeEvidence.rank = method.rank)
    (routeProjectionEq : routeEvidence = confessionRouteConvergencePackage.commonRouteEvidence)
    (sigmaEq : sigmaCandidate = sigmaCanonical) :
    FutureRouteUniversalAdmission
      (mkFutureRouteRequirements
        "Polynomial-interpretation with mark elimination"
        method routeEvidence SigmaCarrier sigmaCandidate sigmaCanonical) := by
  let requirements :=
    mkFutureRouteRequirements
      "Polynomial-interpretation with mark elimination"
      method routeEvidence SigmaCarrier sigmaCandidate sigmaCanonical
  have hMet : requirements.RequirementsMet :=
    ⟨methodRankEq, routeRankEq, routeProjectionEq, sigmaEq⟩
  exact Classical.choice
    ((future_route_admits_universal_surface_iff_requirements_met requirements).2 hMet)

end OperatorKO7.Meta.ConfessionMethodFutureRouteSchema
