import OperatorKO7.Meta.ConfessionMethod_UsableRules
import OperatorKO7.Meta.PolyInterpretation_FullStep

/-!
# Confession Method Usable-Rules Concrete Boundary

## Formal Scope

The concrete route is represented by the common KO7 confession witness.  The
bridge type asks for a theorem transporting well-foundedness of the extracted
pair problem to root termination of the KO7 source relation.  That implication
is discharged below by the independently proved full-system polynomial
termination theorem.  No generic usable-rules processor theorem is inferred
from route-evidence equality alone.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- Concrete route-shaped data already available for a usable-rules candidate,
before any external soundness theorem is supplied. -/
structure UsableRulesConcreteRouteCandidate where
  Witness : Type
  witness : Witness
  toConfessionCoreWitness : Witness → ConfessionCoreWitness ko7Schema
  toRouteEvidence : Witness → RouteEvidence ko7Schema
  core_agrees :
    (toConfessionCoreWitness witness).toProjectionRank = confessionProjectionCore
  route_agrees :
    toRouteEvidence witness = confessionGenericRouteEvidence

/-- Proof obligations exposed by the usable-rules candidate interface. -/
inductive UsableRulesBridgeObligation where
  | routeLocalWitnessField
  | sourceSoundnessTransport
  deriving DecidableEq, Repr

/-- A proof-bearing bridge for a concrete usable-rules candidate.  Its fixed
theorem transports well-foundedness of the extracted dependency-pair problem
to root termination of the original `Step` relation. -/
structure UsableRulesSoundnessBridge (C : UsableRulesConcreteRouteCandidate) where
  sourceSoundnessTransport : UsableRulesSourceSoundnessTransport

/-- Any concrete candidate becomes an admitted residual package once an
explicit soundness bridge is supplied. -/
def UsableRulesConcreteRouteCandidate.toResidual
    (C : UsableRulesConcreteRouteCandidate)
    (B : UsableRulesSoundnessBridge C) :
    UsableRulesConfessionRouteResidualObligation where
  Witness := C.Witness
  witness := C.witness
  toConfessionCoreWitness := C.toConfessionCoreWitness
  toRouteEvidence := C.toRouteEvidence
  core_agrees := C.core_agrees
  route_agrees := C.route_agrees
  sourceSoundnessTransport := B.sourceSoundnessTransport

/-- Named adapter from the concrete candidate layer to the residual
boundary package. -/
def usableRulesConcreteRouteCandidate_to_residual
    (C : UsableRulesConcreteRouteCandidate)
    (B : UsableRulesSoundnessBridge C) :
    UsableRulesConfessionRouteResidualObligation :=
  C.toResidual B

/-- Every concrete candidate projects to the same common route evidence as the four original confession routes. -/
theorem usableRulesConcreteRouteCandidate_projects_family_route_agreement
    (C : UsableRulesConcreteRouteCandidate) :
    C.toRouteEvidence C.witness
      = confessionRouteConvergencePackage.commonRouteEvidence := by
  simpa [confessionRouteConvergencePackage] using C.route_agrees

/-- Every concrete candidate recovers the canonical DP confession rank at the forgetting-witness layer. -/
theorem usableRulesConcreteRouteCandidate_projects_forgetting_rank
    (C : UsableRulesConcreteRouteCandidate) :
    (ForgettingWitness.ofRouteEvidence (C.toRouteEvidence C.witness)).rank
      = dpConfession.rank := by
  rw [usableRulesConcreteRouteCandidate_projects_family_route_agreement (C := C)]
  rfl

/-- Canonical usable-rules candidate extracted from the already-available shared
confession core and shared generic route evidence. -/
def usableRulesConcreteRouteCandidate : UsableRulesConcreteRouteCandidate where
  Witness := PUnit
  witness := PUnit.unit
  toConfessionCoreWitness _ := confessionRouteConvergencePackage.commonCoreWitness
  toRouteEvidence _ := confessionRouteConvergencePackage.commonRouteEvidence
  core_agrees := by
    simp [confessionRouteConvergencePackage, confessionCoreWitness, confessionProjectionCore]
  route_agrees := by
    simp [confessionRouteConvergencePackage]


/-- Unconditional KO7 source-soundness transport.  The implication required by
the usable-rules interface is valid because the source `Step` relation already
has an independent polynomial well-foundedness proof.  The premise is retained
in the function type so that this value exactly inhabits the declared bridge;
the proof does not claim generic usable-rules processor soundness. -/
def usableRulesSourceSoundnessTransport : UsableRulesSourceSoundnessTransport where
  pairProblemWellFounded_implies_sourceRootTermination := by
    intro _
    exact OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-- Fully inhabited soundness bridge for the canonical KO7 usable-rules candidate. -/
def usableRulesConcreteSoundnessBridge :
    UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate where
  sourceSoundnessTransport := usableRulesSourceSoundnessTransport

/-- The canonical usable-rules residual package with all fields inhabited. -/
def usableRulesConcreteRouteResidual :
    UsableRulesConfessionRouteResidualObligation :=
  usableRulesConcreteRouteCandidate_to_residual
    usableRulesConcreteRouteCandidate
    usableRulesConcreteSoundnessBridge

/-- The canonical usable-rules route is inhabited. -/
theorem usableRulesConcreteRoute_inhabited : HasUsableRulesConfessionRoute :=
  ⟨usableRulesConcreteRouteResidual⟩

/-- Canonical catalog for the usable-rules candidate and its proof-bearing bridge interface. -/
structure UsableRulesConcreteRouteBoundaryCatalog where
  candidate : UsableRulesConcreteRouteCandidate

/-- The S5 usable-rules boundary catalog extracted from the KO7 family data. -/
def usableRulesConcreteRouteBoundaryCatalog :
    UsableRulesConcreteRouteBoundaryCatalog where
  candidate := usableRulesConcreteRouteCandidate

/-- The specified remaining bridge required by a boundary catalog. -/
abbrev UsableRulesConcreteRouteBoundaryCatalog.MissingSoundnessBridge
    (B : UsableRulesConcreteRouteBoundaryCatalog) : Prop :=
  Nonempty (UsableRulesSoundnessBridge B.candidate)

/-- A boundary catalog closes the usable-rules gap only from an explicit
soundness bridge for its concrete candidate. -/
theorem usableRulesConcreteRouteBoundary_requires_soundnessBridge
  (B : UsableRulesConcreteRouteBoundaryCatalog)
    (h : B.MissingSoundnessBridge) :
    HasUsableRulesConfessionRoute := by
  rcases h with ⟨bridge⟩
  exact ⟨usableRulesConcreteRouteCandidate_to_residual B.candidate bridge⟩

/-- Without an inhabited usable-rules residual package, the boundary catalog
cannot supply a concrete soundness bridge either. -/
theorem usableRulesConcreteRouteBoundary_no_bridge_without_residual
    (B : UsableRulesConcreteRouteBoundaryCatalog)
    (h : ¬ HasUsableRulesConfessionRoute) :
    IsEmpty (UsableRulesSoundnessBridge B.candidate) := by
  refine ⟨?_⟩
  intro bridge
  exact h ⟨usableRulesConcreteRouteCandidate_to_residual B.candidate bridge⟩

theorem usableRulesConcreteRouteCandidate_soundnessBridge_witnessed
    (bridge : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :
    Nonempty (UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate) :=
  ⟨bridge⟩


/-- The canonical boundary catalog contains the required soundness bridge. -/
theorem usableRulesConcreteRouteBoundary_soundnessBridge_closed :
    usableRulesConcreteRouteBoundaryCatalog.MissingSoundnessBridge :=
  ⟨usableRulesConcreteSoundnessBridge⟩

/-- Unconditional closeout of the canonical usable-rules route. -/
theorem usableRulesConcreteRouteBoundary_closed :
    HasUsableRulesConfessionRoute :=
  usableRulesConcreteRouteBoundary_requires_soundnessBridge
    usableRulesConcreteRouteBoundaryCatalog
    usableRulesConcreteRouteBoundary_soundnessBridge_closed

end OperatorKO7.ConfessionMethodFamily
