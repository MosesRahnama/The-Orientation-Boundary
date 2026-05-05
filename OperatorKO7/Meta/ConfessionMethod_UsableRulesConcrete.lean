import OperatorKO7.Meta.ConfessionMethod_UsableRules

/-!
# Confession Method Usable-Rules Concrete Boundary

This module extracts the concrete candidate data already present in the landed
four-route convergence package and separates it from the still-missing
usable-rules soundness bridge.

It does not prove that the usable-rules route is inhabited. It only names the
canonical candidate and the exact additional bridge object required to turn
that candidate into an admitted residual package.
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

/-- Exact open bridge obligations for the live usable-rules candidate. -/
inductive UsableRulesBridgeObligation where
  | routeLocalWitnessField
  | standaloneSoundnessTheorem
  deriving DecidableEq, Repr

/-- The exact missing bridge for a concrete usable-rules candidate: an explicit
theorem statement together with a proof of it. -/
structure UsableRulesSoundnessBridge (C : UsableRulesConcreteRouteCandidate) where
  SoundnessTheorem : Prop
  soundnessTheorem : SoundnessTheorem
  certification : UsableRulesBridgeCertification := .opaqueBridge

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
  SoundnessTheorem := B.SoundnessTheorem
  soundnessTheorem := B.soundnessTheorem
  bridgeCertification := B.certification

/-- Named adapter from the concrete candidate layer to the earlier residual
boundary package. -/
def usableRulesConcreteRouteCandidate_to_residual
    (C : UsableRulesConcreteRouteCandidate)
    (B : UsableRulesSoundnessBridge C) :
    UsableRulesConfessionRouteResidualObligation :=
  C.toResidual B

/-- Any concrete candidate still projects to the same common route evidence as
the four landed confession routes. -/
theorem usableRulesConcreteRouteCandidate_projects_family_route_agreement
    (C : UsableRulesConcreteRouteCandidate) :
    C.toRouteEvidence C.witness
      = confessionRouteConvergencePackage.commonRouteEvidence := by
  simpa [confessionRouteConvergencePackage] using C.route_agrees

/-- Any concrete candidate still recovers the canonical DP confession rank at
the forgetting-witness layer. -/
theorem usableRulesConcreteRouteCandidate_projects_forgetting_rank
    (C : UsableRulesConcreteRouteCandidate) :
    (ForgettingWitness.ofRouteEvidence (C.toRouteEvidence C.witness)).rank
      = dpConfession.rank := by
  rw [usableRulesConcreteRouteCandidate_projects_family_route_agreement (C := C)]
  rfl

/-- Canonical usable-rules candidate extracted from the already-landed shared
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

/-- Canonical boundary catalog for the usable-rules closure attempt: the
candidate is present, but the bridge is still a separate object. -/
structure UsableRulesConcreteRouteBoundaryCatalog where
  candidate : UsableRulesConcreteRouteCandidate

/-- The live S5 usable-rules boundary catalog extracted from the current KO7
family data. -/
def usableRulesConcreteRouteBoundaryCatalog :
    UsableRulesConcreteRouteBoundaryCatalog where
  candidate := usableRulesConcreteRouteCandidate

/-- The exact remaining bridge required by a boundary catalog. -/
abbrev UsableRulesConcreteRouteBoundaryCatalog.MissingSoundnessBridge
    (B : UsableRulesConcreteRouteBoundaryCatalog) : Prop :=
  ∃ bridge : UsableRulesSoundnessBridge B.candidate,
    bridge.certification.IsVerified

/-- A boundary catalog closes the usable-rules gap only from an explicit
soundness bridge for its concrete candidate. -/
theorem usableRulesConcreteRouteBoundary_requires_soundnessBridge
    (B : UsableRulesConcreteRouteBoundaryCatalog)
    (h : B.MissingSoundnessBridge) :
    HasUsableRulesConfessionRoute := by
  rcases h with ⟨bridge, hVerified⟩
  exact ⟨usableRulesConcreteRouteCandidate_to_residual B.candidate bridge, hVerified⟩

/-- Without an inhabited usable-rules residual package, the boundary catalog
cannot supply a concrete soundness bridge either. -/
theorem usableRulesConcreteRouteBoundary_no_bridge_without_residual
    (B : UsableRulesConcreteRouteBoundaryCatalog)
    (h : ¬ HasUsableRulesConfessionRoute) :
    IsEmpty { bridge : UsableRulesSoundnessBridge B.candidate //
      bridge.certification.IsVerified } := by
  refine ⟨?_⟩
  intro bridge
  exact h ⟨usableRulesConcreteRouteCandidate_to_residual B.candidate bridge.1, bridge.2⟩

theorem usableRulesConcreteRouteCandidate_verified_soundnessBridge_witnessed
    (bridge : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate)
    (hVerified : bridge.certification.IsVerified) :
    Nonempty { bridge : UsableRulesSoundnessBridge usableRulesConcreteRouteCandidate //
      bridge.certification.IsVerified } :=
  ⟨⟨bridge, hVerified⟩⟩

end OperatorKO7.ConfessionMethodFamily
