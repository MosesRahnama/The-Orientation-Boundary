import OperatorKO7.Meta.ConfessionMethod_RouteEvidence

/-!
# Confession Method Usable-Rules Boundary

This module does not construct a concrete usable-rules confession route.
It only exposes the theorem-visible projection and admission interface already
licensed by `UsableRulesConfessionRouteResidualObligation`.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- Any admitted usable-rules residual package agrees with the common
confession-core projection rank. -/
theorem usableRulesResidual_projects_core_agreement
    (R : UsableRulesConfessionRouteResidualObligation) :
    (R.toConfessionCoreWitness R.witness).toProjectionRank = confessionProjectionCore :=
  R.core_agrees

/-- Any admitted usable-rules residual package agrees with the same common
generic route-evidence object used by the four landed routes. -/
theorem usableRulesResidual_projects_route_agreement
    (R : UsableRulesConfessionRouteResidualObligation) :
    R.toRouteEvidence R.witness = confessionRouteConvergencePackage.commonRouteEvidence :=
  usableRulesRouteResidual_projects_common_route R

/-- The route evidence recovered from an admitted usable-rules residual
package. This is only a projection of existing residual data, not a new
concrete route witness. -/
def usableRulesResidual_to_common_route_evidence
    (R : UsableRulesConfessionRouteResidualObligation) : RouteEvidence ko7Schema :=
  R.toRouteEvidence R.witness

@[simp] theorem usableRulesResidual_to_common_route_evidence_eq
    (R : UsableRulesConfessionRouteResidualObligation) :
    usableRulesResidual_to_common_route_evidence R
        = confessionRouteConvergencePackage.commonRouteEvidence :=
  usableRulesResidual_projects_route_agreement R

/-- The forgetting-witness rank induced by any admitted usable-rules route is
the same canonical DP confession rank already carried by the four landed
routes. -/
theorem usableRulesResidual_projects_forgetting_rank
    (R : UsableRulesConfessionRouteResidualObligation) :
    (ForgettingWitness.ofRouteEvidence (R.toRouteEvidence R.witness)).rank
        = dpConfession.rank := by
  rw [usableRulesResidual_projects_route_agreement (R := R)]
  rfl

/-- The residual package only yields a usable-rules soundness bridge when such
a bridge is supplied explicitly as part of the residual data. -/
theorem usableRulesResidual_requires_explicit_soundnessBridge
    (R : UsableRulesConfessionRouteResidualObligation) :
    R.SoundnessTheorem :=
  R.soundnessTheorem

/-- Honest extension wrapper for the convergence story. A fifth usable-rules
route enters the package only from an inhabited residual obligation. -/
structure UsableRulesConvergenceExtension where
  residual : UsableRulesConfessionRouteResidualObligation
  usableRulesRouteEvidence : RouteEvidence ko7Schema
  usableRulesRouteEvidence_eq_common :
    usableRulesRouteEvidence = confessionRouteConvergencePackage.commonRouteEvidence
  usableRulesCoreRank_eq_common :
    (residual.toConfessionCoreWitness residual.witness).toProjectionRank
      = confessionProjectionCore
  bridgeCertification_verified : residual.bridgeCertification.IsVerified
  usableRulesForgettingRank_eq_common :
    (ForgettingWitness.ofRouteEvidence usableRulesRouteEvidence).rank
      = dpConfession.rank

/-- Any inhabited usable-rules residual package admits an honest fifth-route
extension of the four-route convergence story. -/
def usableRulesResidual_to_convergence_extension
    (R : UsableRulesConfessionRouteResidualObligation)
    (hVerified : R.bridgeCertification.IsVerified) :
    UsableRulesConvergenceExtension where
  residual := R
  usableRulesRouteEvidence := usableRulesResidual_to_common_route_evidence R
  usableRulesRouteEvidence_eq_common := usableRulesResidual_to_common_route_evidence_eq R
  usableRulesCoreRank_eq_common := usableRulesResidual_projects_core_agreement R
  bridgeCertification_verified := hVerified
  usableRulesForgettingRank_eq_common := by
    simpa [usableRulesResidual_to_common_route_evidence] using
      usableRulesResidual_projects_forgetting_rank R

/-- Route-admission criterion, forward direction: an inhabited residual
package is enough to add the usable-rules route to the convergence story. -/
theorem usableRulesResidual_admits_convergence_extension
    (R : UsableRulesConfessionRouteResidualObligation)
    (hVerified : R.bridgeCertification.IsVerified) :
    Nonempty UsableRulesConvergenceExtension :=
  ⟨usableRulesResidual_to_convergence_extension R hVerified⟩

/-- Route-admission criterion, reverse direction: any claimed usable-rules
convergence extension already contains an inhabited residual package. -/
theorem usableRulesConvergenceExtension_requires_residual
    (E : UsableRulesConvergenceExtension) :
    HasUsableRulesConfessionRoute :=
  ⟨E.residual, E.bridgeCertification_verified⟩

/-- Exact admission criterion for the usable-rules fifth route. -/
theorem hasUsableRulesConfessionRoute_iff_nonempty_convergence_extension :
    HasUsableRulesConfessionRoute ↔ Nonempty UsableRulesConvergenceExtension := by
  constructor
  · intro h
    rcases h with ⟨R, hVerified⟩
    exact usableRulesResidual_admits_convergence_extension R hVerified
  · intro h
    rcases h with ⟨E⟩
    exact usableRulesConvergenceExtension_requires_residual E

theorem hasUsableRulesConfessionRoute_requires_routeLocalWitnessField :
    HasUsableRulesConfessionRoute → Nonempty UsableRulesRouteLocalWitnessField := by
  intro h
  rcases h with ⟨R, hVerified⟩
  exact ⟨usableRulesBridgeCertification_verified_requires_routeLocalWitnessField hVerified⟩

theorem hasUsableRulesConfessionRoute_requires_standaloneSoundnessTheorem :
    HasUsableRulesConfessionRoute → UsableRulesStandaloneSoundnessTheorem := by
  intro h
  rcases h with ⟨R, hVerified⟩
  exact usableRulesBridgeCertification_verified_requires_standaloneSoundnessTheorem hVerified

/-- Any verified residual package already closes the usable-rules route. -/
theorem hasUsableRulesConfessionRoute_of_verifiedResidual
    (R : UsableRulesConfessionRouteResidualObligation)
    (hVerified : R.bridgeCertification.IsVerified) :
    HasUsableRulesConfessionRoute :=
  ⟨R, hVerified⟩

theorem hasUsableRulesConfessionRoute_iff_exists_verifiedResidual :
    HasUsableRulesConfessionRoute ↔
      ∃ R : UsableRulesConfessionRouteResidualObligation,
        R.bridgeCertification.IsVerified := by
  rfl

/-- Negative boundary: without an inhabited residual package, this module does
not license a theorem-backed usable-rules extension in the convergence story. -/
theorem no_usableRules_convergence_extension_without_residual
    (h : ¬ HasUsableRulesConfessionRoute) :
    IsEmpty UsableRulesConvergenceExtension := by
  refine ⟨?_⟩
  intro E
  exact h (usableRulesConvergenceExtension_requires_residual E)

end OperatorKO7.ConfessionMethodFamily
