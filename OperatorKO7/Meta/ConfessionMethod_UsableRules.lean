import OperatorKO7.Meta.ConfessionMethod_RouteEvidence

/-!
# Confession Method Usable-Rules Boundary

## Formal Scope

UsableRulesConvergenceExtension is caller-supplied residual data and equalities. The declarations project that package rather than deriving convergence.
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
generic route-evidence object used by the four available routes. -/
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
the same canonical DP confession rank already carried by the four available
routes. -/
theorem usableRulesResidual_projects_forgetting_rank
    (R : UsableRulesConfessionRouteResidualObligation) :
    (ForgettingWitness.ofRouteEvidence (R.toRouteEvidence R.witness)).rank
        = dpConfession.rank := by
  rw [usableRulesResidual_projects_route_agreement (R := R)]
  rfl

/-- The residual package exposes the dependency-pair-to-source transport
supplied explicitly as part of its data. -/
theorem usableRulesResidual_requires_explicit_soundnessBridge
    (R : UsableRulesConfessionRouteResidualObligation) :
    UsableRulesSourceSoundnessTransport :=
  R.sourceSoundnessTransport

/-- Conditional data wrapper built from an inhabited usable-rules residual
obligation. The historical type name does not assert convergence. -/
structure UsableRulesConvergenceExtension where
  residual : UsableRulesConfessionRouteResidualObligation
  usableRulesRouteEvidence : RouteEvidence ko7Schema
  usableRulesRouteEvidence_eq_common :
    usableRulesRouteEvidence = confessionRouteConvergencePackage.commonRouteEvidence
  usableRulesCoreRank_eq_common :
    (residual.toConfessionCoreWitness residual.witness).toProjectionRank
      = confessionProjectionCore
  sourceSoundnessTransport : UsableRulesSourceSoundnessTransport
  usableRulesForgettingRank_eq_common :
    (ForgettingWitness.ofRouteEvidence usableRulesRouteEvidence).rank
      = dpConfession.rank

/-- Construct the conditional data wrapper from an inhabited residual package. -/
def usableRulesResidual_to_convergence_extension
    (R : UsableRulesConfessionRouteResidualObligation) :
    UsableRulesConvergenceExtension where
  residual := R
  usableRulesRouteEvidence := usableRulesResidual_to_common_route_evidence R
  usableRulesRouteEvidence_eq_common := usableRulesResidual_to_common_route_evidence_eq R
  usableRulesCoreRank_eq_common := usableRulesResidual_projects_core_agreement R
  sourceSoundnessTransport := R.sourceSoundnessTransport
  usableRulesForgettingRank_eq_common := by
    simpa [usableRulesResidual_to_common_route_evidence] using
      usableRulesResidual_projects_forgetting_rank R

/-- An inhabited residual package yields an inhabitant of the wrapper type. -/
theorem usableRulesResidual_admits_convergence_extension
    (R : UsableRulesConfessionRouteResidualObligation) :
    Nonempty UsableRulesConvergenceExtension :=
  ⟨usableRulesResidual_to_convergence_extension R⟩

/-- Every wrapper contains its residual package. -/
theorem usableRulesConvergenceExtension_requires_residual
    (E : UsableRulesConvergenceExtension) :
    HasUsableRulesConfessionRoute :=
  ⟨E.residual⟩

/-- Equivalence between the residual-existence predicate and wrapper
inhabitation. -/
theorem hasUsableRulesConfessionRoute_iff_nonempty_convergence_extension :
    HasUsableRulesConfessionRoute ↔ Nonempty UsableRulesConvergenceExtension := by
  constructor
  · intro h
    rcases h with ⟨R⟩
    exact usableRulesResidual_admits_convergence_extension R
  · intro h
    rcases h with ⟨E⟩
    exact usableRulesConvergenceExtension_requires_residual E

/-- Any admitted residual package contains the fixed DP-to-source transport
required by its definition. -/
theorem hasUsableRulesConfessionRoute_requires_sourceSoundnessTransport :
    HasUsableRulesConfessionRoute → UsableRulesSourceSoundnessTransport := by
  intro h
  rcases h with ⟨R⟩
  exact R.sourceSoundnessTransport

/-- Any residual package carrying the required transport inhabits the abstract
usable-rules route interface. -/
theorem hasUsableRulesConfessionRoute_of_residual
    (R : UsableRulesConfessionRouteResidualObligation) :
    HasUsableRulesConfessionRoute :=
  ⟨R⟩

theorem hasUsableRulesConfessionRoute_iff_nonempty_residual :
    HasUsableRulesConfessionRoute ↔
      Nonempty UsableRulesConfessionRouteResidualObligation := by
  rfl

/-- If the residual-existence predicate is false, the wrapper type is empty. -/
theorem no_usableRules_convergence_extension_without_residual
    (h : ¬ HasUsableRulesConfessionRoute) :
    IsEmpty UsableRulesConvergenceExtension := by
  refine ⟨?_⟩
  intro E
  exact h (usableRulesConvergenceExtension_requires_residual E)

end OperatorKO7.ConfessionMethodFamily
