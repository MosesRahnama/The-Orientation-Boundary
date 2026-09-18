import OperatorKO7.Meta.ConfessionMethod_Unification

/-!
# Confession-Method Route Evidence

This module is the shared boundary for the generic `RouteEvidence` layer above
the four concrete KO7 confession-method entry routes.

It packages the route-local evidence in one import:

- the four concrete route witnesses,
- their generic `RouteEvidence` adapters,
- the generic forgetting-witness lift,
- the KO7-local unification theorems showing that all four routes factor
  through one common generic route-evidence object.

The underlying definitions are provided by:

- the abstract `RouteEvidence` interface in `StepDuplicatingSchema.lean`,
- the method-specific witness records in the four route files,
- the convergence results in `ConfessionMethod_Unification.lean`.

This file gives the distributed layer a single import boundary.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-- Compact KO7-facing convergence package for the four confession routes.
It keeps the common confession core, the generic route-evidence surface, and
the four route-local generic adapters in one theorem-backed object. -/
structure ConfessionRouteConvergencePackage where
  commonCoreWitness : ConfessionCoreWitness ko7Schema
  commonRouteEvidence : RouteEvidence ko7Schema
  commonForgettingWitness : ForgettingWitness ko7Schema
  dpRouteEvidence : RouteEvidence ko7Schema
  counterProjectionRouteEvidence : RouteEvidence ko7Schema
  sctRouteEvidence : RouteEvidence ko7Schema
  argumentFilteringRouteEvidence : RouteEvidence ko7Schema
  dp_agrees : dpRouteEvidence = commonRouteEvidence
  counterProjection_agrees : counterProjectionRouteEvidence = commonRouteEvidence
  sct_agrees : sctRouteEvidence = commonRouteEvidence
  argumentFiltering_agrees : argumentFilteringRouteEvidence = commonRouteEvidence
  commonForgettingWitness_rank : commonForgettingWitness.rank = commonRouteEvidence.rank

/-- The canonical convergence package for the four concrete confession routes. -/
def confessionRouteConvergencePackage : ConfessionRouteConvergencePackage where
  commonCoreWitness := confessionCoreWitness
  commonRouteEvidence := confessionGenericRouteEvidence
  commonForgettingWitness := ForgettingWitness.ofRouteEvidence confessionGenericRouteEvidence
  dpRouteEvidence := dpGenericRouteEvidence
  counterProjectionRouteEvidence := directCounterProjectionGenericRouteEvidence
  sctRouteEvidence := sctGenericRouteEvidence
  argumentFilteringRouteEvidence := argumentFilteringGenericRouteEvidence
  dp_agrees := all_route_local_evidence_share_generic_route_evidence.1
  counterProjection_agrees := all_route_local_evidence_share_generic_route_evidence.2.1
  sct_agrees := all_route_local_evidence_share_generic_route_evidence.2.2.1
  argumentFiltering_agrees := all_route_local_evidence_share_generic_route_evidence.2.2.2
  commonForgettingWitness_rank := rfl

/-- The convergence package projects the four route adapters to one common
generic route-evidence object. -/
theorem confessionRouteConvergencePackage_projects_route_agreement :
    confessionRouteConvergencePackage.dpRouteEvidence
        = confessionRouteConvergencePackage.commonRouteEvidence
    ∧ confessionRouteConvergencePackage.counterProjectionRouteEvidence
        = confessionRouteConvergencePackage.commonRouteEvidence
    ∧ confessionRouteConvergencePackage.sctRouteEvidence
        = confessionRouteConvergencePackage.commonRouteEvidence
    ∧ confessionRouteConvergencePackage.argumentFilteringRouteEvidence
        = confessionRouteConvergencePackage.commonRouteEvidence := by
  exact ⟨confessionRouteConvergencePackage.dp_agrees,
    confessionRouteConvergencePackage.counterProjection_agrees,
    confessionRouteConvergencePackage.sct_agrees,
    confessionRouteConvergencePackage.argumentFiltering_agrees⟩

/-- The common forgetting witness carried by the convergence package agrees
with the canonical DP confession rank. -/
theorem confessionRouteConvergencePackage_projects_common_forgetting_witness :
    confessionRouteConvergencePackage.commonForgettingWitness.rank = dpConfession.rank := by
  rfl

/-! Data required for a usable-rules confession route to join the KO7
convergence package. Route-evidence agreement and dependency-pair
well-foundedness are support data. Admission also requires a theorem
transporting dependency-pair well-foundedness to root termination of the
original `Step` relation. -/

/-- Route-local witness field for the usable-rules bridge. It records that the
candidate lies on the same generic route-evidence surface as the four
confession routes. -/
structure UsableRulesRouteLocalWitnessField : Type where
  commonRoute_eq_generic :
    confessionRouteConvergencePackage.commonRouteEvidence = confessionGenericRouteEvidence
  commonRoute_rank_eq_dpConfession :
    confessionRouteConvergencePackage.commonRouteEvidence.rank = dpConfession.rank

/-- Canonical route-local usable-rules witness carried by the shared generic
route-evidence surface. -/
def usableRulesCommonRouteLocalWitnessField : UsableRulesRouteLocalWitnessField where
  commonRoute_eq_generic := rfl
  commonRoute_rank_eq_dpConfession := by
    exact confessionRouteConvergencePackage.commonForgettingWitness_rank.symm.trans
      confessionRouteConvergencePackage_projects_common_forgetting_witness

theorem usableRulesRouteLocalWitnessField_inhabited :
    Nonempty UsableRulesRouteLocalWitnessField :=
  ⟨usableRulesCommonRouteLocalWitnessField⟩

/-- Dependency-pair substrate available to a usable-rules bridge. It records
rank agreement, well-foundedness of the extracted pair relation, and the
external-license tag. It does not prove dependency-pair-to-source transport or
usable-rules processor soundness. -/
structure UsableRulesDPSubstrateEvidence : Prop where
  commonRoute_rank_eq_dpConfession :
    confessionRouteConvergencePackage.commonRouteEvidence.rank = dpConfession.rank
  pairProblemWellFounded : WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev
  dpLicense_is_artsGiesl2000 :
    dpConfession.license = SoundnessLicense.artsGiesl2000

/-- The shared route package supplies dependency-pair substrate evidence. -/
theorem usableRulesDPSubstrateEvidence_witness :
    UsableRulesDPSubstrateEvidence := by
  refine ⟨?_, ?_, rfl⟩
  · exact confessionRouteConvergencePackage.commonForgettingWitness_rank.symm.trans
      confessionRouteConvergencePackage_projects_common_forgetting_witness
  exact OperatorKO7.MetaDependencyPairs.wf_DPPairRev

/-- Source-soundness transport required for the usable-rules route. The statement concerns the
original root relation rather than only the extracted dependency-pair problem. The type records the
implication but does not encode whether its proof comes from a usable-rules processor or from an
independent source-termination proof. -/
structure UsableRulesSourceSoundnessTransport : Prop where
  pairProblemWellFounded_implies_sourceRootTermination :
    WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev →
      WellFounded (fun a b : OperatorKO7.Trace => OperatorKO7.Step b a)

/-- Residual package combining a route-local witness, agreement with the canonical core and route,
and an explicit dependency-pair-to-source well-foundedness implication. -/
structure UsableRulesConfessionRouteResidualObligation where
  Witness : Type
  witness : Witness
  toConfessionCoreWitness : Witness → ConfessionCoreWitness ko7Schema
  toRouteEvidence : Witness → RouteEvidence ko7Schema
  core_agrees :
    (toConfessionCoreWitness witness).toProjectionRank = confessionProjectionCore
  route_agrees :
    toRouteEvidence witness = confessionGenericRouteEvidence
  sourceSoundnessTransport : UsableRulesSourceSoundnessTransport

/-- Existence of a usable-rules residual package carrying explicit dependency-pair-to-source
transport. This proposition records no provenance condition for the transport proof. -/
abbrev HasUsableRulesConfessionRoute : Prop :=
  Nonempty UsableRulesConfessionRouteResidualObligation

/-- Any solution of the usable-rules residual package would project to the same
common generic route-evidence object used by the four routes. -/
theorem usableRulesRouteResidual_projects_common_route
    (R : UsableRulesConfessionRouteResidualObligation) :
    R.toRouteEvidence R.witness = confessionRouteConvergencePackage.commonRouteEvidence := by
  simpa [confessionRouteConvergencePackage] using R.route_agrees

/-! ## Convergence-package projection corollaries

The package fields above are raw equalities. The following corollaries derive
the common route-evidence rank, pairwise agreement of all four routes, and rank
recovery of every route to the canonical DP confession rank. -/

/-- The convergence package's common route-evidence rank function equals the
canonical DP projection. -/
theorem confessionRouteConvergencePackage_commonRouteEvidence_rank :
    confessionRouteConvergencePackage.commonRouteEvidence.rank = dpProjection := rfl

/-- The four route-evidence objects in the convergence package are pairwise
equal: they collapse to one shared object. -/
theorem confessionRouteConvergencePackage_routes_pairwise_agree :
    confessionRouteConvergencePackage.dpRouteEvidence
        = confessionRouteConvergencePackage.counterProjectionRouteEvidence
    ∧ confessionRouteConvergencePackage.dpRouteEvidence
        = confessionRouteConvergencePackage.sctRouteEvidence
    ∧ confessionRouteConvergencePackage.dpRouteEvidence
        = confessionRouteConvergencePackage.argumentFilteringRouteEvidence := by
  refine ⟨?_, ?_, ?_⟩
  · exact confessionRouteConvergencePackage.dp_agrees.trans
      confessionRouteConvergencePackage.counterProjection_agrees.symm
  · exact confessionRouteConvergencePackage.dp_agrees.trans
      confessionRouteConvergencePackage.sct_agrees.symm
  · exact confessionRouteConvergencePackage.dp_agrees.trans
      confessionRouteConvergencePackage.argumentFiltering_agrees.symm

/-- Every route-evidence object in the convergence package recovers the
canonical DP confession rank. This is the rank-level corollary of
`confessionRouteConvergencePackage_routes_pairwise_agree`. -/
theorem confessionRouteConvergencePackage_all_routes_recover_dp_rank :
    confessionRouteConvergencePackage.dpRouteEvidence.rank = dpConfession.rank
    ∧ confessionRouteConvergencePackage.counterProjectionRouteEvidence.rank
        = dpConfession.rank
    ∧ confessionRouteConvergencePackage.sctRouteEvidence.rank
        = dpConfession.rank
    ∧ confessionRouteConvergencePackage.argumentFilteringRouteEvidence.rank
        = dpConfession.rank := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [confessionRouteConvergencePackage.dp_agrees]
    rfl
  · rw [confessionRouteConvergencePackage.counterProjection_agrees]
    rfl
  · rw [confessionRouteConvergencePackage.sct_agrees]
    rfl
  · rw [confessionRouteConvergencePackage.argumentFiltering_agrees]
    rfl

/-- The shared generic route-evidence object also recovers the canonical DP
confession rank. -/
theorem confessionRouteConvergencePackage_commonRouteEvidence_recovers_dp_rank :
    confessionRouteConvergencePackage.commonRouteEvidence.rank = dpConfession.rank := by
  rw [← confessionRouteConvergencePackage.dp_agrees]
  exact confessionRouteConvergencePackage_all_routes_recover_dp_rank.1

end OperatorKO7.ConfessionMethodFamily
