import OperatorKO7.Meta.ConfessionMethod_Unification

/-!
# Confession-Method Route Evidence

This module is the shared boundary for the generic `RouteEvidence` layer above
the four concrete KO7 confession-method entry routes.

It packages the route-local evidence story in one import:

- the four concrete route witnesses,
- their generic `RouteEvidence` adapters,
- the generic forgetting-witness lift,
- the KO7-local unification theorems showing that all four routes factor
  through one common generic route-evidence object.

The underlying definitions still live where they belong:

- the abstract `RouteEvidence` interface in `StepDuplicatingSchema.lean`,
- the method-specific witness records in the four route files,
- the convergence results in `ConfessionMethod_Unification.lean`.

This file exists to give that distributed layer a single import boundary for
downstream users and for the later public API split.
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

/-! Exact data required for a usable-rules confession route to join the KO7
convergence package honestly. LONG-34 closes the bridge by packaging the
already-shared route evidence together with an explicit standalone soundness
carrier. -/

/-- Route-local witness field for the usable-rules bridge. It records that the
candidate already lives on the same generic route-evidence surface as the four
landed confession routes. -/
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

/-- Standalone soundness package for the usable-rules bridge. It records the
existing Arts-Giesl-licensed DP soundness substrate already carried by the
shared route-evidence object. -/
structure UsableRulesStandaloneSoundnessTheorem : Prop where
  commonRoute_rank_eq_dpConfession :
    confessionRouteConvergencePackage.commonRouteEvidence.rank = dpConfession.rank
  pairProblemWellFounded : WellFounded OperatorKO7.MetaDependencyPairs.DPPairRev
  dpLicense_is_artsGiesl2000 :
    dpConfession.license = SoundnessLicense.artsGiesl2000

theorem usableRulesStandaloneSoundnessTheorem_witness :
    UsableRulesStandaloneSoundnessTheorem := by
  refine ⟨?_, ?_, rfl⟩
  · exact confessionRouteConvergencePackage.commonForgettingWitness_rank.symm.trans
      confessionRouteConvergencePackage_projects_common_forgetting_witness
  exact OperatorKO7.MetaDependencyPairs.wf_DPPairRev

/-- Certification state for a usable-rules bridge. `opaqueBridge` preserves the
conditional theorem surface; `verified` would require the exact route-local
witness field and standalone soundness theorem that are currently absent. -/
inductive UsableRulesBridgeCertification where
  | opaqueBridge
  | verified
      (routeLocalWitness : UsableRulesRouteLocalWitnessField)
      (standaloneSoundness : UsableRulesStandaloneSoundnessTheorem)

/-- Honest admission predicate for a usable-rules bridge certification. -/
def UsableRulesBridgeCertification.IsVerified :
    UsableRulesBridgeCertification → Prop
  | .opaqueBridge => False
  | .verified _ _ => True

theorem usableRulesBridgeCertification_opaque_not_verified :
    ¬ UsableRulesBridgeCertification.opaqueBridge.IsVerified := by
  simp [UsableRulesBridgeCertification.IsVerified]

def usableRulesBridgeCertification_verified_requires_routeLocalWitnessField
  {cert : UsableRulesBridgeCertification}
  (h : cert.IsVerified) :
  UsableRulesRouteLocalWitnessField := by
  cases cert with
  | opaqueBridge =>
    cases h
  | verified routeLocalWitness _ =>
    exact routeLocalWitness

theorem usableRulesBridgeCertification_verified_requires_standaloneSoundnessTheorem
  {cert : UsableRulesBridgeCertification}
  (h : cert.IsVerified) :
  UsableRulesStandaloneSoundnessTheorem := by
  cases cert with
  | opaqueBridge =>
    cases h
  | verified _ standaloneSoundnessProof =>
    exact standaloneSoundnessProof

theorem usableRulesBridgeCertification_isVerified_iff
    {cert : UsableRulesBridgeCertification} :
    cert.IsVerified ↔
      ∃ routeLocalWitness : UsableRulesRouteLocalWitnessField,
        ∃ standaloneSoundness : UsableRulesStandaloneSoundnessTheorem,
          cert = .verified routeLocalWitness standaloneSoundness := by
  cases cert with
  | opaqueBridge =>
      simp [UsableRulesBridgeCertification.IsVerified]
  | verified routeLocalWitness standaloneSoundness =>
      constructor
      · intro _
        exact ⟨routeLocalWitness, standaloneSoundness, rfl⟩
      · intro _
        simp [UsableRulesBridgeCertification.IsVerified]

structure UsableRulesConfessionRouteResidualObligation where
  Witness : Type
  witness : Witness
  toConfessionCoreWitness : Witness → ConfessionCoreWitness ko7Schema
  toRouteEvidence : Witness → RouteEvidence ko7Schema
  core_agrees :
    (toConfessionCoreWitness witness).toProjectionRank = confessionProjectionCore
  route_agrees :
    toRouteEvidence witness = confessionGenericRouteEvidence
  SoundnessTheorem : Prop
  soundnessTheorem : SoundnessTheorem
  bridgeCertification : UsableRulesBridgeCertification

/-- The usable-rules confession gap is closed exactly when the residual
package above is inhabited. -/
abbrev HasUsableRulesConfessionRoute : Prop :=
  ∃ R : UsableRulesConfessionRouteResidualObligation,
    R.bridgeCertification.IsVerified

/-- Any solution of the usable-rules residual package would project to the same
common generic route-evidence object used by the four landed routes. -/
theorem usableRulesRouteResidual_projects_common_route
    (R : UsableRulesConfessionRouteResidualObligation) :
    R.toRouteEvidence R.witness = confessionRouteConvergencePackage.commonRouteEvidence := by
  simpa [confessionRouteConvergencePackage] using R.route_agrees

/-! ## Convergence-package projection corollaries

The package fields above are stated as raw equalities. The four corollaries
below repackage that data in the form most convenient for downstream callers:
the common route-evidence rank, the pairwise agreement of all four routes, and
the rank-recovery of every route to the canonical DP confession rank. They
follow directly from `confessionRouteConvergencePackage`'s own agreement
fields and `confessionGenericRouteEvidence`'s definition; no new mathematical
content is introduced. -/

/-- The convergence package's common route-evidence rank function is exactly
the canonical DP projection. -/
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
