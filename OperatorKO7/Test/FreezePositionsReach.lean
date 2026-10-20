import OperatorKO7.Meta.DistinctionBoundary.FreezePositions

/-!
# Freeze-positions reach gate (ROADMAP-09 F3)

Pins every public declaration of
`Meta/DistinctionBoundary/FreezePositions.lean`. Each `#check` is paired
with `#print axioms` (LASOT Q24 reach/axiom parity).

Outcome pinned here: the dispatch's one-sided candidate
`ConfluentOnPos ↔ (¬ eqW ∧ (recD → appR))` is refuted
(`confluentOnPos_appR_only_iff_refuted`) at `recSPeak`; the corrected crown
is `confluentOnPos_eqGuarded_iff`.
-/

set_option autoImplicit false

open OperatorKO7.Meta.DistinctionBoundary.FreezePositions

#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.void
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.void
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.delta
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.delta
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.integrate
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.integrate
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.merge
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.merge
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.appL
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.appL
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.appR
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.appR
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.recD
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.recD
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.eqW
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtorPos.eqW

#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.root
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.root
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.delta
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.delta
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.integrate
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.integrate
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.mergeL
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.mergeL
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.mergeR
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.mergeR
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.appL
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.appL
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.appR
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.appR
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.recB
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.recB
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.recS
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.recS
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.recN
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.recN
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.eqWL
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.eqWL
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.eqWR
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPos.eqWR

#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxStarPos
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxStarPos
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ConfluentOnPos
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ConfluentOnPos
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPosRev
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.CtxOnPosRev

#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ofCtor
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ofCtor
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxOnPos_eqGuarded_sub_stepCtxFull
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxOnPos_eqGuarded_sub_stepCtxFull
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.wf_ctxOnPos_eqGuarded_rev
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.wf_ctxOnPos_eqGuarded_rev
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxOnPos_ofCtor_iff_ctxOn
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxOnPos_ofCtor_iff_ctxOn
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.conf_bridge_pos
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.conf_bridge_pos

#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.selAppRThawed
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.selAppRThawed
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.selAppRFrozen
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.selAppRFrozen
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.b1Peak
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.b1Peak
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.b1RootReduct
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.b1RootReduct
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.b1CongReduct
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.b1CongReduct
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.b1ExpectedJoin
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.b1ExpectedJoin
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxOnPos_app_void_left_stuck
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxOnPos_app_void_left_stuck
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.OnB1CongCone
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.OnB1CongCone
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onB1CongCone_step
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onB1CongCone_step
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onB1CongCone_star
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onB1CongCone_star
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.positional_peak_joins_appR_thawed
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.positional_peak_joins_appR_thawed
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.positional_peak_stuck_appR_frozen
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.positional_peak_stuck_appR_frozen

#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.instabilityWitness
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.instabilityWitness
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.instabilityDifferenceVerdict
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.instabilityDifferenceVerdict
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.instabilityWitness_to_difference
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.instabilityWitness_to_difference
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.instabilityWitness_to_void
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.instabilityWitness_to_void
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.OnInstabilityDifferenceCone
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.OnInstabilityDifferenceCone
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onInstabilityDifferenceCone_step
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onInstabilityDifferenceCone_step
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onInstabilityDifferenceCone_star
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onInstabilityDifferenceCone_star
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.void_not_onInstabilityDifferenceCone
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.void_not_onInstabilityDifferenceCone
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.instabilityDifference_not_joinable_void
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.instabilityDifference_not_joinable_void
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.eqW_congruence_breaks_confluence_pos
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.eqW_congruence_breaks_confluence_pos
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.recD_thaw_appR_freeze_breaks_confluence
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.recD_thaw_appR_freeze_breaks_confluence

#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.recSPeak
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.recSPeak
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.recSRootReduct
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.recSRootReduct
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.recSCongReduct
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.recSCongReduct
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.OnRecSCongCone
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.OnRecSCongCone
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onRecSCongCone_step
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onRecSCongCone_step
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onRecSCongCone_star
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.onRecSCongCone_star
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.app_mergeVoid_not_onRecSCongCone
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.app_mergeVoid_not_onRecSCongCone
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.recD_thaw_appL_freeze_breaks_confluence
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.recD_thaw_appL_freeze_breaks_confluence
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.confluentOnPos_appR_only_iff_refuted
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.confluentOnPos_appR_only_iff_refuted

#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_delta
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_delta
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_integrate
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_integrate
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_mergeL
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_mergeL
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_mergeR
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_mergeR
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_appL
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_appL
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_appR
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_appR
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_recB
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_recB
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_recS
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_recS
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_recN
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxStarPos_recN
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxOnPos_root_peak_joins
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxOnPos_root_peak_joins
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxOnPos_local_join
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.ctxOnPos_local_join
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.freeze_eqW_recAppPosAligned_restores_confluence
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.freeze_eqW_recAppPosAligned_restores_confluence
#check @OperatorKO7.Meta.DistinctionBoundary.FreezePositions.confluentOnPos_eqGuarded_iff
#print axioms OperatorKO7.Meta.DistinctionBoundary.FreezePositions.confluentOnPos_eqGuarded_iff
