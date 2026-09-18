import OperatorKO7.Meta.DistinctionBoundary.SafeStepDeltaConfluence

/-!
# Reach and axiom gate for OperatorKO7.Meta.DistinctionBoundary.SafeStepDeltaConfluence
-/

set_option autoImplicit false

open OperatorKO7.Meta.DistinctionBoundary.SafeStepDeltaConfluence

#check @Sdelta
#print axioms Sdelta
#check @Sdelta_not_eqW
#print axioms Sdelta_not_eqW
#check @Sdelta_delta
#print axioms Sdelta_delta
#check @Sdelta_integrate
#print axioms Sdelta_integrate
#check @Sdelta_merge
#print axioms Sdelta_merge
#check @Sdelta_app
#print axioms Sdelta_app
#check @Sdelta_recD
#print axioms Sdelta_recD
#check @Sdelta_align
#print axioms Sdelta_align
#check @SafeDelta
#print axioms SafeDelta
#check @SafeDeltaStar
#print axioms SafeDeltaStar
#check @ctxOn_safe_sub_eqGuarded
#print axioms ctxOn_safe_sub_eqGuarded
#check @wf_safeDeltaRev
#print axioms wf_safeDeltaRev
#check @not_safeStep_of_delta
#print axioms not_safeStep_of_delta
#check @not_safeStepCtx_delta_merge
#print axioms not_safeStepCtx_delta_merge
#check @delta_congruence_merge_void
#print axioms delta_congruence_merge_void
#check @expanded_strictly_extends_ctx
#print axioms expanded_strictly_extends_ctx
#check @named_prop_is_confluentOn_safe
#print axioms named_prop_is_confluentOn_safe
#check @safeStep_unique_target
#print axioms safeStep_unique_target
#check @safeStep_target_deltaFlag_zero
#print axioms safeStep_target_deltaFlag_zero
#check @no_safeDelta_from_void
#print axioms no_safeDelta_from_void
#check @kappaM_rec_ne_zero
#print axioms kappaM_rec_ne_zero
#check @kappaM_union_eq_zero
#print axioms kappaM_union_eq_zero
#check @kappaM_zero_of_safeStep
#print axioms kappaM_zero_of_safeStep
#check @kappaM_zero_of_safeDelta
#print axioms kappaM_zero_of_safeDelta
#check @deltaFlag_eq_zero_of_kappaM_zero
#print axioms deltaFlag_eq_zero_of_kappaM_zero
#check @exists_of_deltaFlag_one
#print axioms exists_of_deltaFlag_one
#check @recZero_base_joins
#print axioms recZero_base_joins
#check @mergeVoidRight_joins
#print axioms mergeVoidRight_joins
#check @mergeVoidLeft_joins
#print axioms mergeVoidLeft_joins
#check @safeDelta_root_peak_joins
#print axioms safeDelta_root_peak_joins
#check @safeDelta_local_join
#print axioms safeDelta_local_join
#check @confluent_safeDelta
#print axioms confluent_safeDelta
#check @safeStepDeltaCongruenceConfluent_holds
#print axioms safeStepDeltaCongruenceConfluent_holds
#check @safeStepCtx_already_confluent
#print axioms safeStepCtx_already_confluent
