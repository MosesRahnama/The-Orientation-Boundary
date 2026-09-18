import OperatorKO7.Meta.DistinctionBoundary.UniqueCheck
import OperatorKO7.Meta.DistinctionBoundary.CheckRelocation

/-!
# Reach and axiom gate for the unique-check layer

Every public declaration of `Meta/DistinctionBoundary/UniqueCheck.lean` and
`Meta/DistinctionBoundary/CheckRelocation.lean` is type-checked here and its
axiom footprint printed. Roadmap: `ROADMAP-08-the-unique-check.md`, item 11.4.4.
-/

open OperatorKO7.Meta.DistinctionBoundary.UniqueCheck
open OperatorKO7.Meta.DistinctionBoundary.CheckRelocation

section UniqueCheckReach

#check @SoundEq
#check @CompleteEq
#check @IsCheck
#check @check_unique_pointwise
#check @check_unique
#check @decide_isCheck
#check @check_eq_decide
#check @constTrue_complete_not_sound
#check @constFalse_sound_not_complete
#check @factored_check_forces_injective
#check @injectivity_barrier
#check @no_check_of_collision
#check @no_finiteState_check
#check @truncate
#check @truncate_dpow
#check @no_boundedDepth_check
#check @no_depthOne_check
#check @no_hash_check
#check @trace_infinite
#check @no_hash_check_trace
#check @clone_shaped_instance
#check @structEq_isCheck
#check @structEq_canonical
#check @structEq_canonical_eq
#check @structEq_full_depth_needed
#check @one_check_boundary
#check @distinction_axis_forbids_loss
#check @PayloadBlindAt
#check @payloadBlind_supports_no_check
#check @payloadBlind_nonvacuous
#check @module_nonvacuous

#print axioms check_unique_pointwise
#print axioms check_unique
#print axioms decide_isCheck
#print axioms check_eq_decide
#print axioms constTrue_complete_not_sound
#print axioms constFalse_sound_not_complete
#print axioms factored_check_forces_injective
#print axioms injectivity_barrier
#print axioms no_check_of_collision
#print axioms no_finiteState_check
#print axioms truncate_dpow
#print axioms no_boundedDepth_check
#print axioms no_depthOne_check
#print axioms no_hash_check
#print axioms trace_infinite
#print axioms no_hash_check_trace
#print axioms clone_shaped_instance
#print axioms structEq_isCheck
#print axioms structEq_canonical
#print axioms structEq_canonical_eq
#print axioms structEq_full_depth_needed
#print axioms one_check_boundary
#print axioms distinction_axis_forbids_loss
#print axioms payloadBlind_supports_no_check
#print axioms payloadBlind_nonvacuous
#print axioms module_nonvacuous

end UniqueCheckReach

section CheckRelocationReach

#check @Store
#check @MaxSharing
#check @pointerEq
#check @pointer_sound
#check @pointer_check_iff_maxSharing
#check @maxSharing_iff_denote_injective
#check @pointer_check_forces_injective
#check @SharingInsert
#check @sharing_insert_yields_check
#check @sharing_insert_check_is_structEq
#check @sharing_insert_injective
#check @idStore
#check @idStore_maxSharing
#check @idInsert
#check @idStore_extracted_check_is_structEq
#check @collapsedStore
#check @collapsedStore_admits_no_correct_insert

#print axioms pointer_sound
#print axioms pointer_check_iff_maxSharing
#print axioms maxSharing_iff_denote_injective
#print axioms pointer_check_forces_injective
#print axioms sharing_insert_yields_check
#print axioms sharing_insert_check_is_structEq
#print axioms sharing_insert_injective
#print axioms idStore_maxSharing
#print axioms idStore_extracted_check_is_structEq
#print axioms collapsedStore_admits_no_correct_insert

end CheckRelocationReach
