import OperatorKO7.Meta.PolyInterpretation_Family

/-!
Reach check for `Meta/PolyInterpretation_Family.lean`: every public declaration is
elaborated and its axiom inventory printed.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.PolyInterpretationFamilyReach

open OperatorKO7.PolyInterpretation.Family

#check @Wa
#check @Wa_pos
#check @Wa_orients_step
#check @wf_StepRev_Wa
#check @Wa_mono_parameter
#check @Wa_parameter_le_iff_pointwise_le
#check @Wa_recΔ_void_strict
#check @Wa_one_pointwise_le
#check @Wa_one_eq_W
#check @Wa_recΔ_void
#check @Wa_injective
#check @Wa_not_proportional
#check @Wam
#check @Wam_orients_step
#check @Wam_orients_all_steps_iff
#check @Wam_eq_iff
#check @NatProjectivelyEquivalent
#check @Wam_projectivelyEquivalent_iff
#check @Wam_not_projectivelyEquivalent_of_ne
#check @w1_orienting_family
#check @two_nonproportional_orienters
#check @SameFullOrder
#check @sameFullOrder_refl
#check @sameFullOrder_symm
#check @sameFullOrder_trans
#check @fullOrderSetoid
#check @FullOrderQuotient
#check @fullOrderClass
#check @fullOrderClass_eq_iff
#check @Wa_delta_iterate
#check @Wa_delta_iterate_void
#check @Wa_full_order_separating_pair
#check @Wam_full_order_separating_pair
#check @Wam_same_full_order_iff
#check @WamFullOrderClass
#check @WamFullOrderClass_injective
#check @fullOrderQuotient_infinite
#check @RootOrienter
#check @SameRootOrienterFullOrder
#check @sameRootOrienterFullOrder_refl
#check @sameRootOrienterFullOrder_symm
#check @sameRootOrienterFullOrder_trans
#check @rootOrienterFullOrderSetoid
#check @RootOrienterFullOrderQuotient
#check @rootOrienterFullOrderClass
#check @rootOrienterFullOrderClass_eq_iff
#check @WamRootOrienter
#check @WamRootOrienterClass
#check @WamRootOrienterClass_injective
#check @rootOrienterFullOrderQuotient_infinite
#check @StrictlyRecodes
#check @strictlyRecodes_sameFullOrder
#check @Wam_not_strictlyRecodes_of_ne
#check @SameStepOrder
#check @sameStepOrder_refl
#check @sameStepOrder_symm
#check @sameStepOrder_trans
#check @stepOrderSetoid
#check @StepOrderQuotient
#check @stepOrderClass
#check @stepOrderClass_eq_iff
#check @Wam_same_step_order
#check @Wam_stepOrderClass_eq

#print axioms Wa
#print axioms Wa_pos
#print axioms Wa_orients_step
#print axioms wf_StepRev_Wa
#print axioms Wa_mono_parameter
#print axioms Wa_parameter_le_iff_pointwise_le
#print axioms Wa_recΔ_void_strict
#print axioms Wa_one_pointwise_le
#print axioms Wa_one_eq_W
#print axioms Wa_recΔ_void
#print axioms Wa_injective
#print axioms Wa_not_proportional
#print axioms Wam
#print axioms Wam_orients_step
#print axioms Wam_orients_all_steps_iff
#print axioms Wam_eq_iff
#print axioms NatProjectivelyEquivalent
#print axioms Wam_projectivelyEquivalent_iff
#print axioms Wam_not_projectivelyEquivalent_of_ne
#print axioms w1_orienting_family
#print axioms two_nonproportional_orienters
#print axioms SameFullOrder
#print axioms sameFullOrder_refl
#print axioms sameFullOrder_symm
#print axioms sameFullOrder_trans
#print axioms fullOrderSetoid
#print axioms FullOrderQuotient
#print axioms fullOrderClass
#print axioms fullOrderClass_eq_iff
#print axioms Wa_delta_iterate
#print axioms Wa_delta_iterate_void
#print axioms Wa_full_order_separating_pair
#print axioms Wam_full_order_separating_pair
#print axioms Wam_same_full_order_iff
#print axioms WamFullOrderClass
#print axioms WamFullOrderClass_injective
#print axioms fullOrderQuotient_infinite
#print axioms RootOrienter
#print axioms SameRootOrienterFullOrder
#print axioms sameRootOrienterFullOrder_refl
#print axioms sameRootOrienterFullOrder_symm
#print axioms sameRootOrienterFullOrder_trans
#print axioms rootOrienterFullOrderSetoid
#print axioms RootOrienterFullOrderQuotient
#print axioms rootOrienterFullOrderClass
#print axioms rootOrienterFullOrderClass_eq_iff
#print axioms WamRootOrienter
#print axioms WamRootOrienterClass
#print axioms WamRootOrienterClass_injective
#print axioms rootOrienterFullOrderQuotient_infinite
#print axioms StrictlyRecodes
#print axioms strictlyRecodes_sameFullOrder
#print axioms Wam_not_strictlyRecodes_of_ne
#print axioms SameStepOrder
#print axioms sameStepOrder_refl
#print axioms sameStepOrder_symm
#print axioms sameStepOrder_trans
#print axioms stepOrderSetoid
#print axioms StepOrderQuotient
#print axioms stepOrderClass
#print axioms stepOrderClass_eq_iff
#print axioms Wam_same_step_order
#print axioms Wam_stepOrderClass_eq

end OperatorKO7.Test.PolyInterpretationFamilyReach
