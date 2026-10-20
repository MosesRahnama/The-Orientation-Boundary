import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

/-!
Reach check for `Meta/OperationalInexpressibility/FiberDeficit.lean`: every public
declaration is elaborated and its axiom inventory printed.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.FiberDeficitReach

open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

#check @fiberVerdicts
#check @fiberMultiplicity
#check @fiberDeficit
#check @fiberCodeDeficit
#check @mem_fiberVerdicts
#check @fiberVerdicts_card_le_of_mem
#check @fiberVerdicts_card_le_one_iff
#check @fiberMultiplicity_le_one_iff
#check @fiberDeficit_eq_zero_iff_factorsThrough
#check @fiberDeficit_pos_iff_collision
#check @additional_channel_card_lower_bound
#check @additional_channel_bits_lower_bound
#check @fiberVerdicts_card_le
#check @fiberCodeEmbedding
#check @fiberCode
#check @fiberCode_injective_on_fiber
#check @exists_optimal_side_channel
#check @fiberMultiplicity_is_minimum_side_channel_cardinality
#check @exists_binary_side_channel_at_fiberCodeDeficit
#check @fiberCodeDeficit_is_minimum_fixedLength_bits
#check @fiberMultiplicity_le_of_kernel_refines
#check @fiberDeficit_le_of_kernel_refines
#check @fiberMultiplicity_le_of_refines
#check @fiberDeficit_le_of_refines
#check @valueObserver
#check @roleTarget
#check @two_verdict_multiplicity
#check @two_verdict_deficit
#check @role_channel_closes_two_verdict_deficit
#check @two_verdict_collision
#check @two_verdict_deficit_eq_fork3_zero_evidence_gap

#print axioms fiberVerdicts
#print axioms fiberMultiplicity
#print axioms fiberDeficit
#print axioms fiberCodeDeficit
#print axioms mem_fiberVerdicts
#print axioms fiberVerdicts_card_le_of_mem
#print axioms fiberVerdicts_card_le_one_iff
#print axioms fiberMultiplicity_le_one_iff
#print axioms fiberDeficit_eq_zero_iff_factorsThrough
#print axioms fiberDeficit_pos_iff_collision
#print axioms additional_channel_card_lower_bound
#print axioms additional_channel_bits_lower_bound
#print axioms fiberVerdicts_card_le
#print axioms fiberCodeEmbedding
#print axioms fiberCode
#print axioms fiberCode_injective_on_fiber
#print axioms exists_optimal_side_channel
#print axioms fiberMultiplicity_is_minimum_side_channel_cardinality
#print axioms exists_binary_side_channel_at_fiberCodeDeficit
#print axioms fiberCodeDeficit_is_minimum_fixedLength_bits
#print axioms fiberMultiplicity_le_of_kernel_refines
#print axioms fiberDeficit_le_of_kernel_refines
#print axioms fiberMultiplicity_le_of_refines
#print axioms fiberDeficit_le_of_refines
#print axioms valueObserver
#print axioms roleTarget
#print axioms two_verdict_multiplicity
#print axioms two_verdict_deficit
#print axioms role_channel_closes_two_verdict_deficit
#print axioms two_verdict_collision
#print axioms two_verdict_deficit_eq_fork3_zero_evidence_gap

end OperatorKO7.Test.FiberDeficitReach
