import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral

set_option autoImplicit false

namespace OperatorKO7.Test.OverproductionGapRoleExchangeGeneralReach

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral

#check @roleWeightsOf
#check @roleResolving_mixture_eq_law
#check @general_valueBlind_gap
#check @general_roleResolving_condEntropyDirect
#check @general_roleResolving_residual_zero
#check @general_roleResolving_deficit
#check @general_roleResolving_deficitBits
#check @general_role_gap
#check @general_role_exchange
#check @general_role_gap_nonneg
#check @H_eq_log_card_iff_eq_uniformMass
#check @HBits_eq_logb_card_iff_eq_uniformMass
#check @general_role_gap_eq_zero_iff
#check @no_role_law_zero
#check @finiteRoleWeightsOf
#check @finiteRoleResolving
#check @finiteRoleResolving_mixture_eq_law
#check @finiteRoleResolving_deficitBits
#check @finite_relation_valueBlind_gap
#check @finite_relation_role_gap
#check @finite_relation_role_exchange
#check @finite_relation_role_gap_nonneg
#check @finite_relation_role_gap_eq_zero_iff
#check @uniform_case
#check @frameUniform
#check @frameUniform_sum_one
#check @H_frameUniform_eq_log
#check @dpChannel
#check @dpChannel_active
#check @dpChannel_frame
#check @dpChannel_mixture_eq_uniform
#check @dpChannel_condEntropyDirect
#check @dpChannel_condEntropyLicensed
#check @dpChannel_deficitBits
#check @activeShareEntropyBits
#check @activeShareEntropyBits_closed
#check @dpChannel_deficitBits_eq_activeShareEntropy
#check @dpChannel_gap
#check @rary_dp_exchange
#check @full_role_resolution_closes
#check @dpChannel_one_eq_roleResolving_two
#check @rary_one_frame
#check @rary_one_frame_eq_one_bit_exchange
#check @frame_ambiguity_pos
#check @rary_zero_nonexample
#check @RaryOcc
#check @raryOccEquiv
#check @raryValue
#check @raryDPChannel
#check @raryDP_separates
#check @raryDP_not_value_factored
#check @raryDPEvidence
#check @raryDP_evidence_eq_dpChannel
#check @raryDPChannel_true_iff_role_zero
#check @raryContractumPayload
#check @raryContractumPayload_eq
#check @rary_occurrence_count
#check @rary_stepRule_occurrence_indexed
#check @rary_license_is_active_bit

#print axioms roleWeightsOf
#print axioms roleResolving_mixture_eq_law
#print axioms general_valueBlind_gap
#print axioms general_roleResolving_condEntropyDirect
#print axioms general_roleResolving_residual_zero
#print axioms general_roleResolving_deficit
#print axioms general_roleResolving_deficitBits
#print axioms general_role_gap
#print axioms general_role_exchange
#print axioms general_role_gap_nonneg
#print axioms H_eq_log_card_iff_eq_uniformMass
#print axioms HBits_eq_logb_card_iff_eq_uniformMass
#print axioms general_role_gap_eq_zero_iff
#print axioms no_role_law_zero
#print axioms finiteRoleWeightsOf
#print axioms finiteRoleResolving
#print axioms finiteRoleResolving_mixture_eq_law
#print axioms finiteRoleResolving_deficitBits
#print axioms finite_relation_valueBlind_gap
#print axioms finite_relation_role_gap
#print axioms finite_relation_role_exchange
#print axioms finite_relation_role_gap_nonneg
#print axioms finite_relation_role_gap_eq_zero_iff
#print axioms uniform_case
#print axioms frameUniform
#print axioms frameUniform_sum_one
#print axioms H_frameUniform_eq_log
#print axioms dpChannel
#print axioms dpChannel_active
#print axioms dpChannel_frame
#print axioms dpChannel_mixture_eq_uniform
#print axioms dpChannel_condEntropyDirect
#print axioms dpChannel_condEntropyLicensed
#print axioms dpChannel_deficitBits
#print axioms activeShareEntropyBits
#print axioms activeShareEntropyBits_closed
#print axioms dpChannel_deficitBits_eq_activeShareEntropy
#print axioms dpChannel_gap
#print axioms rary_dp_exchange
#print axioms full_role_resolution_closes
#print axioms dpChannel_one_eq_roleResolving_two
#print axioms rary_one_frame
#print axioms rary_one_frame_eq_one_bit_exchange
#print axioms frame_ambiguity_pos
#print axioms rary_zero_nonexample
#print axioms RaryOcc
#print axioms raryOccEquiv
#print axioms raryValue
#print axioms raryDPChannel
#print axioms raryDP_separates
#print axioms raryDP_not_value_factored
#print axioms raryDPEvidence
#print axioms raryDP_evidence_eq_dpChannel
#print axioms raryDPChannel_true_iff_role_zero
#print axioms raryContractumPayload
#print axioms raryContractumPayload_eq
#print axioms rary_occurrence_count
#print axioms rary_stepRule_occurrence_indexed
#print axioms rary_license_is_active_bit

end OperatorKO7.Test.OverproductionGapRoleExchangeGeneralReach
