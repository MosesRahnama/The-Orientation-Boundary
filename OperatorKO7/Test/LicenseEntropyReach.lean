import OperatorKO7.Meta.OperationalInexpressibility.LicenseEntropy

#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseEntropy.w2_role_information_zero
#print axioms OperatorKO7.Meta.OperationalInexpressibility.LicenseEntropy.w2_role_information_zero
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseEntropy.w2_role_information_chain_rule_all_nat
#print axioms OperatorKO7.Meta.OperationalInexpressibility.LicenseEntropy.w2_role_information_chain_rule_all_nat

/-!
Reach check for `Meta/OperationalInexpressibility/LicenseEntropy.lean`: every public
declaration is elaborated and its axiom inventory printed.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.LicenseEntropyReach

open OperatorKO7.Meta.OperationalInexpressibility.LicenseEntropy

#check @w1FiniteChoiceHartley
#check @w2ActiveFlagShannon
#check @w2FullRoleHartley
#check @w2ResidualFrameShannon
#check @w1FiniteChoiceHartley_two_pow
#check @w1_finite_choice_hartley_unbounded
#check @w2_active_flag_shannon_one_at_binary
#check @w2_active_flag_shannon_le_one
#check @w2_active_flag_shannon_nonneg
#check @w2_role_information_chain_rule
#check @w2_residual_frame_shannon_zero_at_binary
#check @w2_full_role_hartley_one_at_binary
#check @construction_choice_vs_confession_role_profile

#print axioms w1FiniteChoiceHartley
#print axioms w2ActiveFlagShannon
#print axioms w2FullRoleHartley
#print axioms w2ResidualFrameShannon
#print axioms w1FiniteChoiceHartley_two_pow
#print axioms w1_finite_choice_hartley_unbounded
#print axioms w2_active_flag_shannon_one_at_binary
#print axioms w2_active_flag_shannon_le_one
#print axioms w2_active_flag_shannon_nonneg
#print axioms w2_role_information_chain_rule
#print axioms w2_residual_frame_shannon_zero_at_binary
#print axioms w2_full_role_hartley_one_at_binary
#print axioms construction_choice_vs_confession_role_profile

end OperatorKO7.Test.LicenseEntropyReach
