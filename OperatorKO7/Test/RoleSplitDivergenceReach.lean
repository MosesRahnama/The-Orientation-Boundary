import OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw
import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral

/-!
# Reach gate: W2 payload-generic role split and W6 role-gap divergence

Paired `#check @` and `#print axioms` for every declaration added by lanes W2 and W6.
Import-and-check only; this file proves no new content.
-/

set_option maxHeartbeats 1000000

namespace OperatorKO7.Test.RoleSplitDivergenceReach

open OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw
open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapRoleExchangeGeneral

#check @payloadValueProj
#print axioms payloadValueProj
#check @payloadTwoActionBoundary
#print axioms payloadTwoActionBoundary
#check @payload_two_actions_same_boundary
#print axioms payload_two_actions_same_boundary
#check @payload_separator_exogenous
#print axioms payload_separator_exogenous
#check @recursorTwoActionBoundary_eq_payload
#print axioms recursorTwoActionBoundary_eq_payload
#check @payloadValueProj_surjective
#print axioms payloadValueProj_surjective

#check @klFromUniform
#print axioms klFromUniform
#check @klFromUniform_term_split
#print axioms klFromUniform_term_split
#check @klFromUniform_eq_log_card_sub_H
#print axioms klFromUniform_eq_log_card_sub_H
#check @general_role_gap_eq_kl
#print axioms general_role_gap_eq_kl
#check @finite_relation_role_gap_eq_kl
#print axioms finite_relation_role_gap_eq_kl
#check @klFromUniform_nonneg
#print axioms klFromUniform_nonneg
#check @klFromUniform_eq_zero_iff_uniform
#print axioms klFromUniform_eq_zero_iff_uniform

end OperatorKO7.Test.RoleSplitDivergenceReach
