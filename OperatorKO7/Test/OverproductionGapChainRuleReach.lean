import OperatorKO7.Meta.BoundaryGeneral.OverproductionGapChainRule

/-! Paired reach and axiom gate for OverproductionGapChainRule. -/

set_option autoImplicit false

namespace OperatorKO7.Test.OverproductionGapChainRuleReach

open OperatorKO7.Meta.BoundaryGeneral.OverproductionGapChainRule

#check @incrementalGainBits
#check @overproductionGap_evidence_chain_rule
#check @omega_drop_eq_incremental_gain
#check @omega_antitone_in_licensed_gain
#check @omega_strictly_drops_with_strict_gain
#check @fork3_echo_to_resolving_chain_rule

#print axioms overproductionGap_evidence_chain_rule
#print axioms omega_drop_eq_incremental_gain
#print axioms omega_antitone_in_licensed_gain
#print axioms omega_strictly_drops_with_strict_gain
#print axioms fork3_echo_to_resolving_chain_rule

end OperatorKO7.Test.OverproductionGapChainRuleReach
