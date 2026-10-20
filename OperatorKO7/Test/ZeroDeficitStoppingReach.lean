import OperatorKO7.Meta.Decision.ZeroDeficitStopping

/-!
Paired reachability and axiom check for ZeroDeficitStopping: one `#check @` and one `#print axioms`
for every public declaration of the module, structure constructors and projections included.
-/

set_option autoImplicit false

#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.MetaPolicy
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.MetaPolicy
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.MetaPolicy.stop
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.MetaPolicy.stop
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.MetaPolicy.compute
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.MetaPolicy.compute
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.FiniteDecision
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.FiniteDecision
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.FiniteDecision.mk
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.FiniteDecision.mk
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.FiniteDecision.actions
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.FiniteDecision.actions
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.FiniteDecision.nonempty
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.FiniteDecision.nonempty
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.FiniteDecision.loss
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.FiniteDecision.loss
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.cellLoss
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.cellLoss
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.directCellLoss
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.directCellLoss
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.bestCellLoss
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.bestCellLoss
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.bestDirectLoss
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.bestDirectLoss
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.expectedStop
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.expectedStop
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.expectedComputeNoCost
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.expectedComputeNoCost
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.expectedCompute
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.expectedCompute
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.valueOfComputation
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.valueOfComputation
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.optimalMetaPolicy
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.optimalMetaPolicy
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.circular_reference_is_zero_deficit
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.circular_reference_is_zero_deficit
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.zero_deficit_zero_VOC
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.zero_deficit_zero_VOC
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.positive_cost_zero_deficit_forces_stop
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.positive_cost_zero_deficit_forces_stop
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoLoss
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoLoss
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoDecision
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoDecision
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoCost
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoCost
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoPrior
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoPrior
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoChannelLaw
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoChannelLaw
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.echoChannel
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.echoChannel
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.revealingChannel
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.revealingChannel
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoHalfCost
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoHalfCost
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoChannelLaw_sum_one
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demoChannelLaw_sum_one
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_echo_expectedStop
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_echo_expectedStop
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_echo_expectedComputeNoCost
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_echo_expectedComputeNoCost
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_revealing_expectedStop
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_revealing_expectedStop
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_revealing_expectedComputeNoCost
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_revealing_expectedComputeNoCost
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_echo_halfCost_policy_stop
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_echo_halfCost_policy_stop
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_revealing_halfCost_policy_compute
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_revealing_halfCost_policy_compute
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_revealing_unitCost_tie
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_revealing_unitCost_tie
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_revealing_unitCost_policy_stop
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_revealing_unitCost_policy_stop
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_echo_zero_deficit_and_stop
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_echo_zero_deficit_and_stop
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.positive_deficit_stop_conclusion_fails
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.positive_deficit_stop_conclusion_fails
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_twoState_instance_halfCost_unitCostControl
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_twoState_instance_halfCost_unitCostControl
#check @OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_echo_deficit_bracket
#print axioms OperatorKO7.Meta.Decision.ZeroDeficitStopping.demo_echo_deficit_bracket
