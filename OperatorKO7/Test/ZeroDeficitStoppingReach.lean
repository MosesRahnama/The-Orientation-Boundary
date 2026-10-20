import OperatorKO7.Meta.Decision.ZeroDeficitStopping

/-! Paired reach and axiom gate for ZeroDeficitStopping. -/

set_option autoImplicit false

namespace OperatorKO7.Test.ZeroDeficitStoppingReach

open OperatorKO7.Meta.Decision.ZeroDeficitStopping

#check @MetaPolicy
#check @FiniteDecision
#check @cellLoss
#check @directCellLoss
#check @bestCellLoss
#check @bestDirectLoss
#check @expectedStop
#check @expectedComputeNoCost
#check @expectedCompute
#check @valueOfComputation
#check @optimalMetaPolicy
#check @circular_reference_is_zero_deficit
#check @zero_deficit_zero_VOC
#check @positive_cost_zero_deficit_forces_stop
#check @demoLoss
#check @demoDecision
#check @demoStopScore
#check @demoCost
#check @demoZeroDeficitComputeScore
#check @demoPosDeficitComputeScore
#check @demoZeroDeficitOptimal
#check @demoPosDeficitOptimal
#check @demoStopScore_is_min
#check @demo_zero_deficit_optimal_is_stop
#check @demo_pos_deficit_optimal_is_compute
#check @demo_echo_zero_deficit_and_stop
#check @positive_deficit_stop_conclusion_fails
#check @demo_echo_deficit_bracket

#print axioms circular_reference_is_zero_deficit
#print axioms zero_deficit_zero_VOC
#print axioms positive_cost_zero_deficit_forces_stop
#print axioms demoStopScore_is_min
#print axioms demo_zero_deficit_optimal_is_stop
#print axioms demo_pos_deficit_optimal_is_compute
#print axioms demo_echo_zero_deficit_and_stop
#print axioms positive_deficit_stop_conclusion_fails
#print axioms demo_echo_deficit_bracket

end OperatorKO7.Test.ZeroDeficitStoppingReach
