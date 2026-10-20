import OperatorKO7.Meta.ReverseMath.GuardedNewmanExactCalibration

/-! Paired reach and axiom gate for GuardedNewmanExactCalibration. -/

set_option autoImplicit false

namespace OperatorKO7.Test.GuardedNewmanExactCalibrationReach

open OperatorKO7.Meta.ReverseMath.GuardedNewmanExactCalibration

#check @GuardedNewmanStatement
#check @guardedNewmanOmegaOmegaTwo
#check @safeStepCtx_order_type_exact
#check @safeStepCtx_order_type_lower_bound
#check @safeStepCtx_order_descriptor_omegaOmega
#check @safeStepCtx_order_descriptor_below_epsilon0
#check @guardedNewmanOmegaOmegaTwo_closes

#print axioms safeStepCtx_order_type_exact
#print axioms safeStepCtx_order_type_lower_bound
#print axioms safeStepCtx_order_descriptor_omegaOmega
#print axioms safeStepCtx_order_descriptor_below_epsilon0
#print axioms guardedNewmanOmegaOmegaTwo_closes

end OperatorKO7.Test.GuardedNewmanExactCalibrationReach
