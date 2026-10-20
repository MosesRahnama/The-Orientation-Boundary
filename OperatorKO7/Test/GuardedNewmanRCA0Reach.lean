import OperatorKO7.Meta.ReverseMath.GuardedNewmanRCA0

/-! Paired reach and axiom gate for GuardedNewmanRCA0. -/

set_option autoImplicit false

namespace OperatorKO7.Test.GuardedNewmanRCA0Reach

open OperatorKO7.Meta.ReverseMath.GuardedNewmanRCA0

#check @GuardedNewmanUpper
#check @safeStep_guardedNewmanUpper
#check @guarded_newman_upper_package
#check @guarded_newman_order_below_epsilon0

#print axioms guarded_newman_upper_package
#print axioms guarded_newman_order_below_epsilon0

end OperatorKO7.Test.GuardedNewmanRCA0Reach
