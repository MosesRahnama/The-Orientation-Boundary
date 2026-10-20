import OperatorKO7.Meta.ReverseMath.ConfluenceOrderType

/-! Paired reach and axiom gate for ConfluenceOrderType. -/

set_option autoImplicit false

namespace OperatorKO7.Test.ConfluenceOrderTypeReach

open OperatorKO7.ReverseMath

#check @confluence_measure_order_type
#check @confluence_measure_trace_bound
#check @confluence_measure_order_type_lt_epsilon0
#check @confluence_measure_below_epsilon0

#print axioms confluence_measure_order_type
#print axioms confluence_measure_trace_bound
#print axioms confluence_measure_order_type_lt_epsilon0
#print axioms confluence_measure_below_epsilon0

end OperatorKO7.Test.ConfluenceOrderTypeReach
