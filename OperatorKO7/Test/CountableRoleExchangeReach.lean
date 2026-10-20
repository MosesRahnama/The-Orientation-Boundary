import OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange

/-! Paired reach and axiom gate for CountableRoleExchange. -/

set_option autoImplicit false

namespace OperatorKO7.Test.CountableRoleExchangeReach

open OperatorKO7.Meta.BoundaryGeneral.CountableRoleExchange

#check @countableRoleDivergence
#check @countableRoleDivergence_fintype
#check @countableRoleDivergence_uniform
#check @neg_divergence_term_le
#check @countableRoleDivergence_nonneg_of_equal_mass
#check @countableRoleDivergence_nonneg
#check @countableRoleDivergence_self
#check @countable_recovers_finite_role_exchange

#print axioms countableRoleDivergence_fintype
#print axioms countableRoleDivergence_uniform
#print axioms neg_divergence_term_le
#print axioms countableRoleDivergence_nonneg_of_equal_mass
#print axioms countableRoleDivergence_nonneg
#print axioms countableRoleDivergence_self
#print axioms countable_recovers_finite_role_exchange

end OperatorKO7.Test.CountableRoleExchangeReach
