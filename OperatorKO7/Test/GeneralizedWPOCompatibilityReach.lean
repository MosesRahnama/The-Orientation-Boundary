import OperatorKO7.Meta.GeneralizedWPOCompatibility

/-!
# Reach tests for `Meta/GeneralizedWPOCompatibility.lean`
-/

set_option autoImplicit false

namespace OperatorKO7.Test.GeneralizedWPOCompatibilityReach

open OperatorKO7.GeneralizedWPOCompatibility

#check GeneralizedWPOAlgebraicBranch
#check generalized_wpo_algebraic_branch
#check GeneralizedWPOOutOfDirectLane
#check generalized_wpo_out_of_direct_lane
#check GeneralizedWPOCompatibility
#check generalized_wpo_compatibility_exact
#check audit_theory_expansion_generalized_wpo_compatibility_module_anchor

#print axioms generalized_wpo_compatibility_exact

example : GeneralizedWPOAlgebraicBranch :=
  generalized_wpo_algebraic_branch

example : GeneralizedWPOOutOfDirectLane :=
  generalized_wpo_out_of_direct_lane

end OperatorKO7.Test.GeneralizedWPOCompatibilityReach
