import OperatorKO7.Meta.DistinctionBoundary.GodelFixedPoint

/-!
# Reach and axiom gate for GodelFixedPoint (P-G-0 through P-G-3)
-/

set_option autoImplicit false

open OperatorKO7.Meta.DistinctionBoundary.GodelFixedPoint

#check @selfApplication
#print axioms selfApplication
#check @Represents
#print axioms Represents
#check @represented_composite_has_fixed_point
#print axioms represented_composite_has_fixed_point
#check @not_represents_composite_of_fixed_point_free
#print axioms not_represents_composite_of_fixed_point_free
#check @not_represents_delta_composite
#print axioms not_represents_delta_composite
#check @ClosedUnderLeftDelta
#print axioms ClosedUnderLeftDelta
#check @self_exclusion_of_class
#print axioms self_exclusion_of_class
#check @trivial_not_represents_delta_composite
#print axioms trivial_not_represents_delta_composite
#check @represents_trivial_iff
#print axioms represents_trivial_iff
#check @trivial_represents_id_not_delta
#print axioms trivial_represents_id_not_delta
