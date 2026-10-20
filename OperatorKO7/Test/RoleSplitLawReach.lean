import OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw

/-!
# Reach gate: role-split law

Pins every public declaration of `OperatorKO7/Meta/BoundaryGeneral/RoleSplitLaw.lean`.
Import-and-check only.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.RoleSplitLawReach

#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.ValueFactored
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.ValueFactored
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.separator_not_valueFactored
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.separator_not_valueFactored
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.diagonal_refuses_every_coordinate
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.diagonal_refuses_every_coordinate
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.value_blind_of_valueFactored
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.value_blind_of_valueFactored
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.boundary_query_trichotomy
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.boundary_query_trichotomy
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.RoleSplit
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.RoleSplit
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.boolSeparator
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.boolSeparator
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.boolSeparator_separates
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.boolSeparator_separates
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.TwoActionBoundary
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.TwoActionBoundary
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.TwoActionBoundary.refuses_valueFactored
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.TwoActionBoundary.refuses_valueFactored
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.TwoActionBoundary.lifts_separator
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.TwoActionBoundary.lifts_separator
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.TwoActionBoundary.separator_is_exogenous
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.TwoActionBoundary.separator_is_exogenous
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.roleSplit_iff
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.roleSplit_iff
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.roleSplit_iff_refuse_lift_exogenous
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.roleSplit_iff_refuse_lift_exogenous
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.valueProj
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.valueProj
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.recursor_roleSplit
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.recursor_roleSplit
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.recursorTwoActionBoundary
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.recursorTwoActionBoundary
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.recursor_two_actions_same_boundary
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.recursor_two_actions_same_boundary
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.recursor_separator_exogenous
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.recursor_separator_exogenous
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.eqW_diagonal_refuses
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.eqW_diagonal_refuses
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.eqW_refuse_face
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.eqW_refuse_face
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.lift_supplies_one_bit
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.lift_supplies_one_bit
#check @OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.boundary_two_actions
#print axioms OperatorKO7.Meta.BoundaryGeneral.RoleSplitLaw.boundary_two_actions

end OperatorKO7.Test.RoleSplitLawReach
