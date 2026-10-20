import OperatorKO7.Meta.Methods.OrientationClosure.ContextLiftMetatheorem

/-! # ContextLiftMetatheorem reach and axiom check -/

set_option autoImplicit false

#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.OrientsFreeContext
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.OrientsFreeContext
#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.free_context_orientation_implies_root
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.free_context_orientation_implies_root
#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.barrier_cell_excludes_context_orientation
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.barrier_cell_excludes_context_orientation
#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.treeSize_barrierCell_every_pair
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.treeSize_barrierCell_every_pair
#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.treeSize_not_context_orienter
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.treeSize_not_context_orienter
#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.interpretation_context_consumption
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.interpretation_context_consumption
#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.interpretation_context_reverse_wellFounded
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.interpretation_context_reverse_wellFounded
#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.minWrapInterpretation
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.minWrapInterpretation
#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.minWrapInterpretation_rootRuleOrients
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.minWrapInterpretation_rootRuleOrients
#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.minWrapInterpretation_not_context_orienter
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.minWrapInterpretation_not_context_orienter
#check @OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.context_lift_controls
#print axioms OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem.context_lift_controls

/-! ## Non-vacuity control at the carrier `Nat` -/

open OperatorKO7.Methods.OrientationClosure.SchemaCore
open OperatorKO7.Methods.OrientationClosure.ContextLiftMetatheorem

/-- The barrier form applies at the carrier `Nat`, at a pair carrying a variable. -/
example : ¬ OrientsFreeContext
    (OperatorKO7.Methods.OrientationClosure.AblationComparisons.treeSize (ν := Nat)) (· < ·) :=
  barrier_cell_excludes_context_orientation _ (FreeTerm.var 0) (FreeTerm.succ (FreeTerm.var 1))
    (treeSize_barrierCell_every_pair Nat _ _).1 (treeSize_barrierCell_every_pair Nat _ _).2
