import OperatorKO7.Meta.BoundaryObserver.NormalFormTarget

/-!
Type and axiom queries for `Meta/BoundaryObserver/NormalFormTarget.lean`, the declarations of
Proposition `prop:normal-form-target` of the source manuscript. Every public declaration of
the module has one `#check` and one `#print axioms`.
-/

open OperatorKO7.Meta.BoundaryObserver

#check @NormalFormTarget.isMergedPair_normalForm_iff
#print axioms NormalFormTarget.isMergedPair_normalForm_iff
#check @NormalFormTarget.mergedPair_normalForm_not_both_normal
#print axioms NormalFormTarget.mergedPair_normalForm_not_both_normal
#check @NormalFormTarget.normalForm_determines_iff_step_invariant
#print axioms NormalFormTarget.normalForm_determines_iff_step_invariant
#check @NormalFormTarget.determines_normalForm_iff
#print axioms NormalFormTarget.determines_normalForm_iff
#check @NormalFormTarget.collision_normalForm_iff
#print axioms NormalFormTarget.collision_normalForm_iff
#check @NormalFormTarget.invariant_determines_normalForm_iff_kernel
#print axioms NormalFormTarget.invariant_determines_normalForm_iff_kernel
#check @NormalFormTarget.ambientClass_determines_normalForm_iff_unc
#print axioms NormalFormTarget.ambientClass_determines_normalForm_iff_unc
#check @NormalFormTarget.five_ambientClass_not_determines_normalForm
#print axioms NormalFormTarget.five_ambientClass_not_determines_normalForm
#check @NormalFormTarget.five_normalForm_mergedPair
#print axioms NormalFormTarget.five_normalForm_mergedPair
