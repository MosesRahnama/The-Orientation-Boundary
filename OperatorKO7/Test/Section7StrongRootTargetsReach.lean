import OperatorKO7.Meta.UniqueNormalization.Section7StrongRootTargets

#check @OperatorKO7.Meta.UniqueNormalization.root_deterministic_of_finite_common_generalisations
#print axioms OperatorKO7.Meta.UniqueNormalization.root_deterministic_of_finite_common_generalisations

#check @OperatorKO7.Meta.UniqueNormalization.StronglyAlmostNonOmegaOverlapping.deterministic
#print axioms OperatorKO7.Meta.UniqueNormalization.StronglyAlmostNonOmegaOverlapping.deterministic

#check @OperatorKO7.Meta.UniqueNormalization.Deterministic.rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.Deterministic.rhsDetermined

#check @OperatorKO7.Meta.UniqueNormalization.StronglyAlmostNonOmegaOverlapping.rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.StronglyAlmostNonOmegaOverlapping.rhsDetermined

#check @OperatorKO7.Meta.UniqueNormalization.StronglyAlmostNonOmegaOverlapping.almost
#print axioms OperatorKO7.Meta.UniqueNormalization.StronglyAlmostNonOmegaOverlapping.almost

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @TermTargetedPGraph.target_rootStep_eqvOn_of_complete_strong
#print axioms TermTargetedPGraph.target_rootStep_eqvOn_of_complete_strong

#check @OperatorKO7.Meta.UniqueNormalization.constructorCompatible_equality
#print axioms OperatorKO7.Meta.UniqueNormalization.constructorCompatible_equality
#check @OperatorKO7.Meta.UniqueNormalization.sigmaClosed_equality
#print axioms OperatorKO7.Meta.UniqueNormalization.sigmaClosed_equality
#check @OperatorKO7.Meta.UniqueNormalization.CT_equality_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.CT_equality_iff
#check @OperatorKO7.Meta.UniqueNormalization.root_deterministic_of_strong
#print axioms OperatorKO7.Meta.UniqueNormalization.root_deterministic_of_strong

open OperatorKO7.Meta.Rewriting in
example : Deterministic
    ([{ lhs := .app 0 [.var 0], rhs := .var 0, lhs_isApp := rfl }] : TRS Nat Nat) := by
  apply root_deterministic_of_finite_common_generalisations
  intro r hr s hs _
  simp only [List.mem_singleton] at hr hs
  subst r
  subst s
  refine ⟨CommonGeneralisation.self _ ?_⟩
  intro a b hab
  simpa only [Subst.apply_app, Subst.applyList_eq_map, List.map_cons, List.map_nil,
    Term.app.injEq, true_and, List.cons.injEq, and_true, Subst.apply_var] using hab

example : ¬ Deterministic FreshRhs.trs := by
  intro h
  exact FreshRhs.not_rhsDetermined h.rhsDetermined
