import OperatorKO7.Meta.UniqueNormalization.Lemma64Counterexample

/-!
# Reach and axiom gate for the Lemma 64 counterexample

Pins the public declarations of
`OperatorKO7/Meta/UniqueNormalization/Lemma64Counterexample.lean`.
Baseline axioms only.
-/

set_option autoImplicit false

#check @OperatorKO7.Meta.UniqueNormalization.ConsistencyInvariantOn
#print axioms OperatorKO7.Meta.UniqueNormalization.ConsistencyInvariantOn
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.T
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.T
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.terms
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.terms
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.terms_coalgebra
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.terms_coalgebra
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.rules
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.rules
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.rules_constructor
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.rules_constructor
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.not_mem_terms_var
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.not_mem_terms_var
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.semantic_fork
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.semantic_fork
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.downOn_sigmaClosedOn
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.downOn_sigmaClosedOn
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.downOn_is_consistencyInvariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.downOn_is_consistencyInvariant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph_complete
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph_complete
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.targeted
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.targeted
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.targeted_not_universal
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.targeted_not_universal
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.not_every_complete_targeted_graph_universal
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.not_every_complete_targeted_graph_universal
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.lemma64_as_printed
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.lemma64_as_printed
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.lemma64_fails_as_printed
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.lemma64_fails_as_printed
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.trap_DownOn_is_consistencyInvariant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.trap_DownOn_is_consistencyInvariant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.selected_redex_returns_to_fiber
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.selected_redex_returns_to_fiber
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.induction_promotion_fails
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.induction_promotion_fails
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.repair_requires_parent_change
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.repair_requires_parent_change
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.eqvOn_eq_of_mutual_extends
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.eqvOn_eq_of_mutual_extends
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.reach_eq_of_no_parent
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.reach_eq_of_no_parent
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.once_reach_cases
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.once_reach_cases
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.once_not_eqv_constant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.once_not_eqv_constant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.no_grey_twice_constant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.no_grey_twice_constant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.grey_from_constant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.grey_from_constant

example :
    OperatorKO7.Meta.UniqueNormalization.ConsistencyInvariantOn
      OperatorKO7.Meta.UniqueNormalization.Section7Active.terms
      OperatorKO7.Meta.UniqueNormalization.Section7Active.rules
      (OperatorKO7.Meta.UniqueNormalization.DownOn
        OperatorKO7.Meta.UniqueNormalization.Section7Active.terms
        OperatorKO7.Meta.UniqueNormalization.Section7Active.rules) ∧
      OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph.Complete ∧
      ¬ OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.targeted.Universal :=
  ⟨OperatorKO7.Meta.UniqueNormalization.Section7Active.downOn_is_consistencyInvariant,
    OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph_complete,
    OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.targeted_not_universal⟩
