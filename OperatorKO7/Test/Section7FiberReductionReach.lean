import OperatorKO7.Meta.UniqueNormalization.Section7FiberReduction

/-!
# Reach and axiom gate for the Section 7 fiber reduction

Pins every explicit public declaration of
`OperatorKO7/Meta/UniqueNormalization/Section7FiberReduction.lean`
with a paired axiom query. Baseline axioms only.
-/

set_option autoImplicit false

#check @OperatorKO7.Meta.UniqueNormalization.FiberArgsRepresented
#check @OperatorKO7.Meta.UniqueNormalization.barRel_eqvOn_trans
#check @OperatorKO7.Meta.UniqueNormalization.FiberArgsRepresented.barRel_of_barReachOn
#check @OperatorKO7.Meta.UniqueNormalization.barRel_eqvOn_refl_of_rootStep
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.constructorCompatible_eqvOn
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.rootStepsRepresented_of_fiberArgs
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.fiberArgsRepresented_of_universal
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.universal_iff_fiberArgsRepresented
#check @OperatorKO7.Meta.UniqueNormalization.fiberArgsRepresented_nil
#check @OperatorKO7.Meta.UniqueNormalization.fiberArgsRepresented_of_all_conTopped

#print axioms OperatorKO7.Meta.UniqueNormalization.FiberArgsRepresented
#print axioms OperatorKO7.Meta.UniqueNormalization.barRel_eqvOn_trans
#print axioms OperatorKO7.Meta.UniqueNormalization.FiberArgsRepresented.barRel_of_barReachOn
#print axioms OperatorKO7.Meta.UniqueNormalization.barRel_eqvOn_refl_of_rootStep
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.constructorCompatible_eqvOn
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.rootStepsRepresented_of_fiberArgs
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.fiberArgsRepresented_of_universal
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.universal_iff_fiberArgsRepresented
#print axioms OperatorKO7.Meta.UniqueNormalization.fiberArgsRepresented_nil
#print axioms OperatorKO7.Meta.UniqueNormalization.fiberArgsRepresented_of_all_conTopped

#check @OperatorKO7.Meta.UniqueNormalization.PGraph.complete_of_common_reduct
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.complete_of_common_reduct
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.universal_of_common_reduct
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.universal_of_common_reduct
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.T
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.T
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.wrap
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.wrap
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.constant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.constant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.once
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.once
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.twice
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.twice
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.terms
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.terms
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.terms_coalgebra
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.terms_coalgebra
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.mem_terms
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.mem_terms
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.twice_ne_once
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.twice_ne_once
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.twice_ne_constant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.twice_ne_constant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.once_ne_constant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.once_ne_constant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.constant_conTopped
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.constant_conTopped
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.rule
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.rule
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.rules
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.rules
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.rules_constructor
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.rules_constructor
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.rootStep_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.rootStep_iff
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.rules_rhsDetermined
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.rules_rhsDetermined
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.rules_strong
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.rules_strong
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.root_once
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.root_once
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.root_twice
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.root_twice
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.down_once_constant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.down_once_constant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.down_twice_constant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.down_twice_constant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.down_twice_once
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.down_twice_once
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.down_all
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.down_all
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.bar_twice_once
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.bar_twice_once
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.parent
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.parent
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.parent_edge
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.parent_edge
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.parent_terminating
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.parent_terminating
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.graph
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.graph
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.reach_constant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.reach_constant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.graph_complete
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.graph_complete
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.pick
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.pick
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.target
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.target
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.targeted
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.targeted
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.targeted_universal
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.targeted_universal
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.fiberArgs
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.fiberArgs
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.active_destructor_certificate
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.active_destructor_certificate

/-! ## Complete but nonuniversal graph and actual parent replacement -/

#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.parent
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.parent
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.parent_edge
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.parent_edge
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.parent_terminating
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.parent_terminating
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph
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
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph_complete
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph_complete
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.pick
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.pick
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.target
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.target
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.all_guided
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.all_guided
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.targeted
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.targeted
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.targeted_not_universal
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.targeted_not_universal
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.fiberArgs_not_represented
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.fiberArgs_not_represented
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.complete_targeted_counterexample
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.complete_targeted_counterexample
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.not_every_complete_targeted_graph_universal
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.not_every_complete_targeted_graph_universal
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.selected_redex_returns_to_fiber
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.selected_redex_returns_to_fiber
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.repairedParent
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.repairedParent
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.repairedParent_eq
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.repairedParent_eq
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.parent_replacement_repairs_graph
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.parent_replacement_repairs_graph
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.repair_is_not_edge_preserving
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.repair_is_not_edge_preserving
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.same_coalgebra_complete_universal_and_nonuniversal
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.same_coalgebra_complete_universal_and_nonuniversal

/-! ## The generic repair applied to the same counterexample -/

#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.once_guided_to_twice_root
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.once_guided_to_twice_root
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.any_graph_constant_nf
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.any_graph_constant_nf
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.generic_path_repair
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.generic_path_repair
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.trap_not_equalityComplete
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.trap_not_equalityComplete
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.equality_complete_repair_separates_edge_completion
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.equality_complete_repair_separates_edge_completion

example :
    OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph.Complete ∧
      ¬ OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph.EqualityComplete :=
  ⟨OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph_complete,
    OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.trap_not_equalityComplete⟩

/-! ## Actual reconstructed targets and the zero-distance redex case -/

#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.graph_barClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.graph_barClosed
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.graph_normalRoot_eq_constant
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.graph_normalRoot_eq_constant
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.once_positive_fiberDistance
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.once_positive_fiberDistance
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.reconstruction_selects_actual_exit
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.reconstruction_selects_actual_exit
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.reconstructed_once_parent
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.reconstructed_once_parent
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.reconstructed_active_graph_universal
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.reconstructed_active_graph_universal
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph_barClosed
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.graph_barClosed
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.zero_distance_redex_fiber
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.zero_distance_redex_fiber
#check @OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.reconstructed_trap_still_not_universal
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Active.Trap.reconstructed_trap_still_not_universal

/-! ## Missing-root argument witnesses -/

#check @OperatorKO7.Meta.UniqueNormalization.forall₂_exists_aligned_failure
#print axioms OperatorKO7.Meta.UniqueNormalization.forall₂_exists_aligned_failure
#check @OperatorKO7.Meta.UniqueNormalization.BarReachOn.eq_or_barRel_or_bad_step
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.eq_or_barRel_or_bad_step
#check @OperatorKO7.Meta.UniqueNormalization.BarStepOn.exists_unrepresented_argument
#print axioms OperatorKO7.Meta.UniqueNormalization.BarStepOn.exists_unrepresented_argument
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.missing_root_has_target_exit
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.missing_root_has_target_exit
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.missing_root_has_bad_fiber_step
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.missing_root_has_bad_fiber_step
#check @OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.missing_root_has_unrepresented_argument
#print axioms OperatorKO7.Meta.UniqueNormalization.TermTargetedPGraph.missing_root_has_unrepresented_argument
