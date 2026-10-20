import OperatorKO7.Meta.UniqueNormalization.Section7JointClosure

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @TightEdge
#check @TightEdge.mono
#check @TightEdge.toGrey
#check @TightEdge.symm_of_not_root
#check @Grey.symm_of_not_root
#check @PGraph.Tight
#check @PGraph.empty_tight
#check @PGraph.constructorCompatible_eqvOn
#check @PGraph.RootOnly.tight
#check @PGraph.Tight.extend_one
#check @PGraph.TightEqualityComplete
#check @PGraph.Tight.exists_tightEqualityComplete
#check @exists_tightEqualityComplete
#check @exists_tightEqualityComplete_rootStepsRepresented_of_strong
#check @PGraph.TightEqualityComplete.eqvOn_of_nf_tightEdge
#check @TightNonRootReach
#check @TightNonRootReach.toReach
#check @TightNonRootReach.reversible_without_tightness
#check @TightNonRootReach.reversible
#check @Reach.tightNonRoot_or_firstRoot
#check @TightNonRootReach.barReachOn
#check @barRel_eqvOn_refl_of_destructor
#check @TightNonRootReach.barRel_eqvOn
#check @PGraph.Tight.rootRoute
#check @PGraph.Tight.reroot_one
#check @PGraph.Tight.reroot_nonRootReach
#check @PGraph.Tight.repair_rootStep_along_nonRootReach
#check @PGraph.repair_rootStep_along_rootFreeReach
#check @PGraph.EqualityComplete.missing_rootStep_has_first_root_blocker
#check @PGraph.EqualityComplete.missing_rootStep_has_fiber_blocker
#check @PGraph.TightEqualityComplete.rootStepsRepresented_of_sigmaClosedOn
#check @PGraph.TightEqualityComplete.universal_of_sigmaClosedOn

namespace OperatorKO7.Meta.UniqueNormalization.UN79JointClosureReach

open Section7Active

/-- The live trap graph has a root-free parent path from `once` to `twice`. -/
theorem trap_once_twice_rootFree :
    TightNonRootReach Section7Active.Trap.graph once twice := by
  apply TightNonRootReach.head (b := twice)
  · simp [Section7Active.Trap.graph, Section7Active.Trap.parent]
  · intro hroot
    exact (by decide : once ≠ wrap twice) ((rootStep_iff _ _).mp hroot)
  · exact TightNonRootReach.refl _

/-- The root-free path is reversible without a tightness assumption. -/
theorem trap_once_twice_reversible :
    ReversibleReach Section7Active.Trap.graph once twice :=
  trap_once_twice_rootFree.reversible_without_tightness

/-- The same live path stays in the destructor fiber. -/
theorem trap_once_twice_barReach : BarReachOn terms rules once twice :=
  trap_once_twice_rootFree.barReachOn
    ((mem_terms _).2 (Or.inr (Or.inl rfl))) ⟨(), [constant], rfl⟩

/-- The general repair theorem installs the missing live root rewrite while
retaining every equality of the trap graph. -/
theorem trap_root_repair_exists :
    ∃ beta : PGraph terms rules, beta.par once = some constant ∧
      Section7Active.Trap.graph.EqualityExtends beta ∧
      EqvOn terms beta.par once constant := by
  exact Section7Active.Trap.graph.repair_rootStep_along_rootFreeReach
    terms_coalgebra rules_constructor
    ((mem_terms _).2 (Or.inr (Or.inl rfl)))
    ((mem_terms _).2 (Or.inr (Or.inr rfl)))
    trap_once_twice_rootFree
    (by simp [PGraph.NF, Section7Active.Trap.graph, Section7Active.Trap.parent])
    Section7Active.Trap.once_not_eqv_constant root_once

end OperatorKO7.Meta.UniqueNormalization.UN79JointClosureReach

#check @OperatorKO7.Meta.UniqueNormalization.UN79JointClosureReach.trap_once_twice_rootFree
#check @OperatorKO7.Meta.UniqueNormalization.UN79JointClosureReach.trap_once_twice_reversible
#check @OperatorKO7.Meta.UniqueNormalization.UN79JointClosureReach.trap_once_twice_barReach
#check @OperatorKO7.Meta.UniqueNormalization.UN79JointClosureReach.trap_root_repair_exists

#print axioms TightEdge
#print axioms TightEdge.mono
#print axioms TightEdge.toGrey
#print axioms TightEdge.symm_of_not_root
#print axioms Grey.symm_of_not_root
#print axioms PGraph.Tight
#print axioms PGraph.empty_tight
#print axioms PGraph.constructorCompatible_eqvOn
#print axioms PGraph.RootOnly.tight
#print axioms PGraph.Tight.extend_one
#print axioms PGraph.TightEqualityComplete
#print axioms PGraph.Tight.exists_tightEqualityComplete
#print axioms exists_tightEqualityComplete
#print axioms exists_tightEqualityComplete_rootStepsRepresented_of_strong
#print axioms PGraph.TightEqualityComplete.eqvOn_of_nf_tightEdge
#print axioms TightNonRootReach
#print axioms TightNonRootReach.toReach
#print axioms TightNonRootReach.reversible_without_tightness
#print axioms TightNonRootReach.reversible
#print axioms Reach.tightNonRoot_or_firstRoot
#print axioms TightNonRootReach.barReachOn
#print axioms barRel_eqvOn_refl_of_destructor
#print axioms TightNonRootReach.barRel_eqvOn
#print axioms PGraph.Tight.rootRoute
#print axioms PGraph.Tight.reroot_one
#print axioms PGraph.Tight.reroot_nonRootReach
#print axioms PGraph.Tight.repair_rootStep_along_nonRootReach
#print axioms PGraph.repair_rootStep_along_rootFreeReach
#print axioms PGraph.EqualityComplete.missing_rootStep_has_first_root_blocker
#print axioms PGraph.EqualityComplete.missing_rootStep_has_fiber_blocker
#print axioms PGraph.TightEqualityComplete.rootStepsRepresented_of_sigmaClosedOn
#print axioms PGraph.TightEqualityComplete.universal_of_sigmaClosedOn
#print axioms OperatorKO7.Meta.UniqueNormalization.UN79JointClosureReach.trap_once_twice_rootFree
#print axioms OperatorKO7.Meta.UniqueNormalization.UN79JointClosureReach.trap_once_twice_reversible
#print axioms OperatorKO7.Meta.UniqueNormalization.UN79JointClosureReach.trap_once_twice_barReach
#print axioms OperatorKO7.Meta.UniqueNormalization.UN79JointClosureReach.trap_root_repair_exists
