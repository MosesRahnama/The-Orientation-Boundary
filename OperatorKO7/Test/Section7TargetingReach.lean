import OperatorKO7.Meta.UniqueNormalization.Section7Targeting

#check @OperatorKO7.Meta.UniqueNormalization.BarReachOn.single
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.single
#check @OperatorKO7.Meta.UniqueNormalization.BarReachOn.tail
#print axioms OperatorKO7.Meta.UniqueNormalization.BarReachOn.tail
#check @OperatorKO7.Meta.UniqueNormalization.barReachOn_iff_reflTransGen
#print axioms OperatorKO7.Meta.UniqueNormalization.barReachOn_iff_reflTransGen
#check @OperatorKO7.Meta.UniqueNormalization.Target.pickAt
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.pickAt
#check @OperatorKO7.Meta.UniqueNormalization.Target.pickAt_of_mem
#print axioms OperatorKO7.Meta.UniqueNormalization.Target.pickAt_of_mem
#check @OperatorKO7.Meta.UniqueNormalization.Section7Target.ofTarget
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Target.ofTarget
#check @OperatorKO7.Meta.UniqueNormalization.Section7Target.ofTarget_pick
#print axioms OperatorKO7.Meta.UniqueNormalization.Section7Target.ofTarget_pick
#check @OperatorKO7.Meta.UniqueNormalization.section7Target_nonempty
#print axioms OperatorKO7.Meta.UniqueNormalization.section7Target_nonempty
#check @OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.toTermTargeted
#print axioms OperatorKO7.Meta.UniqueNormalization.TargetedPGraph.toTermTargeted

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @BarStepOn
#check @BarReachOn
#check @BarStepOn.symm
#check @BarReachOn.refl
#check @BarReachOn.trans
#check @BarReachOn.symm
#check @not_conTopped_barStepOn_source
#check @BarReachOn.eq_of_conTopped
#check @HasRootRedexInFiber
#check @Section7Target
#check @Section7Target.mk
#check @Section7Target.pick
#check @Section7Target.pick_mem
#check @Section7Target.inFiber
#check @Section7Target.respectsFiber
#check @Section7Target.redex_if_available
#check @Section7Target.pick_eq_self_of_conTopped
#check @no_rootRedexInFiber_of_conTopped
#check @GuidedParentStep
#check @GuidedReach
#check @TermTargetedPGraph
#check @TermTargetedPGraph.mk
#check @TermTargetedPGraph.graph
#check @TermTargetedPGraph.target
#check @TermTargetedPGraph.guided_or_nf
#check @TermTargetedPGraph.target_edge_exits_fiber
#check @TermTargetedPGraph.Universal
#check @TermTargetedPGraph.constructor_guided

#print axioms BarStepOn
#print axioms BarReachOn
#print axioms BarStepOn.symm
#print axioms BarReachOn.refl
#print axioms BarReachOn.trans
#print axioms BarReachOn.symm
#print axioms not_conTopped_barStepOn_source
#print axioms BarReachOn.eq_of_conTopped
#print axioms HasRootRedexInFiber
#print axioms Section7Target
#print axioms Section7Target.mk
#print axioms Section7Target.pick
#print axioms Section7Target.pick_mem
#print axioms Section7Target.inFiber
#print axioms Section7Target.respectsFiber
#print axioms Section7Target.redex_if_available
#print axioms Section7Target.pick_eq_self_of_conTopped
#print axioms no_rootRedexInFiber_of_conTopped
#print axioms GuidedParentStep
#print axioms GuidedReach
#print axioms TermTargetedPGraph
#print axioms TermTargetedPGraph.mk
#print axioms TermTargetedPGraph.graph
#print axioms TermTargetedPGraph.target
#print axioms TermTargetedPGraph.guided_or_nf
#print axioms TermTargetedPGraph.target_edge_exits_fiber
#print axioms TermTargetedPGraph.Universal
#print axioms TermTargetedPGraph.constructor_guided
