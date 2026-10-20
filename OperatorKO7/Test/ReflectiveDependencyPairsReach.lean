import OperatorKO7.Meta.Decision.ReflectiveDependencyPairs

/-!
# Reach and axiom gate for reflective dependency pairs (Roadmap 09, Layer 7.3)

Pins every public declaration of `Meta/Decision/ReflectiveDependencyPairs.lean`,
including constructors and projections. Each `#check` is paired with
`#print axioms`.
-/

set_option autoImplicit false

open OperatorKO7.Meta.Decision.ReflectiveDependencyPairs

-- Carrier
#check OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.Obligation
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.Obligation
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.mk
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.mk
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.metaState
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.metaState
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.activeQuery
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.activeQuery
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.obligations
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.obligations
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.budget
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.budget
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.instDecidableEqMetaQueryState
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.instDecidableEqMetaQueryState
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.rec
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.rec
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.casesOn
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.casesOn
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.noConfusion
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.MetaQueryState.noConfusion
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveStep.rec
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveStep.rec
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveStep.casesOn
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveStep.casesOn

-- Rank and licensed relation
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.rank
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.rank
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.RankLT
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.RankLT
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.wf_RankLT
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.wf_RankLT
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveStep
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveStep
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveStep.budgetDrop
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveStep.budgetDrop
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveStep.obligationDrop
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveStep.obligationDrop
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.reflective_pair_strict_rank
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.reflective_pair_strict_rank
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveLt
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.ReflectiveLt
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.reflective_DP_wellFounded
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.reflective_DP_wellFounded
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.identity_reflective_pair_blocked
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.identity_reflective_pair_blocked
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.mutual_reflective_cycle_requires_descent
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.mutual_reflective_cycle_requires_descent

-- R5 three-state deliberation and unlicensed rank-tie
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.dm_empty_of_singleton
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.dm_empty_of_singleton
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demoS0
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demoS0
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demoS1
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demoS1
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demoS2
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demoS2
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demo_step01
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demo_step01
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demo_step12
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demo_step12
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demoS2_terminal
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demoS2_terminal
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demo_deliberation_terminates
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demo_deliberation_terminates
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.tieA
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.tieA
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.tieB
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.tieB
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.unlicensed_rank_tie_blocked
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.unlicensed_rank_tie_blocked
#check @OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demo_identity_blocked
#print axioms OperatorKO7.Meta.Decision.ReflectiveDependencyPairs.demo_identity_blocked
