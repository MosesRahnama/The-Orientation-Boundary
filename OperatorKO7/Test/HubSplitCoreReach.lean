import OperatorKO7.Meta.UniqueNormalization.HubSplitCore

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @HubSplitResult
#check @HubSplitResult.mk
#check @HubSplitResult.term
#check @HubSplitResult.next
#check @HubSplitResult.seen
#check @HubSplitResult.conds
#check @HubSplitListResult
#check @HubSplitListResult.mk
#check @HubSplitListResult.terms
#check @HubSplitListResult.next
#check @HubSplitListResult.seen
#check @HubSplitListResult.conds
#check @hubSplitTermAux
#check @hubSplitListAux
#check @hubSplitTerm
#check @hubSplitConditions
#check @VarOccurrencesBelow
#check @hubSplitTermAux_collapse
#check @hubSplitListAux_collapse
#check @rule_lhs_varOccurrencesBelow
#check @hubSplitRuleLhs_collapse
#check @hubSplitTermAux_next
#check @hubSplitListAux_next
#check @hubSplitTermAux_conds_length_le
#check @hubSplitListAux_conds_length_le
#check @hubSplitConditions_length_le

#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitResult
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitResult.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitResult.term
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitResult.next
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitResult.seen
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitResult.conds
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitListResult
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitListResult.mk
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitListResult.terms
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitListResult.next
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitListResult.seen
#print axioms OperatorKO7.Meta.UniqueNormalization.HubSplitListResult.conds
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitListAux
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTerm
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitConditions
#print axioms OperatorKO7.Meta.UniqueNormalization.VarOccurrencesBelow
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_collapse
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_collapse
#print axioms OperatorKO7.Meta.UniqueNormalization.rule_lhs_varOccurrencesBelow
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitRuleLhs_collapse
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_next
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_next
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_conds_length_le
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_conds_length_le
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitConditions_length_le
