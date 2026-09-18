import OperatorKO7.Meta.UniqueNormalization.HubSplitLinearity

set_option autoImplicit false

open OperatorKO7.Meta.UniqueNormalization

#check @hubSeenStep
#check @hubSeenAfter
#check @encodeHubOccurrences
#check @hubSeenAfter_append
#check @encodeHubOccurrences_append
#check @AllBelowNat
#check @hubFresh_not_mem_encodeHubOccurrences_of_lt
#check @encodeHubOccurrences_nodup_disjoint
#check @hubSplitTermAux_trace
#check @hubSplitListAux_trace
#check @hubSplitTerm_varOccurrences
#check @hubSplitTerm_leftLinear_of_below
#check @hubSplitRuleLhs_leftLinear

#print axioms OperatorKO7.Meta.UniqueNormalization.hubSeenStep
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSeenAfter
#print axioms OperatorKO7.Meta.UniqueNormalization.encodeHubOccurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSeenAfter_append
#print axioms OperatorKO7.Meta.UniqueNormalization.encodeHubOccurrences_append
#print axioms OperatorKO7.Meta.UniqueNormalization.AllBelowNat
#print axioms OperatorKO7.Meta.UniqueNormalization.hubFresh_not_mem_encodeHubOccurrences_of_lt
#print axioms OperatorKO7.Meta.UniqueNormalization.encodeHubOccurrences_nodup_disjoint
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_trace
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_trace
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTerm_varOccurrences
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTerm_leftLinear_of_below
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitRuleLhs_leftLinear
