import OperatorKO7.Meta.UniqueNormalization.Section7SupportSaturation

/-!
# Reach gate for Section 7 staged support saturation
-/

#check @OperatorKO7.Meta.UniqueNormalization.PGraph.pairSetRel
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.pairSetRel
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportPairSet
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportPairSet
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.mem_supportPairSet_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mem_supportPairSet_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportPairSet_subset_pairUniverse
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportPairSet_subset_pairUniverse
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportSuccSet
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportSuccSet
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.mem_supportSuccSet_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mem_supportSuccSet_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_mono_succ
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_mono_succ
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_mono
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_mono
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_subset_pairUniverse
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_subset_pairUniverse
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_sound
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_sound
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_eq_succ_of_eq_succ_at
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_eq_succ_of_eq_succ_at
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_eq_succ_of_eq_succ_of_le
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_eq_succ_of_eq_succ_of_le
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.card_supportIter_ge_of_strict_prefix
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.card_supportIter_ge_of_strict_prefix
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_stabilizes_at_pairUniverse_card
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportIter_stabilizes_at_pairUniverse_card
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportSuccSet_supportClosure
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportSuccSet_supportClosure
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure_subset_pairUniverse
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure_subset_pairUniverse
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure_sound
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.supportClosure_sound
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.rootPeeled_supportClosure_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.rootPeeled_supportClosure_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.context_supportClosure_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.context_supportClosure_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.residualSupportSeedSet
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.residualSupportSeedSet
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.mem_residualSupportSeedSet_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.mem_residualSupportSeedSet_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.residualSupportClosure
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.residualSupportClosure
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.ResidualBatchSpec.residualSupportClosure_sound
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.ResidualBatchSpec.residualSupportClosure_sound
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.rootPeeled_residualSupportClosure_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.rootPeeled_residualSupportClosure_iff
#check @OperatorKO7.Meta.UniqueNormalization.PGraph.context_residualSupportClosure_iff
#print axioms OperatorKO7.Meta.UniqueNormalization.PGraph.context_residualSupportClosure_iff
