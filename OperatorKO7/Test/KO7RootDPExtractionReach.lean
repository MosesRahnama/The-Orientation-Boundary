import OperatorKO7.Meta.DistinctionBoundary.KO7RootDPExtraction

/-!
# Reach and axiom gate for OperatorKO7.Meta.DistinctionBoundary.KO7RootDPExtraction
-/

set_option autoImplicit false

open OperatorKO7.Meta.DistinctionBoundary.KO7RootDPExtraction

#check @isRecSuccRedex
#print axioms isRecSuccRedex
#check @extractsDP
#print axioms extractsDP
#check @extractsDP_recSucc
#print axioms extractsDP_recSucc
#check @extractsDP_iff
#print axioms extractsDP_iff
#check @dpPair_iff
#print axioms dpPair_iff
#check @extraction_sound
#print axioms extraction_sound
#check @extraction_complete
#print axioms extraction_complete
#check @seven_rules_pair_free
#print axioms seven_rules_pair_free
#check @processor_rank_decrease
#print axioms processor_rank_decrease
#check @processor_wf
#print axioms processor_wf
#check @SpuriousPair
#print axioms SpuriousPair
#check @SpuriousPair.extra
#print axioms SpuriousPair.extra
#check @spurious_not_step
#print axioms spurious_not_step
#check @spurious_not_dpPair
#print axioms spurious_not_dpPair
#check @recSucc_nonvacuous
#print axioms recSucc_nonvacuous
#check @processor_sound
#print axioms processor_sound
