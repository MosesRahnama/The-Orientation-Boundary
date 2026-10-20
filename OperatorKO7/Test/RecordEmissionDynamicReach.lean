import OperatorKO7.Meta.RecordEmissionDynamic

/-! Paired reach and axiom gate for RecordEmissionDynamic. -/

set_option autoImplicit false

namespace OperatorKO7.Test.RecordEmissionDynamicReach

open OperatorKO7.Meta.RecordEmissionDynamic

#check @natToCounter
#check @frameStack
#check @canonicalStage
#check @RecordStep
#check @frameStack_frame
#check @recordStep_frameStack
#check @recordStep_canonicalStage_succ
#check @canonicalStage_emitsNewRecordFrame
#check @preservesRecursiveGenerator_frameStack
#check @canonicalStage_preservesRecursiveGenerator
#check @canonicalStage_carries_frame_and_active_generator_positions
#check @every_positive_stage_duplicates_the_generator
#check @canonicalStage_sequence_is_inhabited

#print axioms frameStack_frame
#print axioms recordStep_frameStack
#print axioms recordStep_canonicalStage_succ
#print axioms canonicalStage_emitsNewRecordFrame
#print axioms preservesRecursiveGenerator_frameStack
#print axioms canonicalStage_preservesRecursiveGenerator
#print axioms canonicalStage_carries_frame_and_active_generator_positions
#print axioms every_positive_stage_duplicates_the_generator
#print axioms canonicalStage_sequence_is_inhabited

end OperatorKO7.Test.RecordEmissionDynamicReach
