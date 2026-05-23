import OperatorKO7.Meta.RDRSNonKO7Instances

/-!
# Reach tests for `Meta/RDRSNonKO7Instances.lean`

Phase A.3 Sprint 3 reach companion. Smoke-tests the three non-KO7 RDRS
instance names plus the per-instance gap and strict-inequality smoke
theorems. Deterministic; no Lean call beyond `#check`; no LLM call.
-/

namespace OperatorKO7.StepDuplicating
namespace RDRSNonKO7Instances

#check @textbookRDRS
#check @taggedBinaryRDRS
#check @depthCounterRDRS

#check @TextbookTerm.lhs_x_count_eq_one
#check @TextbookTerm.rhs_x_count_eq_two
#check @TaggedBinaryTerm.lhs_s_count_eq_one
#check @TaggedBinaryTerm.rhs_s_count_eq_two
#check @DepthCounterTerm.lhs_d_count_eq_one
#check @DepthCounterTerm.rhs_d_count_eq_two

#check @textbookRDRS_gap_pos
#check @taggedBinaryRDRS_gap_pos
#check @depthCounterRDRS_gap_pos

#check @textbookRDRS_rhs_strict
#check @taggedBinaryRDRS_rhs_strict
#check @depthCounterRDRS_rhs_strict

-- Smoke: the three instances populate `distinguishedDuplicationGap = 1`.
example : textbookRDRS.distinguishedDuplicationGap = 1 := by
  unfold RightDuplicatingRecursorSchema.distinguishedDuplicationGap
  decide

example : taggedBinaryRDRS.distinguishedDuplicationGap = 1 := by
  unfold RightDuplicatingRecursorSchema.distinguishedDuplicationGap
  decide

example : depthCounterRDRS.distinguishedDuplicationGap = 1 := by
  unfold RightDuplicatingRecursorSchema.distinguishedDuplicationGap
  decide

end RDRSNonKO7Instances
end OperatorKO7.StepDuplicating
