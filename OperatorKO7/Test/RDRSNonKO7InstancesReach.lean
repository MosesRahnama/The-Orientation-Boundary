import OperatorKO7.Meta.RDRSNonKO7Instances

/-!
# Reach tests for `Meta/RDRSNonKO7Instances.lean`

Phase A.3 Sprint 3 reach companion. Smoke-tests the three non-KO7 RDRS
instance names plus the per-instance gap and strict-inequality smoke
theorems. Deterministic; no Lean call beyond `#check`; no LLM call.
-/

namespace OperatorKO7.StepDuplicating
namespace RDRSNonKO7Instances

open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity

#check @textbookRDRS
#check @taggedBinaryRDRS
#check @depthCounterRDRS

#check @textbookRDRSStep
#check @taggedBinaryRDRSStep
#check @depthCounterRDRSStep

#check @textbookPayloadErasure
#check @taggedBinaryPayloadErasure
#check @depthCounterPayloadErasure

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

#check @textbookRDRSStep_not_direct_decisive_payload_sensitive
#check @taggedBinaryRDRSStep_not_direct_decisive_payload_sensitive
#check @depthCounterRDRSStep_not_direct_decisive_payload_sensitive
#check @rdrs_non_ko7_instances_unconditional
#check @audit_theory_expansion_rdrs_non_ko7_instances_module_anchor

#print axioms rdrs_non_ko7_instances_unconditional

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

example (M : SemanticDirectMeasure TextbookTerm) :
    ¬ PayloadSensitiveDecisive textbookRDRSStep M.data :=
  rdrs_non_ko7_instances_unconditional.1 M

example (M : SemanticDirectMeasure TaggedBinaryTerm) :
    ¬ PayloadSensitiveDecisive taggedBinaryRDRSStep M.data :=
  rdrs_non_ko7_instances_unconditional.2.1 M

example (M : SemanticDirectMeasure DepthCounterTerm) :
    ¬ PayloadSensitiveDecisive depthCounterRDRSStep M.data :=
  rdrs_non_ko7_instances_unconditional.2.2 M

end RDRSNonKO7Instances
end OperatorKO7.StepDuplicating
