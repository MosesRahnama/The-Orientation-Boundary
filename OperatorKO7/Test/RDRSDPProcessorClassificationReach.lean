import OperatorKO7.Meta.RDRSDPProcessorClassification

/-!
# Reachability checks for the RDRS DP processor classification layer.
-/

namespace OperatorKO7.RDRSDPProcessorClassificationReach

open OperatorKO7.RDRSDPProcessorClassification

theorem reach_rdrs_dp_processor_classification_closed :
    RDRSDPProcessorClassificationClosed :=
  rdrs_dp_processor_classification_closed

theorem reach_projection_count :
    projectionStyleProcessors.length = 7 := by
  rfl

theorem reach_inheritance_count :
    inheritanceStyleProcessors.length = 3 := by
  rfl

theorem reach_neutral_count :
    neutralProcessors.length = 5 := by
  rfl

theorem reach_subterm_projection_closes :
    ClosesRDRSByProjection .subtermCriterion :=
  (projectionStyle_iff_closes_by_projection .subtermCriterion).1 rfl

theorem reach_reduction_pair_requires_base_order :
    RequiresDuplicationTolerantBaseOrder .reductionPairProcessor := by
  rfl

theorem reach_narrowing_is_neutral_until_paired :
    NeutralUnlessPaired .narrowing := by
  rfl

theorem reach_usable_rules_no_projection_no_elimination :
    eliminatesDuplicatingRule .usableRulesMinimality .none = false := by
  rfl

theorem reach_usable_rules_projection_elimination :
    eliminatesDuplicatingRule .usableRulesMinimality .withProjection = true := by
  rfl

end OperatorKO7.RDRSDPProcessorClassificationReach
