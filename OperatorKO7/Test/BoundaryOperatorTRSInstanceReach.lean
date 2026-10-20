import OperatorKO7.Meta.BoundaryOperator.TRSInstance

namespace BoundaryOperatorTRSInstanceReach

open OperatorKO7.Meta.BoundaryOperator
open OperatorKO7.MetaHalt.Predicate

#check trsConfessionCoreWitness
#check trsRouteEvidence
#check trsConfessionCoreWitness_projects_core
#check trsRouteEvidence_projects_generic_route
#check trsRouteEvidence_projects_forgetting_rank
#check TRSPayloadTag
#check TRSPlugInput
#check trsBoundaryVerdict
#check trsGaugeActionX
#check trsGaugeActionY
#check trsChannel
#check TRS_BoundaryOperator
#check TRS_BoundaryOperator_inhabited
#check TRS_BoundaryOperator_typed_refusal_completeness
#check TRS_LicensedQuotient
#check TRS_BoundaryOperator_factorization
#check TRS_BoundaryOperator_has_licensed_quotient_factorization

example : TRS_BoundaryOperator.domain TRSPlugInput.direct := by
  simp [TRS_BoundaryOperator]

example : TRS_BoundaryOperator.domain TRSPlugInput.shadow := by
  simp [TRS_BoundaryOperator]

example : ¬ TRS_BoundaryOperator.domain TRSPlugInput.blocked := by
  simp [TRS_BoundaryOperator]

example (h : TRS_BoundaryOperator.domain TRSPlugInput.direct) :
    TRS_BoundaryOperator.apply TRSPlugInput.direct h = trsBoundaryVerdict := by
  rfl

example : Nonempty (BoundaryOperator TRSPlugInput TypedOutput) :=
  TRS_BoundaryOperator_inhabited

example : ∃ (Y_typed : Set TypedOutput) (refusal_classifier : TypedOutput → RefusalType),
    Y_typed = Set.univ ∧
      ∀ y, refusal_classifier y ∈ refusalTypeSupport :=
  TRS_BoundaryOperator_typed_refusal_completeness

example : ∃ (LQ : LicensedQuotient TRSPlugInput) (O : LQ.quotient → TypedOutput),
    ∀ x h, TRS_BoundaryOperator.apply x h = O (LQ.proj x) :=
  TRS_BoundaryOperator_has_licensed_quotient_factorization

end BoundaryOperatorTRSInstanceReach
