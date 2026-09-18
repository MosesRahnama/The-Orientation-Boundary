import OperatorKO7.Meta.DistinctionBoundary.SemanticsPreservingMaximality
import OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.LawvereObstruction

open OperatorKO7 Trace
open MetaSN_KO7

/-- Finite fixed-point obstruction at a single `eqW a a` diagonal. -/
structure FiniteFixedPointObstruction (a : Trace) : Prop where
  reflexiveBranch : Step (eqW a a) void
  totalizedDifferenceBranch : Step (eqW a a) (integrate (merge a a))
  differenceTokenFalse :
    OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy.FalseFormalLegitimacyToken
      a a (integrate (merge a a))
  verdictsDoNotJoin :
    ¬ ∃ d, StepStar void d ∧ StepStar (integrate (merge a a)) d

/-- The canonical KO7 diagonal is a finite fixed-point obstruction. -/
theorem eqW_void_void_finite_fixed_point_obstruction :
    FiniteFixedPointObstruction void :=
  { reflexiveBranch := Step.R_eq_refl void
    totalizedDifferenceBranch := Step.R_eq_diff void void
    differenceTokenFalse :=
      (OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy.raw_diagonal_emits_false_formal_legitimacy void).2
    verdictsDoNotJoin :=
      OperatorKO7.Meta.DistinctionBoundary.void_integrate_merge_self_not_joinable void }

/-- SafeStep is the finite restriction that refuses the false fixed-point difference token. -/
theorem safeStep_restricts_fixed_point_difference :
    ¬ SafeStep (eqW void void) (integrate (merge void void)) :=
  OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy.safeStep_refuses_false_formal_legitimacy
    void (integrate (merge void void)) ⟨rfl, fun h => h rfl⟩

#print axioms eqW_void_void_finite_fixed_point_obstruction
#print axioms safeStep_restricts_fixed_point_difference

end OperatorKO7.Meta.DistinctionBoundary.LawvereObstruction
