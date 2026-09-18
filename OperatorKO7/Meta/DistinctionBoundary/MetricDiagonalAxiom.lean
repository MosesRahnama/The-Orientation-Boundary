import OperatorKO7.Meta.SafeStep.BranchTransaction
import OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MetricDiagonalAxiom

open OperatorKO7 Trace
open MetaSN_KO7

def DistanceToken (a b token : Trace) : Prop :=
  token = integrate (merge a b)

def ZeroDistanceToken (token : Trace) : Prop :=
  token = void

/-- The diagonal-null half of identity of indiscernibles for a rewrite relation. -/
def DiagonalNull (R : Trace -> Trace -> Prop) : Prop :=
  forall a token, DistanceToken a a token -> Not (R (eqW a a) token)

/-- The unguarded full relation violates diagonal-null by emitting a positive diagonal token. -/
theorem raw_step_violates_metric_diagonal_null (a : Trace) :
    Step (eqW a a) (integrate (merge a a))
      ∧ DistanceToken a a (integrate (merge a a))
      ∧ Not (ZeroDistanceToken (integrate (merge a a))) := by
  refine ⟨Step.R_eq_diff a a, rfl, ?_⟩
  intro h
  cases h

/-- SafeStep satisfies the diagonal-null half for every positive diagonal distance token. -/
theorem safeStep_satisfies_metric_diagonal_null :
    DiagonalNull SafeStep := by
  intro a token htoken hs
  subst htoken
  exact OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy.safeStep_refuses_false_formal_legitimacy
    a (integrate (merge a a)) ⟨rfl, fun h => h rfl⟩ hs

#print axioms raw_step_violates_metric_diagonal_null
#print axioms safeStep_satisfies_metric_diagonal_null

end OperatorKO7.Meta.DistinctionBoundary.MetricDiagonalAxiom
