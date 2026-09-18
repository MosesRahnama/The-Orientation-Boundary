import OperatorKO7.Meta.SafeStep.BranchTransaction
import OperatorKO7.Meta.SafeStep.EqualityWitnessGeneralization

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy

open OperatorKO7 Trace
open MetaSN_KO7

def FalseFormalLegitimacyToken (a b token : Trace) : Prop :=
  token = integrate (merge a b) ∧ ¬ (a ≠ b)

theorem raw_diagonal_emits_false_formal_legitimacy (a : Trace) :
    Step (eqW a a) (integrate (merge a a)) ∧
      FalseFormalLegitimacyToken a a (integrate (merge a a)) :=
  ⟨Step.R_eq_diff a a, rfl, fun h => h rfl⟩

theorem safeStep_refuses_false_formal_legitimacy
    (a token : Trace) (hffl : FalseFormalLegitimacyToken a a token) :
    ¬ SafeStep (eqW a a) token := by
  rcases hffl with ⟨rfl, hno⟩
  intro h
  cases h with
  | R_eq_diff _ _ hne => exact hno hne

theorem diagonal_false_formal_legitimacy_refused_at_void :
    ¬ SafeStep (eqW void void) (integrate (merge void void)) :=
  safeStep_refuses_false_formal_legitimacy void (integrate (merge void void))
    ⟨rfl, fun h => h rfl⟩

#print axioms raw_diagonal_emits_false_formal_legitimacy
#print axioms safeStep_refuses_false_formal_legitimacy
#print axioms diagonal_false_formal_legitimacy_refused_at_void

end OperatorKO7.Meta.SafeStep.FalseFormalLegitimacy
