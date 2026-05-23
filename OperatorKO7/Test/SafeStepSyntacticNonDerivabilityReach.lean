import OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

namespace SafeStepSyntacticNonDerivabilityReach

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.SigmaFreeAlgebra
open OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

-- The W16.7 headline theorem `disequality_not_sigma_expressible` is an
-- unconditional proven proposition discharged by the SigmaFreeAlgebra
-- substitution-invariance lemma. The reach test asserts the
-- unconditional form by name and confirms the seven-arity `SigmaTerm`
-- plus variable-slot signature is in scope.
#check @SigmaTerm
#check @evalSigma
#check @evalSigma_non_leaf_never_void
#check @substitution_invariance
#check @disequality_is_not_substitution_invariant
#check @disequality_not_sigma_expressible_unconditional
#check @disequality_not_sigma_expressible
#check @safestep_guard_requires_external_observer

example : ¬ ∃ (t : SigmaTerm),
    ∀ (a b : SigmaTerm),
      (a ≠ b) ↔ (evalSigma a b t ≠ SigmaTerm.void) :=
  disequality_not_sigma_expressible_unconditional

example : ¬ ∃ (t : SigmaTerm),
    ∀ (a b : SigmaTerm),
      (a ≠ b) ↔ (evalSigma a b t ≠ SigmaTerm.void) :=
  disequality_not_sigma_expressible

end SafeStepSyntacticNonDerivabilityReach
