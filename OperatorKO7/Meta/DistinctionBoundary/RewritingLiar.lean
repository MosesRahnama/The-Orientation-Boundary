import OperatorKO7.Meta.SafeStep.EqWVoidAnomaly
import OperatorKO7.Meta.SafeStep.BranchEntropy

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.RewritingLiar

open OperatorKO7 Trace
open OperatorKO7.Meta.SafeStep.EqWVoidAnomaly

/-- A finite rewriting-level liar package: one source emits incompatible truth and difference verdicts. -/
structure DiagonalLemmaInstance : Type where
  source : Trace
  truthVerdict : Trace
  falseDifferenceVerdict : Trace
  truthStep : Step source truthVerdict
  falseDifferenceStep : Step source falseDifferenceVerdict
  unjoinable : ¬ ∃ d, StepStar truthVerdict d ∧ StepStar falseDifferenceVerdict d

/-- `eqW void void` is the canonical rewriting-level liar instance. -/
def eqW_void_void_rewriting_liar : DiagonalLemmaInstance :=
  { source := eqW void void
    truthVerdict := void
    falseDifferenceVerdict := integrate (merge void void)
    truthStep := Step.R_eq_refl void
    falseDifferenceStep := Step.R_eq_diff void void
    unjoinable := eqW_void_void_normal_forms_are_unjoinable }

/-- The liar package carries the same one-bit branch fracture as the entropy theorem. -/
theorem rewriting_liar_has_one_bit_branch_fracture :
    Nonempty DiagonalLemmaInstance
      ∧ OperatorKO7.Meta.SafeStep.BranchEntropy.BranchEntropyCollapse :=
  ⟨⟨eqW_void_void_rewriting_liar⟩,
    OperatorKO7.Meta.SafeStep.BranchEntropy.eqW_void_void_branchEntropy_collapse⟩

#print axioms eqW_void_void_rewriting_liar
#print axioms rewriting_liar_has_one_bit_branch_fracture

end OperatorKO7.Meta.DistinctionBoundary.RewritingLiar
