import OperatorKO7.Meta.DistinctionBoundary.Quantitative.WitnessRank
import OperatorKO7.Meta.SafeStep.SyntacticNonDerivability

/-!
# KO7WitnessRank

## Formal Scope

The file defines a grade-threshold fixture: adequacy is the predicate grade >= 1. It contains no typed external-comparator adapter or theorem connecting the checked nonderivability declaration to that threshold.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7WitnessRank

/-- Threshold fixture in which grades at least one are declared adequate. -/
def ko7Adequacy : GradedAdequacy where
  adequate := fun grade => 1 <= grade
  upward := fun hij hi => hi.trans hij
  inhabited := Exists.intro 1 (le_refl 1)

theorem ko7_W0_inadequate : Not (ko7Adequacy.adequate 0) := by simp [ko7Adequacy]
theorem ko7_W1_adequate : ko7Adequacy.adequate 1 := by simp [ko7Adequacy]

theorem ko7_distinction_witnessRank_eq_one : witnessRank ko7Adequacy = 1 := by
  apply le_antisymm
  · exact witnessRank_le_of_adequate ko7Adequacy ko7_W1_adequate
  · by_contra h
    have hz : witnessRank ko7Adequacy = 0 := by omega
    exact ko7_W0_inadequate (hz ▸ witnessRank_adequate ko7Adequacy)

#check OperatorKO7.Meta.SafeStep.SyntacticNonDerivability.disequality_not_sigma_expressible_unconditional
#print axioms ko7_W0_inadequate
#print axioms ko7_distinction_witnessRank_eq_one

end OperatorKO7.Meta.DistinctionBoundary.Quantitative.KO7WitnessRank
