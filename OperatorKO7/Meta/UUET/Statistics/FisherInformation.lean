import OperatorKO7.Meta.UUET.Statistics.Score

set_option autoImplicit false

/-!
# Fisher information of a finite score model

Relation: probability-weighted squared score.
Closure: finite nonnegative sums.
Trust: kernel-only real algebra.
Scope: regular local finite families.
-/

namespace OperatorKO7.Meta.UUET.Statistics

open scoped BigOperators

noncomputable def fisherInformation {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) : ℝ :=
  ∑ ω, F.probability ω * (score F ω) ^ 2

theorem fisher_information_nonneg {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) : 0 <= fisherInformation F := by
  exact Finset.sum_nonneg fun ω _ =>
    mul_nonneg (F.probability_nonnegative ω) (sq_nonneg (score F ω))

theorem constant_family_fisher_zero :
    fisherInformation constantBinaryFamily = 0 := by
  simp [fisherInformation, constant_family_score_zero]

/-- Negative fixture: positive Fisher cannot be equal to zero. -/
theorem positive_fisher_not_zero {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) (h : 0 < fisherInformation F) :
    Not (fisherInformation F = 0) :=
  ne_of_gt h

/-! Imported NameGate and TypeGate. -/
#check @sq_nonneg
#check @score_mean_zero
#check @fisherInformation
#check @fisher_information_nonneg

#check @constant_family_fisher_zero
#check @positive_fisher_not_zero
#print axioms fisher_information_nonneg
#print axioms constant_family_fisher_zero
#print axioms positive_fisher_not_zero

end OperatorKO7.Meta.UUET.Statistics
