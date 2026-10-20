import OperatorKO7.Meta.UUET.Statistics.ParametricFamily

set_option autoImplicit false

/-!
# Score of a finite parametric family

Relation: tangent mass divided by strictly positive probability mass.
Closure: normalization derivative forces zero mean score.
Trust: kernel-only field algebra and finite sums.
Scope: regular finite support only.
-/

namespace OperatorKO7.Meta.UUET.Statistics

open scoped BigOperators

noncomputable def score {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) (ω : Ω) : ℝ :=
  F.tangent ω / F.probability ω

theorem probability_mul_score {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) (ω : Ω) :
    F.probability ω * score F ω = F.tangent ω := by
  unfold score
  field_simp [ne_of_gt (F.positive_support ω)]

theorem score_mean_zero {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) :
    (∑ ω, F.probability ω * score F ω) = 0 := by
  calc
    (∑ ω, F.probability ω * score F ω) = ∑ ω, F.tangent ω := by
      apply Finset.sum_congr rfl
      intro ω _
      exact probability_mul_score F ω
    _ = 0 := F.tangent_total_zero

/-- Positive fixture: every score of the constant family is zero. -/
theorem constant_family_score_zero (ω : Fin 2) :
    score constantBinaryFamily ω = 0 := by
  simp [score, constantBinaryFamily]

/-! Imported NameGate and TypeGate. -/
#check @div_eq_mul_inv
#check @ParametricFamily.tangent_total_zero
#check @score
#check @probability_mul_score

#check @score_mean_zero
#check @constant_family_score_zero
#print axioms probability_mul_score
#print axioms score_mean_zero
#print axioms constant_family_score_zero

end OperatorKO7.Meta.UUET.Statistics
