import OperatorKO7.Meta.UUET.Statistics.FisherInformation

set_option autoImplicit false

/-!
# Locally unbiased finite estimators

Relation: estimator expectation and its tangent derivative at one parameter.
Closure: tangent normalization converts the derivative identity to score covariance.
Trust: kernel-only finite field algebra.
Scope: local unbiasedness at the family parameter.
-/

namespace OperatorKO7.Meta.UUET.Statistics

open scoped BigOperators

noncomputable def expectation {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) (T : Ω -> ℝ) : ℝ :=
  ∑ ω, F.probability ω * T ω

noncomputable def derivativeExpectation {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) (T : Ω -> ℝ) : ℝ :=
  ∑ ω, F.tangent ω * T ω

/-- An estimator unbiased to first order at the represented parameter. -/
structure UnbiasedEstimator {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) where
  estimate : Ω -> ℝ
  mean_eq_parameter : expectation F estimate = F.parameter
  derivative_eq_one : derivativeExpectation F estimate = 1

noncomputable def scoreCovariance {Ω : Type} [Fintype Ω]
    (F : ParametricFamily Ω) (T : Ω -> ℝ) : ℝ :=
  ∑ ω, F.probability ω * (T ω - F.parameter) * score F ω

theorem scoreCovariance_eq_derivativeExpectation
    {Ω : Type} [Fintype Ω] (F : ParametricFamily Ω) (T : Ω -> ℝ) :
    scoreCovariance F T = derivativeExpectation F T := by
  calc
    scoreCovariance F T = ∑ ω, (T ω - F.parameter) * F.tangent ω := by
      unfold scoreCovariance
      apply Finset.sum_congr rfl
      intro ω _
      rw [score]
      field_simp [ne_of_gt (F.positive_support ω)]
      ring
    _ = ∑ ω, (F.tangent ω * T ω - F.parameter * F.tangent ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = (∑ ω, F.tangent ω * T ω) -
        F.parameter * (∑ ω, F.tangent ω) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = derivativeExpectation F T := by
      rw [F.tangent_total_zero]
      simp [derivativeExpectation]

theorem unbiased_derivative_identity {Ω : Type} [Fintype Ω]
    {F : ParametricFamily Ω} (E : UnbiasedEstimator F) :
    derivativeExpectation F E.estimate = 1 :=
  E.derivative_eq_one

theorem unbiased_score_identity {Ω : Type} [Fintype Ω]
    {F : ParametricFamily Ω} (E : UnbiasedEstimator F) :
    scoreCovariance F E.estimate = 1 := by
  rw [scoreCovariance_eq_derivativeExpectation]
  exact E.derivative_eq_one

/-! Imported NameGate and TypeGate. -/
#check @Finset.sum_sub_distrib
#check @score_mean_zero
#check @UnbiasedEstimator.derivative_eq_one
#check @scoreCovariance

#check @scoreCovariance_eq_derivativeExpectation
#check @unbiased_derivative_identity
#check @unbiased_score_identity
#print axioms scoreCovariance_eq_derivativeExpectation
#print axioms unbiased_derivative_identity
#print axioms unbiased_score_identity

end OperatorKO7.Meta.UUET.Statistics
