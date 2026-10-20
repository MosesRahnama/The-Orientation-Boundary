import OperatorKO7.Meta.UUET.Statistics.CramerRao

set_option autoImplicit false

/-!
# Bernoulli score and exact Cramer-Rao fixture

Relation: the two probabilities `(1-p,p)` have tangent `(-1,1)`.
Closure: strict interior parameters give a regular finite score family.
Trust: kernel-only exact real algebra.
Scope: one Bernoulli observation at a local parameter.
-/

namespace OperatorKO7.Meta.UUET.Statistics

open scoped BigOperators

noncomputable def bernoulliFamily (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ParametricFamily (Fin 2) where
  parameter := p
  probability := ![1 - p, p]
  tangent := ![-1, 1]
  probability_nonnegative := by
    intro ω
    fin_cases ω <;> simp <;> linarith
  probability_total := by
    simp [Fin.sum_univ_two]
  tangent_total_zero := by
    simp [Fin.sum_univ_two]
  positive_support := by
    intro ω
    fin_cases ω <;> simp <;> linarith

noncomputable def bernoulliEstimator (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    UnbiasedEstimator (bernoulliFamily p hp0 hp1) where
  estimate := ![0, 1]
  mean_eq_parameter := by
    simp [expectation, bernoulliFamily, Fin.sum_univ_two]
  derivative_eq_one := by
    simp [derivativeExpectation, bernoulliFamily, Fin.sum_univ_two]

noncomputable def bernoulliHalfFamily : ParametricFamily (Fin 2) :=
  bernoulliFamily (1 / 2) (by norm_num) (by norm_num)

noncomputable def bernoulliHalfEstimator : UnbiasedEstimator bernoulliHalfFamily :=
  bernoulliEstimator (1 / 2) (by norm_num) (by norm_num)

theorem bernoulli_half_fisher_exact :
    fisherInformation bernoulliHalfFamily = 4 := by
  norm_num [fisherInformation, score, bernoulliHalfFamily, bernoulliFamily,
    Fin.sum_univ_two]

theorem bernoulli_half_variance_exact :
    estimatorVariance bernoulliHalfFamily bernoulliHalfEstimator.estimate = 1 / 4 := by
  norm_num [estimatorVariance, bernoulliHalfEstimator, bernoulliEstimator,
    bernoulliHalfFamily, bernoulliFamily, Fin.sum_univ_two]

theorem bernoulli_cramer_rao_exact :
    estimatorVariance bernoulliHalfFamily bernoulliHalfEstimator.estimate =
      1 / fisherInformation bernoulliHalfFamily := by
  rw [bernoulli_half_variance_exact, bernoulli_half_fisher_exact]

/-- A biased constant estimator fails the derivative identity and is outside Cramer-Rao. -/
theorem biased_zero_estimator_outside_theorem :
    derivativeExpectation bernoulliHalfFamily (fun _ => 0) = 0 ∧
      Not (derivativeExpectation bernoulliHalfFamily (fun _ => 0) = 1) := by
  norm_num [derivativeExpectation, bernoulliHalfFamily, bernoulliFamily,
    Fin.sum_univ_two]

/-! Imported NameGate and TypeGate. -/
#check @Fin.sum_univ_two
#check @cramer_rao_bound
#check @bernoulliFamily
#check @bernoulliEstimator

#check @bernoulli_half_fisher_exact
#check @bernoulli_half_variance_exact
#check @bernoulli_cramer_rao_exact
#check @biased_zero_estimator_outside_theorem
#print axioms bernoulli_half_fisher_exact
#print axioms bernoulli_half_variance_exact
#print axioms bernoulli_cramer_rao_exact
#print axioms biased_zero_estimator_outside_theorem

end OperatorKO7.Meta.UUET.Statistics
