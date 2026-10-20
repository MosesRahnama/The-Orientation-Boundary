import Mathlib

namespace OperatorKO7.Meta.LiteratureReview

/-!
# cor:typed-refusal

Two hidden values with distinct answers and identical conditional transcript laws
force every definite decision rule to incur error mass at least the smaller prior
mass, and a constant report of the more probable answer attains that bound.

The file formalizes only the collision error bound requested by the operator.
The hidden carrier is finite. The transcript carrier is an arbitrary discrete
type with nonnegative summable real masses, so finite and countable transcripts
are included. General nonatomic transcript laws are outside this representation.
The prior is the law already conditioned on the retained history. Error on the
pair means the ambient probability of an erroneous report and membership in the
pair. Division by the pair mass gives the separately stated conditional bound.
Every answer-valued decision is definite; a refusal symbol is not an answer.
-/

namespace TypedRefusal

open scoped BigOperators

noncomputable section

variable {Z T A : Type*} [Fintype Z] [DecidableEq A]

def IsPrior (p : Z → ℝ) : Prop :=
  (∀ z, 0 ≤ p z) ∧ (∑ z, p z) = 1

def IsRow (r : T → ℝ) : Prop :=
  (∀ t, 0 ≤ r t) ∧ HasSum r 1

def IsKernel (K : Z → T → ℝ) : Prop :=
  ∀ z, IsRow (K z)

def errorAt (p : Z → ℝ) (K : Z → T → ℝ)
    (answer : Z → A) (report : T → A) (z : Z) (t : T) : ℝ :=
  if report t = answer z then 0 else p z * K z t

def individualError (p : Z → ℝ) (K : Z → T → ℝ)
    (answer : Z → A) (report : T → A) (z : Z) : ℝ :=
  ∑' t, errorAt p K answer report z t

def pairError (p : Z → ℝ) (K : Z → T → ℝ)
    (answer : Z → A) (z₀ z₁ : Z) (report : T → A) : ℝ :=
  ∑' t, (errorAt p K answer report z₀ t +
    errorAt p K answer report z₁ t)

def totalError (p : Z → ℝ) (K : Z → T → ℝ)
    (answer : Z → A) (report : T → A) : ℝ :=
  ∑ z, individualError p K answer report z

def conditionalPairError (p : Z → ℝ) (K : Z → T → ℝ)
    (answer : Z → A) (z₀ z₁ : Z) (report : T → A) : ℝ :=
  pairError p K answer z₀ z₁ report / (p z₀ + p z₁)

variable {p : Z → ℝ} {K : Z → T → ℝ} {answer : Z → A}
  {z₀ z₁ : Z}

omit [Fintype Z] in
lemma weightedRow_hasSum (p : Z → ℝ) (hK : IsKernel K) (z : Z) :
    HasSum (fun t => p z * K z t) (p z) := by
  simpa only [mul_one] using ((hK z).2.mul_left (p z))

lemma jointMass_sum_one (hp : IsPrior p) (hK : IsKernel K) :
    (∑ z, ∑' t, p z * K z t) = 1 := by
  calc
    (∑ z, ∑' t, p z * K z t) = ∑ z, p z := by
      apply Finset.sum_congr rfl
      intro z _hz
      exact (weightedRow_hasSum p hK z).tsum_eq
    _ = 1 := hp.2

lemma errorAt_nonneg (hp : IsPrior p) (hK : IsKernel K)
    (report : T → A) (z : Z) (t : T) :
    0 ≤ errorAt p K answer report z t := by
  unfold errorAt
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hp.1 z) ((hK z).1 t)

lemma errorAt_le (hp : IsPrior p) (hK : IsKernel K)
    (report : T → A) (z : Z) (t : T) :
    errorAt p K answer report z t ≤ p z * K z t := by
  unfold errorAt
  split_ifs
  · exact mul_nonneg (hp.1 z) ((hK z).1 t)
  · exact le_rfl

lemma errorAt_summable (hp : IsPrior p) (hK : IsKernel K)
    (report : T → A) (z : Z) :
    Summable (errorAt p K answer report z) := by
  exact Summable.of_nonneg_of_le
    (errorAt_nonneg hp hK report z)
    (errorAt_le hp hK report z)
    (weightedRow_hasSum p hK z).summable

lemma individualError_nonneg (hp : IsPrior p) (hK : IsKernel K)
    (report : T → A) (z : Z) :
    0 ≤ individualError p K answer report z := by
  exact tsum_nonneg (errorAt_nonneg hp hK report z)

lemma individualError_le (hp : IsPrior p) (hK : IsKernel K)
    (report : T → A) (z : Z) :
    individualError p K answer report z ≤ p z := by
  exact hasSum_le (errorAt_le hp hK report z)
    (errorAt_summable hp hK report z).hasSum
    (weightedRow_hasSum p hK z)

lemma pairError_eq_add (hp : IsPrior p) (hK : IsKernel K)
    (report : T → A) :
    pairError p K answer z₀ z₁ report =
      individualError p K answer report z₀ +
        individualError p K answer report z₁ := by
  exact (errorAt_summable hp hK report z₀).tsum_add
    (errorAt_summable hp hK report z₁)

lemma pairError_nonneg (hp : IsPrior p) (hK : IsKernel K)
    (report : T → A) :
    0 ≤ pairError p K answer z₀ z₁ report := by
  rw [pairError_eq_add hp hK report]
  exact add_nonneg (individualError_nonneg hp hK report z₀)
    (individualError_nonneg hp hK report z₁)

lemma pairError_le_pairMass (hp : IsPrior p) (hK : IsKernel K)
    (report : T → A) :
    pairError p K answer z₀ z₁ report ≤ p z₀ + p z₁ := by
  rw [pairError_eq_add hp hK report]
  exact add_le_add (individualError_le hp hK report z₀)
    (individualError_le hp hK report z₁)

lemma two_terms_le_sum {f : Z → ℝ} (hf : ∀ z, 0 ≤ f z)
    (hz : z₀ ≠ z₁) :
    f z₀ + f z₁ ≤ ∑ z, f z := by
  classical
  have hmem : z₁ ∈ Finset.univ.erase z₀ := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact Ne.symm hz
  have hsingle : f z₁ ≤ ∑ z ∈ Finset.univ.erase z₀, f z :=
    Finset.single_le_sum (fun z _ => hf z) hmem
  have hsum := Finset.sum_erase_add Finset.univ f (Finset.mem_univ z₀)
  linarith

lemma pairMass_le_one (hp : IsPrior p) (hz : z₀ ≠ z₁) :
    p z₀ + p z₁ ≤ 1 := by
  simpa only [hp.2] using two_terms_le_sum hp.1 hz

lemma pairError_le_totalError (hp : IsPrior p) (hK : IsKernel K)
    (hz : z₀ ≠ z₁) (report : T → A) :
    pairError p K answer z₀ z₁ report ≤ totalError p K answer report := by
  rw [pairError_eq_add hp hK report]
  exact two_terms_le_sum (individualError_nonneg hp hK report) hz

lemma totalError_le_one (hp : IsPrior p) (hK : IsKernel K)
    (report : T → A) :
    totalError p K answer report ≤ 1 := by
  calc
    totalError p K answer report ≤ ∑ z, p z := by
      apply Finset.sum_le_sum
      intro z _hz
      exact individualError_le hp hK report z
    _ = 1 := hp.2

lemma collision_pointwise (hp : IsPrior p) (hK : IsKernel K)
    (hanswer : answer z₀ ≠ answer z₁) (hrows : K z₀ = K z₁)
    (report : T → A) (t : T) :
    min (p z₀) (p z₁) * K z₀ t ≤
      errorAt p K answer report z₀ t + errorAt p K answer report z₁ t := by
  by_cases h₀ : report t = answer z₀
  · have h₁ : report t ≠ answer z₁ := by
      intro h
      exact hanswer (h₀.symm.trans h)
    simpa only [errorAt, if_pos h₀, if_neg h₁, zero_add,
      ← congrFun hrows t] using
      mul_le_mul_of_nonneg_right (min_le_right (p z₀) (p z₁))
        ((hK z₀).1 t)
  · have hfirst :
        min (p z₀) (p z₁) * K z₀ t ≤
          errorAt p K answer report z₀ t := by
      simpa only [errorAt, if_neg h₀] using
        mul_le_mul_of_nonneg_right (min_le_left (p z₀) (p z₁))
          ((hK z₀).1 t)
    exact hfirst.trans
      (le_add_of_nonneg_right (errorAt_nonneg hp hK report z₁ t))

lemma collision_lower_bound (hp : IsPrior p) (hK : IsKernel K)
    (hanswer : answer z₀ ≠ answer z₁) (hrows : K z₀ = K z₁)
    (report : T → A) :
    min (p z₀) (p z₁) ≤ pairError p K answer z₀ z₁ report := by
  have hmin :
      HasSum (fun t => min (p z₀) (p z₁) * K z₀ t)
        (min (p z₀) (p z₁)) := by
    simpa only [mul_one] using
      ((hK z₀).2.mul_left (min (p z₀) (p z₁)))
  exact hasSum_le (collision_pointwise hp hK hanswer hrows report)
    hmin
    ((errorAt_summable hp hK report z₀).add
      (errorAt_summable hp hK report z₁)).hasSum

lemma collision_error_pos (hp : IsPrior p) (hK : IsKernel K)
    (hanswer : answer z₀ ≠ answer z₁) (hrows : K z₀ = K z₁)
    (h₀ : 0 < p z₀) (h₁ : 0 < p z₁) (report : T → A) :
    0 < pairError p K answer z₀ z₁ report := by
  exact lt_of_lt_of_le (lt_min_iff.mpr ⟨h₀, h₁⟩)
    (collision_lower_bound hp hK hanswer hrows report)

lemma conditionalPairError_bounds (hp : IsPrior p) (hK : IsKernel K)
    (hanswer : answer z₀ ≠ answer z₁) (hrows : K z₀ = K z₁)
    (h₀ : 0 < p z₀) (h₁ : 0 < p z₁) (report : T → A) :
    min (p z₀) (p z₁) / (p z₀ + p z₁) ≤
        conditionalPairError p K answer z₀ z₁ report ∧
      conditionalPairError p K answer z₀ z₁ report ≤ 1 := by
  have hmass : 0 < p z₀ + p z₁ := add_pos h₀ h₁
  constructor
  · exact div_le_div_of_nonneg_right
      (collision_lower_bound hp hK hanswer hrows report) hmass.le
  · exact (div_le_one hmass).mpr (pairError_le_pairMass hp hK report)

omit [Fintype Z] in
lemma constant_left_error (hK : IsKernel K)
    (hanswer : answer z₀ ≠ answer z₁) :
    pairError p K answer z₀ z₁ (fun _ => answer z₀) = p z₁ := by
  have hsum := (weightedRow_hasSum p hK z₁).tsum_eq
  simpa only [pairError, errorAt, if_pos rfl, if_neg hanswer,
    ite_true, zero_add] using hsum

omit [Fintype Z] in
lemma constant_right_error (hK : IsKernel K)
    (hanswer : answer z₀ ≠ answer z₁) :
    pairError p K answer z₀ z₁ (fun _ => answer z₁) = p z₀ := by
  have hsum := (weightedRow_hasSum p hK z₀).tsum_eq
  simpa only [pairError, errorAt, if_neg (Ne.symm hanswer), if_pos rfl,
    ite_true, add_zero] using hsum

omit [Fintype Z] in
lemma exists_optimal_pair_report (hK : IsKernel K)
    (hanswer : answer z₀ ≠ answer z₁) :
    ∃ report : T → A,
      (∀ t, report t = answer z₀ ∨ report t = answer z₁) ∧
        pairError p K answer z₀ z₁ report = min (p z₀) (p z₁) := by
  by_cases h : p z₀ ≤ p z₁
  · exists fun _ => answer z₁
    constructor
    · intro t
      exact Or.inr rfl
    · rw [constant_right_error hK hanswer, min_eq_left h]
  · exists fun _ => answer z₀
    constructor
    · intro t
      exact Or.inl rfl
    · rw [constant_left_error hK hanswer, min_eq_right (le_of_not_ge h)]

lemma collision_optimum (hp : IsPrior p) (hK : IsKernel K)
    (hanswer : answer z₀ ≠ answer z₁) (hrows : K z₀ = K z₁) :
    IsLeast
      {r : ℝ | ∃ report : T → A, pairError p K answer z₀ z₁ report = r}
      (min (p z₀) (p z₁)) := by
  constructor
  · obtain ⟨report, _, herror⟩ := exists_optimal_pair_report
      (p := p) hK hanswer
    exact ⟨report, herror⟩
  · intro r hr
    obtain ⟨report, herror⟩ := hr
    rw [← herror]
    exact collision_lower_bound hp hK hanswer hrows report

end

end TypedRefusal

open TypedRefusal

/-- The collision part of cor:typed-refusal, including the sharp conditional bound. -/
theorem typed_refusal
    {Z T A : Type*} [Fintype Z] [DecidableEq A]
    (p : Z → ℝ) (K : Z → T → ℝ) (answer : Z → A) (z₀ z₁ : Z)
    (hp : IsPrior p) (hK : IsKernel K)
    (hz : z₀ ≠ z₁) (h₀ : 0 < p z₀) (h₁ : 0 < p z₁)
    (hanswer : answer z₀ ≠ answer z₁) (hrows : K z₀ = K z₁) :
    (p z₀ + p z₁ ≤ 1) ∧
    (∀ report : T → A,
      min (p z₀) (p z₁) ≤ pairError p K answer z₀ z₁ report ∧
      0 < pairError p K answer z₀ z₁ report ∧
      pairError p K answer z₀ z₁ report ≤ p z₀ + p z₁ ∧
      pairError p K answer z₀ z₁ report ≤ totalError p K answer report ∧
      totalError p K answer report ≤ 1 ∧
      min (p z₀) (p z₁) / (p z₀ + p z₁) ≤
        conditionalPairError p K answer z₀ z₁ report ∧
      conditionalPairError p K answer z₀ z₁ report ≤ 1) ∧
    (∃ report : T → A,
      (∀ t, report t = answer z₀ ∨ report t = answer z₁) ∧
      pairError p K answer z₀ z₁ report = min (p z₀) (p z₁)) ∧
    IsLeast
      {r : ℝ | ∃ report : T → A, pairError p K answer z₀ z₁ report = r}
      (min (p z₀) (p z₁)) := by
  constructor
  · exact pairMass_le_one hp hz
  constructor
  · intro report
    have hc := conditionalPairError_bounds hp hK hanswer hrows h₀ h₁ report
    exact ⟨collision_lower_bound hp hK hanswer hrows report,
      collision_error_pos hp hK hanswer hrows h₀ h₁ report,
      pairError_le_pairMass hp hK report,
      pairError_le_totalError hp hK hz report,
      totalError_le_one hp hK report, hc.1, hc.2⟩
  exact ⟨exists_optimal_pair_report hK hanswer,
    collision_optimum hp hK hanswer hrows⟩

end OperatorKO7.Meta.LiteratureReview
