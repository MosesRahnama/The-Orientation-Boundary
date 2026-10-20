import OperatorKO7.Meta.Methods.OrientationClosure.MethodUniverseClosure

/-!
# The two method tables agree

`RDRSTerminationMethodUniverse.statusOf` classifies each of the 76 termination methods in a finer
vocabulary than the verdict `MethodUniverseClosure.methodVerdict` of the methods table. The barrier
status admits only the barrier verdict and the escape status only the escape verdict. The statuses
`conditional_escape`, `nonconservative_escape`, `definitional_admitter` and `import_dependent` admit
an escape on the whole system or on a fragment. The statuses `conditional_barrier`, `not_applicable`
and `external_non_lane_problem` fix no polarity. Every row of the finer table admits the verdict of
the closure table, so the two tables agree on all 76 methods, and a row whose status is `escape`
carries the orienting result that the closure table proves.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.MethodStatusAgreement

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.Methods.OrientationClosure.MethodUniverseClosure

/-- The closure verdicts that each status of the finer table admits. -/
def statusAdmits : RDRSMethodStatus → MethodVerdict → Bool
  | .barrier, v => v == .barrier
  | .escape, v => v == .escape
  | .conditional_escape, v => v == .escape || v == .fragmentEscape
  | .nonconservative_escape, v => v == .escape || v == .fragmentEscape
  | .definitional_admitter, v => v == .escape || v == .fragmentEscape
  | .import_dependent, v => v == .escape || v == .fragmentEscape
  | .conditional_barrier, _ => true
  | .not_applicable, _ => true
  | .external_non_lane_problem, _ => true

/-- Every one of the 76 methods has a status in the finer table that admits its verdict in the
closure table. -/
theorem statusOf_agrees_methodVerdict :
    ∀ f : RDRSMethodFamily, statusAdmits (statusOf f) (methodVerdict f) = true := by
  intro f
  cases f <;> rfl

/-- A method with the barrier status has the barrier verdict. -/
theorem methodVerdict_of_statusOf_barrier (f : RDRSMethodFamily)
    (h : statusOf f = .barrier) : methodVerdict f = .barrier := by
  have hf := statusOf_agrees_methodVerdict f
  rw [h] at hf
  simpa [statusAdmits] using hf

/-- A method with the escape status has the escape verdict. -/
theorem methodVerdict_of_statusOf_escape (f : RDRSMethodFamily)
    (h : statusOf f = .escape) : methodVerdict f = .escape := by
  have hf := statusOf_agrees_methodVerdict f
  rw [h] at hf
  simpa [statusAdmits] using hf

/-- A method with the escape verdict never carries the barrier status. -/
theorem statusOf_ne_barrier_of_escape (f : RDRSMethodFamily)
    (h : methodVerdict f = .escape) : statusOf f ≠ .barrier := by
  intro hb
  have := methodVerdict_of_statusOf_barrier f hb
  rw [h] at this
  exact absurd this (by decide)

/-- A method with the barrier verdict carries the barrier, conditional barrier or inapplicable
status. -/
theorem statusOf_of_methodVerdict_barrier (f : RDRSMethodFamily)
    (h : methodVerdict f = .barrier) :
    statusOf f = .barrier ∨ statusOf f = .conditional_barrier ∨ statusOf f = .not_applicable := by
  cases f <;> simp_all [methodVerdict, statusOf]

/-- A method with the escape status carries the orienting result that the closure table proves for
its row. -/
theorem methodResult_of_statusOf_escape (f : RDRSMethodFamily) (_h : statusOf f = .escape) :
    MethodResult f (methodWitness f) :=
  methodWitness_result f

/-- The seven rows that follow the methods table of the paper: six escapes and one barrier. -/
theorem seven_rows_follow_paper :
    statusOf .generalizedKBO = .escape ∧ statusOf .popStarFamily = .escape ∧
      statusOf .maxPolynomial = .escape ∧ statusOf .multilinearInterpretation = .escape ∧
      statusOf .strictMonotoneAlgebraArchimedean = .escape ∧
      statusOf .raiseConsistencyMatchBounds = .escape ∧ statusOf .typeIntroduction = .barrier :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end OperatorKO7.Methods.OrientationClosure.MethodStatusAgreement
