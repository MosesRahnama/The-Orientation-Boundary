import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Consequences of an assumed real-valued ceiling

`SPRTSubstrate` stores two real numbers, nonnegativity of `expectedRounds`, and the inequality
`expectedRounds ≤ ceiling`. The theorems project that inequality, derive nonnegativity of the
ceiling, and weaken it transitively. No probability space, stopping rule, sequential test, or
boundary-operator instance is defined here.
-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalSPRTBound

/-- Two real values with stored proofs that the first is nonnegative and bounded by the second. -/
structure SPRTSubstrate where
  expectedRounds : ℝ
  ceiling : ℝ
  rounds_nonneg : 0 ≤ expectedRounds
  ceiling_bound : expectedRounds ≤ ceiling

namespace SPRTSubstrate

/-- The defining round-expectation ceiling. -/
theorem bound (S : SPRTSubstrate) : S.expectedRounds ≤ S.ceiling := S.ceiling_bound

/-- The ceiling is nonnegative (it dominates a nonnegative expectation). -/
theorem ceiling_nonneg (S : SPRTSubstrate) : 0 ≤ S.ceiling :=
  le_trans S.rounds_nonneg S.ceiling_bound

/-- Any looser ceiling is still a valid bound (monotone weakening). -/
theorem weaken (S : SPRTSubstrate) {c' : ℝ} (h : S.ceiling ≤ c') :
    S.expectedRounds ≤ c' :=
  le_trans S.ceiling_bound h

end SPRTSubstrate

/-- The numerical fixture `0 ≤ 1 ≤ 2`. -/
def methodTwoSPRT : SPRTSubstrate where
  expectedRounds := 1
  ceiling := 2
  rounds_nonneg := by norm_num
  ceiling_bound := by norm_num

/-- The stored inequality for the numerical fixture. -/
theorem methodTwoSPRT_bound : methodTwoSPRT.expectedRounds ≤ methodTwoSPRT.ceiling :=
  methodTwoSPRT.bound

/-- String naming the bound projection. -/
def universal_sprt_bound_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalSPRTBound.SPRTSubstrate.bound"

end OperatorKO7.Meta.BoundaryOperator.UniversalSPRTBound
