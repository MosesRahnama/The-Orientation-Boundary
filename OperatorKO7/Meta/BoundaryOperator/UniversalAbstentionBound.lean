import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Universal confidence-targeted abstention bound (T13.UN-2)

This module packages a confidence target `τ ∈ [0,1]` together with an abstention
probability bounded by `1 - τ`. The stored bound yields a monotone ceiling and an
acceptance lower bound. `methodOneAbstentionBound` is an illustrative rational
fixture with values `3/4` and `1/4`; it carries no adapter from a decoder theorem.
-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalAbstentionBound

/-- A confidence-targeted abstention bound: a confidence target `τ` in `[0,1]` and
an abstention probability `pAbstain` guaranteed to be at most `1 - τ`. -/
structure AbstentionBound where
  tau : ℝ
  pAbstain : ℝ
  tau_nonneg : 0 ≤ tau
  tau_le_one : tau ≤ 1
  bound : pAbstain ≤ 1 - tau

namespace AbstentionBound

/-- The defining abstention guarantee. -/
theorem pAbstain_le (A : AbstentionBound) : A.pAbstain ≤ 1 - A.tau := A.bound

/-- The acceptance probability (`1 - pAbstain`) is at least the confidence target. -/
theorem acceptance_ge_target (A : AbstentionBound) : A.tau ≤ 1 - A.pAbstain := by
  have := A.bound; linarith

/-- A higher confidence target gives a tighter abstention ceiling. -/
theorem ceiling_antitone (A B : AbstentionBound) (h : A.tau ≤ B.tau) :
    1 - B.tau ≤ 1 - A.tau := by linarith

end AbstentionBound

/-- Illustrative rational instance with confidence target `τ = 3/4` and
abstention probability `1/4`. -/
noncomputable def methodOneAbstentionBound : AbstentionBound where
  tau := 3 / 4
  pAbstain := 1 / 4
  tau_nonneg := by norm_num
  tau_le_one := by norm_num
  bound := by norm_num

/-- The illustrative rational instance satisfies the generic acceptance bound. -/
theorem methodOne_acceptance_ge_target :
    methodOneAbstentionBound.tau ≤ 1 - methodOneAbstentionBound.pAbstain :=
  methodOneAbstentionBound.acceptance_ge_target

/-- Package the defining abstention inequality and its acceptance consequence. -/
def universal_abstention_bound_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalAbstentionBound.AbstentionBound.pAbstain_le"

end OperatorKO7.Meta.BoundaryOperator.UniversalAbstentionBound
