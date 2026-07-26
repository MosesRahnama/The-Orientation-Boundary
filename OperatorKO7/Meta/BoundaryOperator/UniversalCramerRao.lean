import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Conditional Cramer-Rao Record

## Formal Scope

The formal theorem projects the cramer_rao field supplied inside ParameterEstimation. BoundaryOperator instances and QEC adapters are not represented by this module's types.
-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalCramerRao

/-- A parameter-estimation structure: a positive Fisher information and an
unbiased-estimator variance meeting the Cramér-Rao floor. -/
structure ParameterEstimation where
  fisher : ℝ
  variance : ℝ
  fisher_pos : 0 < fisher
  cramer_rao : variance ≥ 1 / fisher

namespace ParameterEstimation

/-- The defining Cramér-Rao lower bound. -/
theorem cr_bound (P : ParameterEstimation) : P.variance ≥ 1 / P.fisher := P.cramer_rao

/-- The estimator variance is strictly positive. -/
theorem variance_pos (P : ParameterEstimation) : 0 < P.variance :=
  lt_of_lt_of_le (div_pos one_pos P.fisher_pos) P.cramer_rao

/-- Efficiency form: the variance-Fisher product is at least one. -/
theorem efficiency (P : ParameterEstimation) : 1 ≤ P.variance * P.fisher := by
  have h : 1 / P.fisher ≤ P.variance := P.cramer_rao
  have key : (1 / P.fisher) * P.fisher ≤ P.variance * P.fisher :=
    mul_le_mul_of_nonneg_right h (le_of_lt P.fisher_pos)
  rwa [one_div_mul_cancel (ne_of_gt P.fisher_pos)] at key

/-- More Fisher information permits a smaller variance floor. -/
theorem floor_antitone (P Q : ParameterEstimation) (h : P.fisher ≤ Q.fisher) :
    1 / Q.fisher ≤ 1 / P.fisher :=
  one_div_le_one_div_of_le P.fisher_pos h

end ParameterEstimation

/-- A representative parameter-estimation instance saturating the floor
(`I = V = 1`, so `V = 1/I`). -/
noncomputable def saturatingEstimator : ParameterEstimation where
  fisher := 1
  variance := 1
  fisher_pos := by norm_num
  cramer_rao := by norm_num

/-- Non-vacuity: the saturating instance has positive variance. -/
theorem saturatingEstimator_variance_pos : 0 < saturatingEstimator.variance :=
  saturatingEstimator.variance_pos

/-- String anchor for the record-field projection theorem. -/
def universal_cramer_rao_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalCramerRao.ParameterEstimation.cr_bound"

end OperatorKO7.Meta.BoundaryOperator.UniversalCramerRao
