import OperatorKO7.Meta.BoundaryOperator.BoundaryWeightBornRatio
import OperatorKO7.QEC.Codes.KnillLaflammeEmpirical

/-!
# QEC specialization of the algebraic ratio

These theorems express the Method 4 empirical amplitude as `bornRatio` and specialize its dominant bound to that amplitude.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryOperator.BoundaryWeightBornRatio

open OperatorKO7.QEC.Codes

/-- Definitional specialization of the Method 4 amplitude to `bornRatio`. -/
theorem qec_methodFour_is_bornRatio (p : ℝ) (n : ℕ) :
    KnillLaflammeEmpirical.methodFourEmpiricalAmplitude p n
      = bornRatio ((1 - p) ^ n) ((p / 3) ^ n) 3 := rfl

/-- Specialize `bornRatio_dominant_bound` to the Method 4 amplitude. -/
theorem qec_methodFour_dominant_bound
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1) :
    KnillLaflammeEmpirical.methodFourEmpiricalAmplitude p n
      ≤ 2 * (p / 3) ^ n / (1 - p) ^ n :=
  amplitude_formula_dominant_bound p n hp hp1

#print axioms qec_methodFour_is_bornRatio
#print axioms qec_methodFour_dominant_bound

end OperatorKO7.Meta.BoundaryOperator.BoundaryWeightBornRatio
