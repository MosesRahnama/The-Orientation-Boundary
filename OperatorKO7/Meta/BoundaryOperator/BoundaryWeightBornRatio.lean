import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Algebraic ratio and its three-term specialization

For real values `g`, `e`, and `k`, this module defines
`bornRatio g e k = 2e / (g + k * e)` and proves elementary denominator, nonnegativity, and upper-bound
facts under explicit sign assumptions. The theorem types use real-valued algebra rather than a
boundary-operator interface.

The three-term amplitude formula `2 (p/3)^n / ((1-p)^n + 3 (p/3)^n)` is obtained by substituting
`(1-p)^n`, `(p/3)^n`, and `3` into that ratio; the equality is definitional and is followed by its
bound. This module states both in plain real algebra and depends on no further development.
-/

namespace OperatorKO7.Meta.BoundaryOperator.BoundaryWeightBornRatio


/-- The algebraic ratio `2e / (g + k * e)` for real parameters `g`, `e`, and `k`. -/
noncomputable def bornRatio (g e k : ℝ) : ℝ := 2 * e / (g + k * e)

/-- The denominator is strictly positive whenever the ground mass is positive and
the excited mass and multiplicity are nonnegative. -/
theorem bornRatio_denom_pos (g e k : ℝ) (hg : 0 < g) (he : 0 ≤ e) (hk : 0 ≤ k) :
    0 < g + k * e := by
  have : 0 ≤ k * e := mul_nonneg hk he
  linarith

/-- The ratio is nonnegative under the stated sign assumptions. -/
theorem bornRatio_nonneg (g e k : ℝ) (hg : 0 < g) (he : 0 ≤ e) (hk : 0 ≤ k) :
    0 ≤ bornRatio g e k := by
  unfold bornRatio
  have hd := bornRatio_denom_pos g e k hg he hk
  have hn : 0 ≤ 2 * e := by linarith
  exact div_nonneg hn hd.le

/-- Algebraic upper bound obtained by dropping the nonnegative `k * e` denominator contribution. -/
theorem bornRatio_dominant_bound (g e k : ℝ) (hg : 0 < g) (he : 0 ≤ e) (hk : 0 ≤ k) :
    bornRatio g e k ≤ 2 * e / g := by
  unfold bornRatio
  have hke : 0 ≤ k * e := mul_nonneg hk he
  have hn : 0 ≤ 2 * e := by linarith
  have hge : g ≤ g + k * e := by linarith
  exact div_le_div_of_nonneg_left hn hg hge

/-- The three-term amplitude formula `2 e / (g + 3 e)` at `g = (1-p)^n`, `e = (p/3)^n` is
definitionally the algebraic ratio. Stated here without reference to any error-correction
development; a downstream module specializes it to that setting. -/
theorem amplitude_formula_is_bornRatio (p : ℝ) (n : ℕ) :
    2 * (p / 3) ^ n / ((1 - p) ^ n + 3 * (p / 3) ^ n)
      = bornRatio ((1 - p) ^ n) ((p / 3) ^ n) 3 := rfl

/-- Specialize `bornRatio_dominant_bound` to the three-term amplitude formula. -/
theorem amplitude_formula_dominant_bound
    (p : ℝ) (n : ℕ) (hp : 0 < p) (hp1 : p < 1) :
    2 * (p / 3) ^ n / ((1 - p) ^ n + 3 * (p / 3) ^ n)
      ≤ 2 * (p / 3) ^ n / (1 - p) ^ n := by
  rw [amplitude_formula_is_bornRatio]
  refine bornRatio_dominant_bound _ _ _ ?_ ?_ ?_
  · exact pow_pos (by linarith) n
  · exact pow_nonneg (by positivity) n
  · norm_num

/-- String containing the declaration name of `bornRatio`. -/
def boundary_weight_born_ratio_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.BoundaryWeightBornRatio.bornRatio"

end OperatorKO7.Meta.BoundaryOperator.BoundaryWeightBornRatio
