import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Method 4 accepted-shot model (manuscript label `thm:empirical-amplitude`)

The module defines `methodFourEmpiricalAmplitude p n = 2 (p / 3)^n / ((1 - p)^n + 3 (p / 3)^n)` and proves algebraic properties of that function. The formula is a restricted accepted-shot model; this module does not establish a measured logical-error rate or physical code performance. The separate Knill-Laflamme license obligations identified by `thm:kl-license` remain open.
-/

namespace OperatorKO7.QEC.Codes.KnillLaflammeEmpirical

/-- Closed-form Method 4 accepted-shot model value for noise parameter `p` and code size `n`: `2 (p / 3)^n / ((1 - p)^n + 3 (p / 3)^n)`. -/
noncomputable def methodFourEmpiricalAmplitude (p : ℝ) (n : ℕ) : ℝ :=
  2 * (p / 3) ^ n / ((1 - p) ^ n + 3 * (p / 3) ^ n)

/-- The denominator of the empirical-amplitude formula is strictly
positive for every physical noise rate `p` in the open interval
`(0, 1)`. -/
theorem methodFourEmpiricalAmplitude_denom_pos
    (p : ℝ) (hp_pos : 0 < p) (hp_lt_one : p < 1) (n : ℕ) :
    0 < (1 - p) ^ n + 3 * (p / 3) ^ n := by
  have h_one_sub_pos : 0 < 1 - p := sub_pos.mpr hp_lt_one
  have h_div_pos : 0 < p / 3 := by positivity
  have h_left : 0 < (1 - p) ^ n := pow_pos h_one_sub_pos n
  have h_right_inner : 0 < (p / 3) ^ n := pow_pos h_div_pos n
  have h_right : 0 < 3 * (p / 3) ^ n := by positivity
  linarith

/-- The empirical-amplitude formula is non-negative for every physical
noise rate `p` in the open interval `(0, 1)`. -/
theorem methodFourEmpiricalAmplitude_nonneg
    (p : ℝ) (hp_pos : 0 < p) (hp_lt_one : p < 1) (n : ℕ) :
    0 ≤ methodFourEmpiricalAmplitude p n := by
  unfold methodFourEmpiricalAmplitude
  have h_denom_pos := methodFourEmpiricalAmplitude_denom_pos p hp_pos hp_lt_one n
  have h_num_nonneg : 0 ≤ 2 * (p / 3) ^ n := by
    have hp_div_nonneg : 0 ≤ p / 3 := by positivity
    positivity
  exact div_nonneg h_num_nonneg h_denom_pos.le

/-- This theorem states the reflexive identity for the ground-weight factor `(1 - p)^n`. -/
theorem methodFourEmpiricalAmplitude_groundOverlap (p : ℝ) (n : ℕ) :
    (1 - p) ^ n = (1 - p) ^ n := rfl

/-- This theorem states the reflexive identity for the top-weight factor `(p / 3)^n`. -/
theorem methodFourEmpiricalAmplitude_topOverlap (p : ℝ) (n : ℕ) :
    (p / 3) ^ n = (p / 3) ^ n := rfl

/-- Definitional expansion with the denominator coefficient `3` explicit. -/
theorem methodFourEmpiricalAmplitude_unfolded
    (p : ℝ) (_hp_pos : 0 < p) (_hp_lt_one : p < 1) (n : ℕ) :
    methodFourEmpiricalAmplitude p n =
      (2 * (p / 3) ^ n) / ((1 - p) ^ n + 3 * (p / 3) ^ n) := rfl

/-- For `0 < p < 1/4`, the function is at most `2 (p / 3)^n / (1 - p)^n`, since the denominator is at least `(1 - p)^n`. -/
theorem methodFourEmpiricalAmplitude_dominant_ratio_bound
    (p : ℝ) (hp_pos : 0 < p) (hp_lt_quarter : p < 1 / 4) (n : ℕ) :
    methodFourEmpiricalAmplitude p n ≤ 2 * (p / 3) ^ n / (1 - p) ^ n := by
  unfold methodFourEmpiricalAmplitude
  have hp_lt_one : p < 1 := lt_trans hp_lt_quarter (by norm_num)
  have h_one_sub_pos : 0 < 1 - p := sub_pos.mpr hp_lt_one
  have h_div_pos : 0 < p / 3 := by positivity
  have h_pow_left : 0 < (1 - p) ^ n := pow_pos h_one_sub_pos n
  have h_pow_right : 0 < (p / 3) ^ n := pow_pos h_div_pos n
  have h_three_pow_right : 0 ≤ 3 * (p / 3) ^ n := by positivity
  have h_num_nonneg : 0 ≤ 2 * (p / 3) ^ n := by positivity
  have h_denom_ge : (1 - p) ^ n ≤ (1 - p) ^ n + 3 * (p / 3) ^ n := by linarith
  have h_denom_pos : 0 < (1 - p) ^ n + 3 * (p / 3) ^ n := by linarith
  exact div_le_div_of_nonneg_left h_num_nonneg h_pow_left h_denom_ge

-- Qualified name of the closed-form model definition.
def thm_empirical_amplitude_anchor : String :=
  "OperatorKO7.QEC.Codes.KnillLaflammeEmpirical.methodFourEmpiricalAmplitude"

end OperatorKO7.QEC.Codes.KnillLaflammeEmpirical
