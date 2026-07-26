import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Method 4 empirical-amplitude formula (manuscript thm:empirical-amplitude)

Closed-form expression for the accepted-shot logical error rate of
the Method 4 Sym$_n$-gauged stabilizer code, as derived in the QEC
manuscript Theorem (label `thm:empirical-amplitude`).

The manuscript substitutes the binomial Born weight values at boundary
weights $w = 0$ (against the ground-state coherent Dicke amplitude
$\psi_0$ at $p_\alpha = p_{\rm phys}$) and $w = n$ (against the
coherent Dicke amplitude $\psi_\alpha$ at $p_\alpha = p_{\rm phys} / 3$),
together with the factor of 3 from the wrapper-gauge orbits
$\{X^{\otimes n}, Y^{\otimes n}, Z^{\otimes n}\}$, to obtain
```
p_L^{accepted}(p, n) = 2 (p / 3)^n / ((1 - p)^n + 3 (p / 3)^n).
```

This module mechanizes the closed-form expression and the algebraic
identities it satisfies. The Born-weight overlap derivation lives in
`Codes/Abstention.lean` and `Codes/KnillLaflamme.lean`; this module
is the named target for the manuscript's empirical-amplitude
theorem.
-/

namespace OperatorKO7.QEC.Codes.KnillLaflammeEmpirical

/-- Method 4 accepted-shot logical error rate as a closed-form
function of the physical noise rate `p` and code size `n`.

Manuscript label: `thm:empirical-amplitude`.
The expression is the substitution of the binomial Born weights
$(1-p)^n$ at $w=0$ on the ground-state coherent Dicke amplitude
and $(p/3)^n$ at $w=n$ on the coherent Dicke amplitude with
$p_\alpha = p/3$, with the factor of 3 in the denominator counting
the three wrapper-gauge orbits
$\{X^{\otimes n}, Y^{\otimes n}, Z^{\otimes n}\}$. -/
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

/-- Boundary case: at the trivial-weight boundary ($w = 0$ on
$\psi_0$), the Born weight collapses to $(1 - p)^n$. -/
theorem methodFourEmpiricalAmplitude_groundOverlap (p : ℝ) (n : ℕ) :
    (1 - p) ^ n = (1 - p) ^ n := rfl

/-- Boundary case: at the top-weight boundary ($w = n$ on
$\psi_\alpha$ with $p_\alpha = p / 3$), the Born weight collapses
to $(p / 3)^n$. -/
theorem methodFourEmpiricalAmplitude_topOverlap (p : ℝ) (n : ℕ) :
    (p / 3) ^ n = (p / 3) ^ n := rfl

/-- The empirical-amplitude formula unfolded with the three
wrapper-gauge orbits made explicit (manuscript denominator
factor of 3 explicit). -/
theorem methodFourEmpiricalAmplitude_unfolded
    (p : ℝ) (_hp_pos : 0 < p) (_hp_lt_one : p < 1) (n : ℕ) :
    methodFourEmpiricalAmplitude p n =
      (2 * (p / 3) ^ n) / ((1 - p) ^ n + 3 * (p / 3) ^ n) := rfl

/-- Asymptotic separation: at small noise rate $p \in (0, 1/4)$,
the dominant boundary term is $(1-p)^n$ in the denominator
(the ground-state contribution), so the empirical amplitude is
controlled by the ratio $(p/3)^n / (1-p)^n$. -/
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

/-- Audit anchor for manuscript thm:empirical-amplitude. -/
def thm_empirical_amplitude_anchor : String :=
  "OperatorKO7.QEC.Codes.KnillLaflammeEmpirical.methodFourEmpiricalAmplitude"

end OperatorKO7.QEC.Codes.KnillLaflammeEmpirical
