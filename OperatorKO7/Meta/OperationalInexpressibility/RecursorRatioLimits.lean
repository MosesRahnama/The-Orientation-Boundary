import OperatorKO7.Meta.Recursor.RaryDuplicator
import OperatorKO7.Meta.SchemaNormMismatch
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The payload ratio and the odd-index inefficiency bound

The cumulative payload mass of the unary duplicator divided by the square of the residual work
tends to half the payload size, and the inefficiency coefficient at odd index `2N+1` is at least
`N`.

Relation: closed forms of the recursor's cost quantities.
Property: an exact ratio, its limit, and a lower bound.
Trust: kernel only.
Scope: natural counter heights and payload sizes.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.RecursorRatioLimits

open OperatorKO7.Meta.Recursor.RaryDuplicator
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open Filter Topology

theorem two_mul_conMassR_one (k β : ℕ) : 2 * conMassR k β 1 = β * ((k + 1) * (k + 2)) := by
  rw [L10_con_r_closed k β 1]
  ring

theorem conMassR_one_div_sq (k β : ℕ) (hk : 1 ≤ k) :
    (conMassR k β 1 : ℝ) / (k : ℝ) ^ 2 =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) * β / (2 * (k : ℝ) ^ 2) := by
  have h' : (2 : ℝ) * (conMassR k β 1 : ℝ) = (β : ℝ) * (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    exact_mod_cast two_mul_conMassR_one k β
  field_simp
  nlinarith [h']

theorem tendsto_conMassR_one_div_sq (β : ℕ) :
    Tendsto (fun k : ℕ => (conMassR k β 1 : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 ((β : ℝ) / 2)) := by
  have hlim : Tendsto (fun k : ℕ => ((β : ℝ) / 2) * (1 + 1 / (k : ℝ)) * (1 + 2 / (k : ℝ)))
      atTop (𝓝 ((β : ℝ) / 2)) := by
    have h1 : Tendsto (fun k : ℕ => (1 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 1
    have h2 : Tendsto (fun k : ℕ => (2 : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 2
    have hA : Tendsto (fun k : ℕ => 1 + 1 / (k : ℝ)) atTop (𝓝 (1 + 0)) :=
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).add h1
    have hB : Tendsto (fun k : ℕ => 1 + 2 / (k : ℝ)) atTop (𝓝 (1 + 0)) :=
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).add h2
    have h := hA.mul hB
    have hc := h.const_mul ((β : ℝ) / 2)
    simpa [mul_assoc] using hc
  refine Tendsto.congr' ?_ hlim
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [conMassR_one_div_sq k β hk]
  field_simp
  ring

theorem inefficiencyCoefficient_odd_index_ge (N w : ℕ) (hw : 1 ≤ w) :
    (N : ℝ) ≤ inefficiencyCoefficient (2 * N + 1) w := by
  have h := inefficiencyCoefficient_lower_linear (2 * N + 1) w (by omega) hw
  have hcast : (((2 * N + 1 : ℕ) + 1 : ℝ)) * (w : ℝ) / 2 = ((N : ℝ) + 1) * w := by
    push_cast
    ring
  rw [hcast] at h
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  nlinarith

end OperatorKO7.Meta.OperationalInexpressibility.RecursorRatioLimits
