import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore
import OperatorKO7.Meta.Methods.OrientationClosure.PolynomialRegion
import OperatorKO7.Meta.NonlinearUnconstrainedExactLaw
import Mathlib.Tactic

/-!
# Exact orientation criterion and quantitative coupling

The pointwise comparison is written in the integers so that wrapper cost and
counter gain are true signed differences for every natural-valued
interpretation. The coupling theorem uses only wrapper retention and orientation.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.CouplingTheorem

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Methods.OrientationClosure.PolynomialRegion

/-- Integer wrapper cost at one duplicating-rule instance. -/
def wrapperCostZ {S : StepDuplicatingSchema} (M : S.T → Nat)
    (b s n : S.T) : Int :=
  (M (S.wrap s (S.recur b s n)) : Int) - (M (S.recur b s n) : Int)

/-- Integer counter gain at one duplicating-rule instance. -/
def counterGainZ {S : StepDuplicatingSchema} (M : S.T → Nat)
    (b s n : S.T) : Int :=
  (M (S.recur b s (S.succ n)) : Int) - (M (S.recur b s n) : Int)

/-- Pointwise orientation is equivalent to wrapper cost being smaller than
counter gain. This holds for every schema and every natural-valued function. -/
theorem orients_instance_iff_wrapperCost_lt_counterGain
    {S : StepDuplicatingSchema} (M : S.T → Nat) (b s n : S.T) :
    M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n)) ↔
      wrapperCostZ M b s n < counterGainZ M b s n := by
  simp only [wrapperCostZ, counterGainZ]
  omega

/-- Uniform orientation is equivalent to the pointwise integer cost/gain law. -/
theorem orients_all_iff_wrapperCost_lt_counterGain
    {S : StepDuplicatingSchema} (M : S.T → Nat) :
    (∀ b s n : S.T,
      M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n))) ↔
    (∀ b s n : S.T, wrapperCostZ M b s n < counterGainZ M b s n) := by
  constructor <;> intro h b s n
  · exact (orients_instance_iff_wrapperCost_lt_counterGain M b s n).1 (h b s n)
  · exact (orients_instance_iff_wrapperCost_lt_counterGain M b s n).2 (h b s n)

/-- Retaining both wrapper arguments at cost `c_w`, together with orientation,
forces the counter gain to exceed the retained payload value plus that cost. -/
theorem retained_wrapper_forces_payload_coupled_gain
    {S : StepDuplicatingSchema} (M : S.T → Nat) (c_w : Nat)
    (hretain : ∀ x y : S.T, c_w + M x + M y ≤ M (S.wrap x y))
    (horient : ∀ b s n : S.T,
      M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n))) :
    ∀ b s n : S.T,
      (M s : Int) + (c_w : Int) < counterGainZ M b s n := by
  intro b s n
  have hr := hretain s (S.recur b s n)
  have ho := horient b s n
  simp only [counterGainZ]
  omega

/-- A uniform natural upper bound on the counter gain conflicts with unbounded
retained payload values. -/
theorem no_orientation_of_retention_bounded_gain_unbounded_payload
    {S : StepDuplicatingSchema} (M : S.T → Nat) (c_w g : Nat)
    (hretain : ∀ x y : S.T, c_w + M x + M y ≤ M (S.wrap x y))
    (hgain : ∀ b s n : S.T,
      M (S.recur b s (S.succ n)) ≤ M (S.recur b s n) + g)
    (hunbounded : ∀ K : Nat, ∃ s : S.T, K ≤ M s) :
    ¬ ∀ b s n : S.T,
      M (S.wrap s (S.recur b s n)) < M (S.recur b s (S.succ n)) := by
  intro horient
  obtain ⟨s, hs⟩ := hunbounded (g + 1)
  have hc := retained_wrapper_forces_payload_coupled_gain M c_w hretain horient
    S.base s S.base
  have hg := hgain S.base s S.base
  simp only [counterGainZ] at hc
  omega

/-- The existing unconstrained-law barrier is the bounded-gain corollary with
its own pumping argument, so no independent unboundedness hypothesis is needed. -/
theorem unconstrained_direct_law_barrier
    {S : StepDuplicatingSchema} (L : UnconstrainedDirectLaw S) :
    ¬ ∀ b s n : S.T,
      L.eval (S.wrap s (S.recur b s n)) < L.eval (S.recur b s (S.succ n)) :=
  no_unconstrainedDirect_orients_dup_step L

/-- For the paper's polynomial witness, the counter gain at base value zero is
exactly `s + 2`, independent of the current counter. -/
theorem main_polynomial_gain_exact (s n : Nat) :
    recursorEval 1 2 0 s (successorEval n) =
      recursorEval 1 2 0 s n + (s + 2) := by
  simp [recursorEval, successorEval]
  ring

/-- The same witness attains the coupling margin by one unit: wrapper retention
cost is one and its gain is `s + 2`. -/
theorem main_polynomial_coupling_tight (s n : Nat) :
    s + 1 < recursorEval 1 2 0 s (successorEval n) - recursorEval 1 2 0 s n ∧
      recursorEval 1 2 0 s (successorEval n) - recursorEval 1 2 0 s n = s + 2 := by
  rw [main_polynomial_gain_exact]
  omega

end OperatorKO7.Methods.OrientationClosure.CouplingTheorem
