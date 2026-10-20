import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Continuation value and finite-horizon stopping

Proof graph: Audit/ledgers/operational-inexpressibility/OBSERVATION-EXTENSIONS-PROOF-GRAPH.md,
node D1. The process state includes the current information state. One specified action advances it.
Payoff is a decision value, not Shannon entropy. The theorem optimizes over all stopping times on
this deterministic path; it does not claim to optimize an unspecified controlled stochastic process.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.DynamicStopping

/-- Return from waiting exactly k further steps and then taking the available payoff. -/
def returnAt {X : Type*} (step : X → X) (pay cost : X → ℝ) : ℕ → X → ℝ
  | 0, x => pay x
  | k + 1, x => returnAt step pay cost k (step x) - cost x

/-- Bellman recursion for stopping now or taking one further step. -/
def value {X : Type*} (step : X → X) (pay cost : X → ℝ) : ℕ → X → ℝ
  | 0, x => pay x
  | n + 1, x => max (pay x) (value step pay cost n (step x) - cost x)

theorem stop_le_value {X : Type*} (step : X → X) (pay cost : X → ℝ) (n : ℕ) (x : X) :
    pay x ≤ value step pay cost n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

/-- The Bellman value bounds every permitted stopping time. -/
theorem return_le_value {X : Type*} (step : X → X) (pay cost : X → ℝ)
    (n k : ℕ) (h : k ≤ n) (x : X) : returnAt step pay cost k x ≤ value step pay cost n x := by
  induction n generalizing k x with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    exact le_rfl
  | succ n ih =>
    cases k with
    | zero => exact stop_le_value step pay cost (n + 1) x
    | succ k =>
      exact (sub_le_sub_right (ih k (by omega) (step x)) (cost x)).trans (le_max_right _ _)

/-- A permitted stopping time attains the Bellman value. -/
theorem value_attained {X : Type*} (step : X → X) (pay cost : X → ℝ) (n : ℕ) (x : X) :
    ∃ k ≤ n, returnAt step pay cost k x = value step pay cost n x := by
  induction n generalizing x with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    by_cases h : value step pay cost n (step x) - cost x ≤ pay x
    · exact ⟨0, Nat.zero_le _, (max_eq_left h).symm⟩
    · obtain ⟨k, hk, he⟩ := ih (step x)
      refine ⟨k + 1, by omega, ?_⟩
      change returnAt step pay cost k (step x) - cost x =
        max (pay x) (value step pay cost n (step x) - cost x)
      rw [he, max_eq_right (le_of_lt (lt_of_not_ge h))]

/-- A longer horizon cannot lower the optimum, even when costs are state dependent. -/
theorem horizon_monotone {X : Type*} (step : X → X) (pay cost : X → ℝ) (n : ℕ) (x : X) :
    value step pay cost n x ≤ value step pay cost (n + 1) x := by
  induction n generalizing x with
  | zero => exact le_max_left _ _
  | succ n ih =>
    exact max_le_max le_rfl (sub_le_sub_right (ih (step x)) (cost x))

/-- A global continuation bound is sufficient for immediate stopping at every horizon. -/
theorem stop_optimal_of_step_bound {X : Type*} (step : X → X) (pay cost : X → ℝ)
    (h : ∀ x, pay (step x) - cost x ≤ pay x) (n : ℕ) (x : X) :
    value step pay cost n x = pay x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change max (pay x) (value step pay cost n (step x) - cost x) = pay x
    rw [ih, max_eq_left (h x)]

/-- If all later information states have the same decision value, nonnegative costs justify stop. -/
theorem stop_optimal_of_preserved_payoff {X : Type*}
    (step : X → X) (pay cost : X → ℝ)
    (hp : ∀ x, pay (step x) = pay x) (hc : ∀ x, 0 ≤ cost x) (n : ℕ) (x : X) :
    value step pay cost n x = pay x := by
  apply stop_optimal_of_step_bound step pay cost
  intro y
  rw [hp y]
  linarith [hc y]

/-- Continuing is strictly better precisely when its full remaining value exceeds the current payoff. -/
theorem continue_improves_iff {X : Type*} (step : X → X) (pay cost : X → ℝ)
    (n : ℕ) (x : X) :
    pay x < value step pay cost (n + 1) x ↔
      pay x < value step pay cost n (step x) - cost x := by
  change pay x < max (pay x) _ ↔ _
  simp only [lt_max_iff, lt_self_iff_false, false_or]

/-- A three-stage experiment, with its hidden bit revealed only at stage two. -/
def delayedStep (stage : Fin 3) : Fin 3 := if stage.val = 0 then 1 else 2

def delayedRead (stage : Fin 3) (hidden : Bool) : Option Bool :=
  if stage.val = 2 then some hidden else none

/-- Best success probability for guessing a fair hidden bit from the stage's record. -/
noncomputable def delayedPay (stage : Fin 3) : ℝ := if stage.val = 2 then 1 else 1 / 2

noncomputable def delayedCost (_ : Fin 3) : ℝ := 1 / 8

/-- This derives the claimed decision payoff from all deterministic Boolean decision rules. -/
theorem delayedPay_is_optimal (stage : Fin 3) :
    (∀ d : Option Bool → Bool,
      ((if d (delayedRead stage false) = false then (1 : ℝ) else 0) +
       (if d (delayedRead stage true) = true then 1 else 0)) / 2 ≤ delayedPay stage) ∧
    (∃ d : Option Bool → Bool,
      ((if d (delayedRead stage false) = false then (1 : ℝ) else 0) +
       (if d (delayedRead stage true) = true then 1 else 0)) / 2 = delayedPay stage) := by
  constructor
  · intro d
    fin_cases stage
    · cases h : d none <;> norm_num [delayedRead, delayedPay, h]
    · cases h : d none <;> norm_num [delayedRead, delayedPay, h]
    · cases h0 : d (some false) <;> cases h1 : d (some true) <;>
        norm_num [delayedRead, delayedPay, h0, h1]
  · refine ⟨fun o => o.getD false, ?_⟩
    fin_cases stage <;> norm_num [delayedRead, delayedPay]

/-- The first step supplies no new record and no immediate decision gain, yet the two-step
continuation has value 3/4 instead of 1/2 after paying both positive costs. -/
theorem zero_current_gain_does_not_force_stop :
    (∀ b, delayedRead (delayedStep 0) b = delayedRead 0 b) ∧
    delayedPay (delayedStep 0) = delayedPay 0 ∧
    value delayedStep delayedPay delayedCost 1 0 = (1 : ℝ) / 2 ∧
    value delayedStep delayedPay delayedCost 2 0 = (3 : ℝ) / 4 ∧
    delayedPay 0 < value delayedStep delayedPay delayedCost 2 0 := by
  norm_num [delayedRead, delayedStep, delayedPay, delayedCost, value]

end OperatorKO7.Meta.BoundaryObserver.DynamicStopping
