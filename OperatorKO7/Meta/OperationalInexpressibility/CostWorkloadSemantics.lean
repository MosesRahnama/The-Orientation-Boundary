import OperatorKO7.Meta.OperationalInexpressibility.CostComparison

/-!
# Workload semantics for the carry-cost formulas

The pointwise direct burden at depth `h` is the sum of the incremental stage charges through
that depth. Summing the pointwise burden over every prefix charges earlier stages repeatedly.
This module records both workloads and their closed forms.

Property: arithmetic cost accounting for declared workloads.
Trust: kernel-only.
-/

set_option autoImplicit false

open scoped BigOperators

namespace OperatorKO7.Meta.OperationalInexpressibility.CostWorkloadSemantics

open OperatorKO7.Meta.ConfessionCrossingPoint
open OperatorKO7.Meta.OperationalInexpressibility.CostComparison

/-- Cost charged when depth `k` is processed once. -/
def directIncrementDoubled (payload depth : Nat) : Nat :=
  2 * (depth + 1) * payload

/-- Incremental execution through one horizon, charging each depth once. -/
def cachedTraceCarryDoubled (payload horizon : Nat) : Nat :=
  ∑ depth ∈ Finset.range (horizon + 1), directIncrementDoubled payload depth

/-- Recompute every prefix from depth zero through the selected horizon. -/
def repeatedPrefixCarryDoubled (payload horizon : Nat) : Nat :=
  ∑ k ∈ Finset.range (horizon + 1), cachedTraceCarryDoubled payload k

/-- The incremental sum is the existing single-prefix direct burden. -/
theorem cachedTraceCarryDoubled_eq_directCarryCostDoubled
    (payload horizon : Nat) :
    cachedTraceCarryDoubled payload horizon = directCarryCostDoubled horizon payload := by
  induction horizon with
  | zero => simp [cachedTraceCarryDoubled, directIncrementDoubled, directCarryCostDoubled]
  | succ horizon ih =>
      rw [cachedTraceCarryDoubled, Finset.sum_range_succ]
      change cachedTraceCarryDoubled payload horizon +
        directIncrementDoubled payload (horizon + 1) =
          directCarryCostDoubled (horizon + 1) payload
      rw [ih]
      simp [directIncrementDoubled, directCarryCostDoubled]
      ring

/-- Recomputing every prefix is exactly the previously defined all-depth cumulative burden. -/
theorem repeatedPrefixCarryDoubled_eq_cumulativeCarryDoubled
    (payload horizon : Nat) :
    repeatedPrefixCarryDoubled payload horizon =
      cumulativeCarryDoubled payload horizon := by
  unfold repeatedPrefixCarryDoubled cumulativeCarryDoubled
  apply Finset.sum_congr rfl
  intro k hk
  exact cachedTraceCarryDoubled_eq_directCarryCostDoubled payload k

/-- The single incremental execution has the quadratic closed form already used by the paper. -/
theorem cachedTraceCarryDoubled_closed (payload horizon : Nat) :
    cachedTraceCarryDoubled payload horizon =
      (horizon + 1) * (horizon + 2) * payload := by
  rw [cachedTraceCarryDoubled_eq_directCarryCostDoubled]
  rfl

/-- Recomputing all prefixes has the cubic division-free closed form. -/
theorem repeatedPrefixCarryDoubled_closed (payload horizon : Nat) :
    3 * repeatedPrefixCarryDoubled payload horizon =
      (horizon + 1) * (horizon + 2) * (horizon + 3) * payload := by
  rw [repeatedPrefixCarryDoubled_eq_cumulativeCarryDoubled]
  exact cumulativeCarryDoubled_closed payload horizon

/-- The repeated-prefix workload obeys the recurrence "old prefixes plus the new prefix". -/
theorem repeatedPrefixCarryDoubled_succ (payload horizon : Nat) :
    repeatedPrefixCarryDoubled payload (horizon + 1) =
      repeatedPrefixCarryDoubled payload horizon +
        cachedTraceCarryDoubled payload (horizon + 1) := by
  unfold repeatedPrefixCarryDoubled
  rw [Finset.sum_range_succ]

/-- With positive payload, recomputing more than the depth-zero prefix costs strictly more than
processing the final trace incrementally once. -/
theorem repeatedPrefixCarryDoubled_gt_cached_of_positive
    (payload horizon : Nat) (hpayload : 0 < payload) :
    cachedTraceCarryDoubled payload (horizon + 1) <
      repeatedPrefixCarryDoubled payload (horizon + 1) := by
  rw [repeatedPrefixCarryDoubled_succ]
  have hzero : 0 < cachedTraceCarryDoubled payload 0 := by
    simp [cachedTraceCarryDoubled, directIncrementDoubled, hpayload]
  have hle : cachedTraceCarryDoubled payload 0 ≤
      repeatedPrefixCarryDoubled payload horizon := by
    unfold repeatedPrefixCarryDoubled
    exact Finset.single_le_sum (fun k hk => Nat.zero_le _) (by simp)
  omega

/-- Zero payload gives zero cost under both workload conventions. -/
theorem zero_payload_workloads (horizon : Nat) :
    cachedTraceCarryDoubled 0 horizon = 0 ∧
      repeatedPrefixCarryDoubled 0 horizon = 0 := by
  simp [cachedTraceCarryDoubled, repeatedPrefixCarryDoubled, directIncrementDoubled]

/-- The difference between the two growth laws is caused by the workload definition: one charges
one execution through the horizon and the other charges every prefix execution. -/
theorem workload_growth_pair (payload horizon : Nat) :
    cachedTraceCarryDoubled payload horizon =
        (horizon + 1) * (horizon + 2) * payload ∧
      3 * repeatedPrefixCarryDoubled payload horizon =
        (horizon + 1) * (horizon + 2) * (horizon + 3) * payload :=
  ⟨cachedTraceCarryDoubled_closed payload horizon,
    repeatedPrefixCarryDoubled_closed payload horizon⟩

end OperatorKO7.Meta.OperationalInexpressibility.CostWorkloadSemantics
