import OperatorKO7.Meta.ConfessionCrossingPoint

/-!
# Reach gate for the confession crossing point

Paired `#check` and `#print axioms` for every public declaration. Expected
footprint is a subset of `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.ConfessionCrossingPointReach

open OperatorKO7.Meta.ConfessionCrossingPoint

#check @directCarryCostDoubled
#check @confessExitCostDoubled
#check @directCarryCostDoubled_eq
#check @confessExitCostDoubled_eq
#check @CarryExceedsConfess
#check @decidableCarryExceedsConfess
#check @carry_exceeds_at_licenseCost
#check @crossing_exists
#check @crossingPoint
#check @crossingPoint_spec
#check @crossingPoint_least
#check @crossingPoint_le_licenseCost
#check @carry_exceeds_succ
#check @carry_exceeds_of_crossingPoint_le
#check @carry_exceeds_iff_crossingPoint_le
#check @no_crossing_of_zero_payload
#check @BudgetDerived
#check @derived_budget_forces_confession
#check @crossingPoint_is_least_derived_budget
#check @confession_crossing_law

#print axioms directCarryCostDoubled_eq
#print axioms confessExitCostDoubled_eq
#print axioms carry_exceeds_at_licenseCost
#print axioms crossing_exists
#print axioms crossingPoint_spec
#print axioms crossingPoint_least
#print axioms crossingPoint_le_licenseCost
#print axioms carry_exceeds_succ
#print axioms carry_exceeds_of_crossingPoint_le
#print axioms carry_exceeds_iff_crossingPoint_le
#print axioms no_crossing_of_zero_payload
#print axioms derived_budget_forces_confession
#print axioms crossingPoint_is_least_derived_budget
#print axioms confession_crossing_law

/-! ## Marginal law and stopping regimes -/

#check @residual_marginal
#check @carry_marginal_doubled
#check @marginal_cost_exceeds_any_bound
#check @ContinueAt
#check @bounded_value_stops
#check @zero_value_never_continues
#check @stopping_regimes_separate

#print axioms residual_marginal
#print axioms carry_marginal_doubled
#print axioms marginal_cost_exceeds_any_bound
#print axioms bounded_value_stops
#print axioms zero_value_never_continues
#print axioms stopping_regimes_separate

/-! ## Computed witnesses (non-vacuity by evaluation) -/

example : crossingPoint 1 12 (by norm_num) ≤ 12 :=
  crossingPoint_le_licenseCost 1 12 (by norm_num)

example : CarryExceedsConfess 1 12 12 :=
  carry_exceeds_at_licenseCost 1 12 (by norm_num)

end OperatorKO7.Test.ConfessionCrossingPointReach
