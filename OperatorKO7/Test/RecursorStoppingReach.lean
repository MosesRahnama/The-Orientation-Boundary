import OperatorKO7.Meta.Decision.RecursorStopping

/-! Paired reach and axiom gate for the execution-derived recursor stopping law. -/

set_option autoImplicit false

namespace OperatorKO7.Test.RecursorStoppingReach

open OperatorKO7.Meta.Decision.EchoStopping.Stochastic
open OperatorKO7.Meta.Decision.RecursorStopping

#check @raryCumulativeCost
#check @raryMarginalCopies
#check @raryMarginalCost
#check @binaryCumulativeCost
#check @raryCumulativeCost_eq_live_sum
#check @raryMarginalCopies_eq_live_next
#check @raryMarginalCost_eq_live_next
#check @raryCumulativeCost_succ
#check @raryCumulativeCost_succ_eq_actual_live_extension
#check @binaryCumulativeCost_eq_tri
#check @binaryCumulativeCost_doubled
#check @binaryCumulativeCost_eq_live_sum
#check @binaryCumulativeCost_succ
#check @runtime_descent_separate_from_copy_cost
#check @decisionDepth_has_actual_execution
#check @raryMarginalCutoff
#check @binaryMarginalCutoff
#check @raryMarginalCutoff_spec
#check @raryMarginalCutoff_least
#check @raryMarginalCutoff_le_iff
#check @raryMarginalCost_lt_of_lt_cutoff
#check @raryMarginalCutoff_one
#check @raryStrictMarginalCutoff
#check @raryStrictMarginalCutoff_le_iff
#check @rary_cutoff_le_strictCutoff_le_succ
#check @rary_cutoff_eq_strictCutoff_iff
#check @rary_strictCutoff_eq_succ_iff_tie
#check @recursorStoppingModel
#check @recursorStoppingModel_actions
#check @recursorStoppingModel_support
#check @DepthExtension
#check @recursorStoppingModel_probability
#check @recursorStoppingModel_support_iff_depthExtension
#check @recursorStoppingModel_positive_probability_iff_depthExtension
#check @recursorStoppingModel_stopValue
#check @recursorStoppingModel_expected
#check @recursorNetGain
#check @recursorPrefixReturn
#check @recursorFiniteHorizonMaximum
#check @recursorPrefixReturn_zero
#check @recursorPrefixReturn_succ
#check @recursorPrefixReturn_eq_sum
#check @recursorStoppingModel_bellman_eq_max
#check @recursorStopping_value_eq_finiteHorizonMaximum
#check @recursorPrefixReturn_le_finiteHorizonMaximum
#check @recursorFiniteHorizonMaximum_attained
#check @recursorFiniteHorizonMaximum_isGreatest
#check @RecursorPolicyStopsAfter
#check @recursorPrefixReturn_realized
#check @recursorStopAfter
#check @recursorStopAfter_value
#check @recursorStopAfter_stopsAfter
#check @recursorOptimalStoppingTime_and_policy_exists
#check @recursorStopping_value_eq_stop_iff_all_prefixReturns_le
#check @recursorStopping_all_horizons_eq_stop_iff_all_prefixReturns_le
#check @positive_transition_cost_eq_actual_live_stage
#check @oneStep_stop_iff
#check @oneStep_continues_iff
#check @oneStep_compute_ties_stop_iff
#check @AfterCutoff
#check @afterCutoff_iff_marginalCost
#check @strictCutoff_le_iff_marginalCost_gt
#check @afterCutoff_closed
#check @expected_stopValue_le_afterCutoff
#check @value_eq_stop_afterCutoff
#check @adaptivePolicy_le_stop_afterCutoff
#check @adaptivePolicy_attains_stop_afterCutoff
#check @constantBenefit_value_one_pos_belowCutoff
#check @constantBenefit_all_horizons_stop_iff
#check @zero_unitCost_control
#check @zero_payload_control
#check @positiveBenefit_zeroPrice_continues
#check @zero_unitCost_positiveBenefit_continues
#check @zero_payload_positiveBenefit_continues
#check @zero_arity_marginalCost
#check @zero_arity_constantBenefit_all_horizons_stop_iff
#check @zero_current_benefit_future_reward_continues
#check @zero_current_benefit_future_reward_control_values
#check @binary_constantBenefit_all_horizons_stop_iff
#check @recursor_stopping_complete
#check @recursor_stopping_policy_crown

/-! Concrete exact-cost, cutoff, tie, and control evaluations. -/

example :
    binaryCumulativeCost 0 2 = 2 ∧
      binaryCumulativeCost 1 2 = 6 ∧
      binaryCumulativeCost 2 2 = 12 := by
  decide

example :
    raryMarginalCost 0 1 2 1 = 4 ∧
      raryMarginalCost 1 1 2 1 = 6 := by
  decide

example :
    binaryMarginalCutoff 7 2 = 2 ∧
      raryMarginalCutoff 10 1 2 = 4 := by
  decide

example :
    raryMarginalCutoff 6 2 1 = 1 ∧
      raryStrictMarginalCutoff 6 2 1 = 2 := by
  decide

example :
    DepthExtension 3 4 ∧ ¬ DepthExtension 3 3 := by
  norm_num [DepthExtension]

example :
    value (recursorStoppingModel (fun _ => (6 : ℝ)) (fun _ => 0) 1 2 1) 1 1 = 0 := by
  apply (oneStep_stop_iff (fun _ => (6 : ℝ)) (fun _ => 0) 1 2 1 1).2
  norm_num [raryMarginalCost, raryMarginalCopies]

example :
    0 < value (recursorStoppingModel (fun _ => (7 : ℝ)) (fun _ => 0) 1 2 1) 1 1 := by
  simpa using constantBenefit_value_one_pos_belowCutoff 7 1 2 1 1
    (by decide) (by decide) (by decide) (by decide)

example :
    ∀ n,
      value (recursorStoppingModel (fun _ => (2 : ℝ)) (fun _ => 0) 1 2 0) n 5 = 0 :=
  (zero_arity_constantBenefit_all_horizons_stop_iff 2 1 2 5).2 (by decide)

example :
    ¬ ∀ n,
      value (recursorStoppingModel (fun _ => (3 : ℝ)) (fun _ => 0) 1 2 0) n 5 = 0 := by
  exact fun h => (by
    have := (zero_arity_constantBenefit_all_horizons_stop_iff 3 1 2 5).1 h
    omega)

example :
    ∀ n,
      value (recursorStoppingModel (fun _ => (7 : ℝ)) (fun _ => 0) 1 2 1) n 2 = 0 := by
  apply (binary_constantBenefit_all_horizons_stop_iff 7 1 2 2
    (by decide) (by decide)).2
  decide

example :
    (recursorStoppingModel (fun _ => (0 : ℝ)) (fun k => 3 * (k : ℝ)) 1 1 1).stopValue 0 <
      value (recursorStoppingModel (fun _ => (0 : ℝ))
        (fun k => 3 * (k : ℝ)) 1 1 1) 1 0 :=
  zero_current_benefit_future_reward_continues

example :
    recursorPrefixReturn (fun _ => (7 : ℝ)) (fun _ => 0) 1 2 1 0 2 = 4 := by
  norm_num [recursorPrefixReturn, recursorNetGain, raryMarginalCost,
    raryMarginalCopies]

example :
    recursorFiniteHorizonMaximum (fun _ => (7 : ℝ)) (fun _ => 0) 1 2 1 3 0 = 4 := by
  norm_num [recursorFiniteHorizonMaximum, recursorNetGain, raryMarginalCost,
    raryMarginalCopies]

example :
    value (recursorStoppingModel (fun _ => (7 : ℝ)) (fun _ => 0) 1 2 1) 3 0 = 4 := by
  rw [recursorStopping_value_eq_finiteHorizonMaximum]
  norm_num [recursorFiniteHorizonMaximum, recursorNetGain, raryMarginalCost,
    raryMarginalCopies]

#print axioms raryCumulativeCost
#print axioms raryMarginalCopies
#print axioms raryMarginalCost
#print axioms binaryCumulativeCost
#print axioms raryCumulativeCost_eq_live_sum
#print axioms raryMarginalCopies_eq_live_next
#print axioms raryMarginalCost_eq_live_next
#print axioms raryCumulativeCost_succ
#print axioms raryCumulativeCost_succ_eq_actual_live_extension
#print axioms binaryCumulativeCost_eq_tri
#print axioms binaryCumulativeCost_doubled
#print axioms binaryCumulativeCost_eq_live_sum
#print axioms binaryCumulativeCost_succ
#print axioms runtime_descent_separate_from_copy_cost
#print axioms decisionDepth_has_actual_execution
#print axioms raryMarginalCutoff
#print axioms binaryMarginalCutoff
#print axioms raryMarginalCutoff_spec
#print axioms raryMarginalCutoff_least
#print axioms raryMarginalCutoff_le_iff
#print axioms raryMarginalCost_lt_of_lt_cutoff
#print axioms raryMarginalCutoff_one
#print axioms raryStrictMarginalCutoff
#print axioms raryStrictMarginalCutoff_le_iff
#print axioms rary_cutoff_le_strictCutoff_le_succ
#print axioms rary_cutoff_eq_strictCutoff_iff
#print axioms rary_strictCutoff_eq_succ_iff_tie
#print axioms recursorStoppingModel
#print axioms recursorStoppingModel_actions
#print axioms recursorStoppingModel_support
#print axioms DepthExtension
#print axioms recursorStoppingModel_probability
#print axioms recursorStoppingModel_support_iff_depthExtension
#print axioms recursorStoppingModel_positive_probability_iff_depthExtension
#print axioms recursorStoppingModel_stopValue
#print axioms recursorStoppingModel_expected
#print axioms recursorNetGain
#print axioms recursorPrefixReturn
#print axioms recursorFiniteHorizonMaximum
#print axioms recursorPrefixReturn_zero
#print axioms recursorPrefixReturn_succ
#print axioms recursorPrefixReturn_eq_sum
#print axioms recursorStoppingModel_bellman_eq_max
#print axioms recursorStopping_value_eq_finiteHorizonMaximum
#print axioms recursorPrefixReturn_le_finiteHorizonMaximum
#print axioms recursorFiniteHorizonMaximum_attained
#print axioms recursorFiniteHorizonMaximum_isGreatest
#print axioms RecursorPolicyStopsAfter
#print axioms recursorPrefixReturn_realized
#print axioms recursorStopAfter
#print axioms recursorStopAfter_value
#print axioms recursorStopAfter_stopsAfter
#print axioms recursorOptimalStoppingTime_and_policy_exists
#print axioms recursorStopping_value_eq_stop_iff_all_prefixReturns_le
#print axioms recursorStopping_all_horizons_eq_stop_iff_all_prefixReturns_le
#print axioms positive_transition_cost_eq_actual_live_stage
#print axioms oneStep_stop_iff
#print axioms oneStep_continues_iff
#print axioms oneStep_compute_ties_stop_iff
#print axioms AfterCutoff
#print axioms afterCutoff_iff_marginalCost
#print axioms strictCutoff_le_iff_marginalCost_gt
#print axioms afterCutoff_closed
#print axioms expected_stopValue_le_afterCutoff
#print axioms value_eq_stop_afterCutoff
#print axioms adaptivePolicy_le_stop_afterCutoff
#print axioms adaptivePolicy_attains_stop_afterCutoff
#print axioms constantBenefit_value_one_pos_belowCutoff
#print axioms constantBenefit_all_horizons_stop_iff
#print axioms zero_unitCost_control
#print axioms zero_payload_control
#print axioms positiveBenefit_zeroPrice_continues
#print axioms zero_unitCost_positiveBenefit_continues
#print axioms zero_payload_positiveBenefit_continues
#print axioms zero_arity_marginalCost
#print axioms zero_arity_constantBenefit_all_horizons_stop_iff
#print axioms zero_current_benefit_future_reward_continues
#print axioms zero_current_benefit_future_reward_control_values
#print axioms binary_constantBenefit_all_horizons_stop_iff
#print axioms recursor_stopping_complete
#print axioms recursor_stopping_policy_crown

end OperatorKO7.Test.RecursorStoppingReach
