import OperatorKO7.Meta.Decision.EchoStoppingMDP

set_option autoImplicit false

open OperatorKO7.Meta.Decision.EchoStopping

#check @EchoStoppingMDP
#check @bestContinuation
#check @continuationAdvantage
#check @netComputeAdvantage
#check @dynamicPolicy
#check @bestContinuation_le_iff
#check @successor_observation_eq
#check @zero_current_gain_positive_cost_dominated_continuations_force_stop
#check @nonpositive_current_gain_positive_cost_dominated_continuations_force_stop
#check @futureGainFixture
#check futureGainFixture_currentGain_zero
#check futureGainFixture_cost_pos
#check futureGainFixture_computes
#check @staticEchoModel
#check @staticEchoModel_continuationAdvantage_zero
#check @static_optimalMetaPolicy_eq_dynamicPolicy
#check @static_zero_deficit_specialization_stops

#print axioms EchoStoppingMDP
#print axioms bestContinuation
#print axioms continuationAdvantage
#print axioms netComputeAdvantage
#print axioms dynamicPolicy
#print axioms bestContinuation_le_iff
#print axioms successor_observation_eq
#print axioms zero_current_gain_positive_cost_dominated_continuations_force_stop
#print axioms nonpositive_current_gain_positive_cost_dominated_continuations_force_stop
#print axioms futureGainFixture
#print axioms futureGainFixture_currentGain_zero
#print axioms futureGainFixture_cost_pos
#print axioms futureGainFixture_computes
#print axioms staticEchoModel
#print axioms staticEchoModel_continuationAdvantage_zero
#print axioms static_optimalMetaPolicy_eq_dynamicPolicy
#print axioms static_zero_deficit_specialization_stops

#check @OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.mk
#print axioms OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.mk
#check @OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.observe
#print axioms OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.observe
#check @OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.successors
#print axioms OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.successors
#check @OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.successors_nonempty
#print axioms OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.successors_nonempty
#check @OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.echo_preserved
#print axioms OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.echo_preserved
#check @OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.stopValue
#print axioms OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.stopValue
#check @OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.currentGain
#print axioms OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.currentGain
#check @OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.futureValue
#print axioms OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.futureValue
#check @OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.computeCost
#print axioms OperatorKO7.Meta.Decision.EchoStopping.EchoStoppingMDP.computeCost
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonValue
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonValue
#check @OperatorKO7.Meta.Decision.EchoStopping.HorizonReturn
#print axioms OperatorKO7.Meta.Decision.EchoStopping.HorizonReturn
#check @OperatorKO7.Meta.Decision.EchoStopping.HorizonReturn.stop
#print axioms OperatorKO7.Meta.Decision.EchoStopping.HorizonReturn.stop
#check @OperatorKO7.Meta.Decision.EchoStopping.HorizonReturn.compute
#print axioms OperatorKO7.Meta.Decision.EchoStopping.HorizonReturn.compute
#check @OperatorKO7.Meta.Decision.EchoStopping.stopValue_le_horizonValue
#print axioms OperatorKO7.Meta.Decision.EchoStopping.stopValue_le_horizonValue
#check @OperatorKO7.Meta.Decision.EchoStopping.HorizonReturn.le_horizonValue
#print axioms OperatorKO7.Meta.Decision.EchoStopping.HorizonReturn.le_horizonValue
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonValue_attained
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonValue_attained
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonValue_isGreatest
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonValue_isGreatest
#check @OperatorKO7.Meta.Decision.EchoStopping.HorizonReturn.weaken
#print axioms OperatorKO7.Meta.Decision.EchoStopping.HorizonReturn.weaken
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonValue_le_succ
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonValue_le_succ
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonValue_independent_futureValue
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonValue_independent_futureValue
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_stop_iff
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_stop_iff
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_stop_iff_value_eq_stop
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_stop_iff_value_eq_stop
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_eq_dynamicPolicy
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_eq_dynamicPolicy
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_compute_realized
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_compute_realized
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonValue_eq_stop_on_invariant
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonValue_eq_stop_on_invariant
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonValue_eq_stop_of_echo_license
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonValue_eq_stop_of_echo_license
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_stops_of_echo_license
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_stops_of_echo_license
#check @OperatorKO7.Meta.Decision.EchoStopping.realizedFutureGainFixture
#print axioms OperatorKO7.Meta.Decision.EchoStopping.realizedFutureGainFixture
#check @OperatorKO7.Meta.Decision.EchoStopping.realizedFutureGainFixture_computes
#print axioms OperatorKO7.Meta.Decision.EchoStopping.realizedFutureGainFixture_computes
#check @OperatorKO7.Meta.Decision.EchoStopping.realizedFutureGainFixture_transition
#print axioms OperatorKO7.Meta.Decision.EchoStopping.realizedFutureGainFixture_transition

#check @OperatorKO7.Meta.Decision.EchoStopping.horizonValue_eq_stop_on_invariant_of_edge_bound
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonValue_eq_stop_on_invariant_of_edge_bound
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonValue_eq_stop_on_invariant_iff
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonValue_eq_stop_on_invariant_iff
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonValue_eq_stop_iff_edge_bound
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonValue_eq_stop_iff_edge_bound
#check @OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_stops_iff_edge_bound
#print axioms OperatorKO7.Meta.Decision.EchoStopping.horizonPolicy_stops_iff_edge_bound
#check @OperatorKO7.Meta.Decision.EchoStopping.compensatedGainFixture
#print axioms OperatorKO7.Meta.Decision.EchoStopping.compensatedGainFixture
#check @OperatorKO7.Meta.Decision.EchoStopping.compensatedGainFixture_stops
#print axioms OperatorKO7.Meta.Decision.EchoStopping.compensatedGainFixture_stops

#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected_mono
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected_mono
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected_congr
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected_congr
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected_congr_on_positive
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected_congr_on_positive
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.positive_outcome_exists
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.positive_outcome_exists
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.choices
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.choices
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.choices_nonempty
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.choices_nonempty
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.mem_choices
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.mem_choices
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.choiceValue
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.choiceValue
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.bellman
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.bellman
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.stop_le_bellman
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.stop_le_bellman
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected_le_bellman
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected_le_bellman
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.stop_le_value
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.stop_le_value
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Policy
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Policy
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Policy.value
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Policy.value
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Policy.le_value
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Policy.le_value
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_attained
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_attained
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_isGreatest
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_isGreatest
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.bellman_mono
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.bellman_mono
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_le_succ
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_le_succ
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.bellman_eq_stop_iff
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.bellman_eq_stop_iff
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_eq_stop_of_no_actions
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_eq_stop_of_no_actions
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_eq_stop_on_invariant
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_eq_stop_on_invariant
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_eq_stop_on_invariant_iff
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_eq_stop_on_invariant_iff
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_eq_stop_iff
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_eq_stop_iff
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected_le_of_pointwise
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.expected_le_of_pointwise
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_eq_stop_of_echo
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.value_eq_stop_of_echo
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_expected
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_expected
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_expected_formula
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_expected_formula
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_bellman_formula
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_bellman_formula
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_one_step
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_one_step
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_two_steps
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_two_steps
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_zero_mass_and_empty_actions
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_zero_mass_and_empty_actions
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_adaptive_policy
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.averagingFixture_adaptive_policy
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.mk
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.mk
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.actions
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.actions
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.support
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.support
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.probability
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.probability
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.probability_nonneg
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.probability_nonneg
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.probability_sum
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.probability_sum
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.stopValue
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.stopValue
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.reward
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Model.reward
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Policy.stop
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Policy.stop
#check @OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Policy.compute
#print axioms OperatorKO7.Meta.Decision.EchoStopping.Stochastic.Policy.compute

namespace OperatorKO7.Test.StochasticStoppingReach
open OperatorKO7.Meta.Decision.EchoStopping.Stochastic

example {S A : Type} [DecidableEq S] [DecidableEq A] (M : Model S A)
    (n : Nat) (s : S) : ∃ p : Policy M n s, p.value = value M n s :=
  value_attained M n s

example {S : Type} [DecidableEq S] (M : Model S Empty) (n : Nat) (s : S) :
    value M n s = M.stopValue s := by
  apply value_eq_stop_of_no_actions M
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a
  exact Empty.elim a

example : ∃ p : Policy averagingFixture 2 0, p.value = 3 / 2 :=
  averagingFixture_adaptive_policy

end OperatorKO7.Test.StochasticStoppingReach
