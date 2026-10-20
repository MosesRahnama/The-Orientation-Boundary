import OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds

/-!
Reachability and axiom check for `Meta/BoundaryObserver/SelfEvaluationBounds.lean`. Every public
declaration of the module has a `#check @` and a `#print axioms`.
-/

open OperatorKO7.Meta.BoundaryObserver.SelfEvaluationBounds

#check @Solvable
#check @collision_blocks_every_family
#check @solvable_univ_iff_determines
#check @boundary_pair_subset
#check @boundary_pair_eq_empty
#check @xorEval
#check @xorEval_self
#check @xorEval_diagonal_not_represented
#check @code_observer_boundary_empty
#check @representation_failure_without_merged_pair
#check @fairReadout
#check @fairReadout_preserves_negation
#check @complement_fixed_iff_half
#check @stochastic_readout_forces_half
#check @stochastic_readout_iff
#check @no_deterministic_readout_fair_law
#check @approx_self_evaluation_bound
#check @approx_bound_attained
#check @collision_error_sum
#check @collision_error_half
#check @shiftMap
#check @shiftMap_displacement
#check @shiftMap_ne_self
#check @shiftMap_no_uniform_displacement
#check @thresholdEval
#check @constTrue
#check @thresholdEval_self
#check @threshold_fails_at_self
#check @threshold_passes_finite
#check @threshold_not_represented
#check @threshold_error_iff
#check @threshold_error_enumerated
#check @geometricLaw
#check @geometricLaw_hasSum
#check @thresholdErrorMass
#check @thresholdErrorMass_hasSum
#check @thresholdErrorMass_eq
#check @thresholdErrorMass_tendsto_zero
#check @pairedEval
#check @pairedTarget
#check @pairedEval_self
#check @pairedTarget_eq_not_self
#check @pairedEval_negation_closed
#check @pairedEval_error_iff
#check @paired_row_error_set
#check @paired_every_code_errs
#check @paired_not_represented
#check @paired_self_evaluation_not_represented
#check @pairedEvalFin
#check @pairedTargetFin
#check @pairedFin_card
#check @pairedFin_error_iff
#check @pairedFin_selected_errors_once
#check @pairedFin_every_code_errs

#print axioms Solvable
#print axioms collision_blocks_every_family
#print axioms solvable_univ_iff_determines
#print axioms boundary_pair_subset
#print axioms boundary_pair_eq_empty
#print axioms xorEval
#print axioms xorEval_self
#print axioms xorEval_diagonal_not_represented
#print axioms code_observer_boundary_empty
#print axioms representation_failure_without_merged_pair
#print axioms fairReadout
#print axioms fairReadout_preserves_negation
#print axioms complement_fixed_iff_half
#print axioms stochastic_readout_forces_half
#print axioms stochastic_readout_iff
#print axioms no_deterministic_readout_fair_law
#print axioms approx_self_evaluation_bound
#print axioms approx_bound_attained
#print axioms collision_error_sum
#print axioms collision_error_half
#print axioms shiftMap
#print axioms shiftMap_displacement
#print axioms shiftMap_ne_self
#print axioms shiftMap_no_uniform_displacement
#print axioms thresholdEval
#print axioms constTrue
#print axioms thresholdEval_self
#print axioms threshold_fails_at_self
#print axioms threshold_passes_finite
#print axioms threshold_not_represented
#print axioms threshold_error_iff
#print axioms threshold_error_enumerated
#print axioms geometricLaw
#print axioms geometricLaw_hasSum
#print axioms thresholdErrorMass
#print axioms thresholdErrorMass_hasSum
#print axioms thresholdErrorMass_eq
#print axioms thresholdErrorMass_tendsto_zero
#print axioms pairedEval
#print axioms pairedTarget
#print axioms pairedEval_self
#print axioms pairedTarget_eq_not_self
#print axioms pairedEval_negation_closed
#print axioms pairedEval_error_iff
#print axioms paired_row_error_set
#print axioms paired_every_code_errs
#print axioms paired_not_represented
#print axioms paired_self_evaluation_not_represented
#print axioms pairedEvalFin
#print axioms pairedTargetFin
#print axioms pairedFin_card
#print axioms pairedFin_error_iff
#print axioms pairedFin_selected_errors_once
#print axioms pairedFin_every_code_errs
