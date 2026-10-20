import OperatorKO7.Meta.BoundaryObserver.PairResolution

set_option autoImplicit false

/-! Paired checks for every public declaration of PairResolution. -/

#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.row
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.row
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.repeatProtocol
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.repeatProtocol
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.repeatProtocol_pairMenu
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.repeatProtocol_pairMenu
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.repeatProtocol_stop
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.repeatProtocol_stop
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.repeatProtocol_stop_false
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.repeatProtocol_stop_false
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_true
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_true
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_false
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_false
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_nil
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_nil
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_append
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_append
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.prefixMass_repeat
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.prefixMass_repeat
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.stoppedMass_repeat
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.stoppedMass_repeat
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_cost
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_cost
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_nonneg
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_nonneg
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.one_sub_bhattacharyya
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.one_sub_bhattacharyya
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.discrimination_term_le_two_sq
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.discrimination_term_le_two_sq
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.discrimination_le_four_one_sub_bhattacharyya
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.discrimination_le_four_one_sub_bhattacharyya
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_le_one_sub_quarter_discrimination
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_le_one_sub_quarter_discrimination
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_le_one
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_le_one
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.mapDecoder
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.mapDecoder
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_rejected_le_min
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.likelihood_rejected_le_min
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.min_le_sqrt_mul
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.min_le_sqrt_mul
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.sqrt_likelihood_mul
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.sqrt_likelihood_mul
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_level
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_level
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_error_le
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_error_le
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.discrimination_le_four
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.discrimination_le_four
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_error_le_discrimination
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_error_le_discrimination
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_error_le_exp
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_error_le_exp
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_information
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_information
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_target
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.repeat_target
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.pair_resolution_two_sided
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.pair_resolution_two_sided
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.deterministicRow
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.deterministicRow
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.deterministicRow_mass
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.deterministicRow_mass
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_deterministic_split
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_deterministic_split
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_deterministic_merged
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.bhattacharyya_deterministic_merged
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.split_pair_one_reading
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.split_pair_one_reading
#check @OperatorKO7.Meta.BoundaryObserver.PairResolution.merged_pair_no_information
#print axioms OperatorKO7.Meta.BoundaryObserver.PairResolution.merged_pair_no_information
