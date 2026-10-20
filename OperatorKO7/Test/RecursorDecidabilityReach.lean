import OperatorKO7.Meta.BoundaryObserver.RecursorDecidability
import OperatorKO7.Meta.BoundaryObserver.Instances.Recursor
import OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws

/-!
Reach and axiom gate for `Meta/BoundaryObserver/RecursorDecidability.lean`. Every public
declaration of the module has a `#check @` and a `#print axioms`.
-/

open OperatorKO7.Meta.BoundaryObserver.RecursorDecidability

#check @selfLoop
#check @selfLoop_return
#check @selfLoop_infinite_seq
#check @constantRun
#check @constantRun_pass
#check @constantRun_merged_pair
#check @constantRun_determines_only_constants
#check @constantRun_observed_not_determined
#check @content
#check @counter
#check @observed
#check @Pass
#check @decidablePass
#check @pass_realized
#check @counter_decreases
#check @pass_chain_counter
#check @pass_no_infinite_seq
#check @pass_transGen_counter
#check @pass_no_return
#check @pass_wellFounded
#check @content_constant_along_pass
#check @content_measure_constant
#check @counter_orients
#check @orienting_measure_not_content_determined
#check @counter_not_content_determined
#check @observed_determined_by_counter
#check @observed_eq_iff_zero_iff
#check @observed_not_content_determined
#check @rec_succ_root_reduct
#check @ne_app_rec
#check @returns_iff_observed
#check @returnsDecidable
#check @passes_reach_zero
#check @run_length_eq_counter
#check @counter_least_coordinate
#check @counter_is_coordinate
#check @leftEntropy
#check @leftEntropy_eq
#check @content_leaves_log
#check @counter_leaves_zero
#check @one_pass_one_bit

#check @OperatorKO7.Meta.BoundaryObserver.BoundaryPole.counterSideSymbol_trace
#check @OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws.countedRecursion_adaptive_zero_information
#check @OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws.countedRecursion_one_pass_bit
#check @OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws.countedRecursion_passes_logb_two
#check @OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws.Laws
#check @OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws.countedRecursion_laws

#print axioms selfLoop
#print axioms selfLoop_return
#print axioms selfLoop_infinite_seq
#print axioms constantRun
#print axioms constantRun_pass
#print axioms constantRun_merged_pair
#print axioms constantRun_determines_only_constants
#print axioms constantRun_observed_not_determined
#print axioms content
#print axioms counter
#print axioms observed
#print axioms Pass
#print axioms decidablePass
#print axioms pass_realized
#print axioms counter_decreases
#print axioms pass_chain_counter
#print axioms pass_no_infinite_seq
#print axioms pass_transGen_counter
#print axioms pass_no_return
#print axioms pass_wellFounded
#print axioms content_constant_along_pass
#print axioms content_measure_constant
#print axioms counter_orients
#print axioms orienting_measure_not_content_determined
#print axioms counter_not_content_determined
#print axioms observed_determined_by_counter
#print axioms observed_eq_iff_zero_iff
#print axioms observed_not_content_determined
#print axioms rec_succ_root_reduct
#print axioms ne_app_rec
#print axioms returns_iff_observed
#print axioms returnsDecidable
#print axioms passes_reach_zero
#print axioms run_length_eq_counter
#print axioms counter_least_coordinate
#print axioms counter_is_coordinate
#print axioms leftEntropy
#print axioms leftEntropy_eq
#print axioms content_leaves_log
#print axioms counter_leaves_zero
#print axioms one_pass_one_bit

#print axioms OperatorKO7.Meta.BoundaryObserver.BoundaryPole.counterSideSymbol_trace
#print axioms OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws.countedRecursion_adaptive_zero_information
#print axioms OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws.countedRecursion_one_pass_bit
#print axioms OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws.countedRecursion_passes_logb_two
#print axioms OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws.Laws
#print axioms OperatorKO7.Meta.BoundaryObserver.CountedRecursionLaws.countedRecursion_laws
