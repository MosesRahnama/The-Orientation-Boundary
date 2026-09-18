import OperatorKO7.Meta.OperationalInexpressibility.RepeatDepthLicense

/-! Paired reach and axiom gate for exact finite-observer record cost. -/

set_option autoImplicit false

namespace OperatorKO7.Test.RepeatDepthLicenseReach

open OperatorKO7.Meta.OperationalInexpressibility.RepeatDepthLicense
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit

#check @observationFiber
#check @priorRepeats
#check @repeatDepth
#check @repeatStatus
#check @maxFiberCard
#check @mem_observationFiber
#check @mem_priorRepeats
#check @priorRepeats_ssubset_ownFiber
#check @repeatDepth_lt_ownFiberCard
#check @observationFiber_card_le_maxFiberCard
#check @repeatDepth_lt_maxFiberCard
#check @repeatDepth_strict_on_fiber
#check @repeatDepth_injective_on_fiber
#check @repeatDepth_values_on_fiber
#check @fiberVerdicts_repeatDepth_card
#check @repeatDepth_fiberMultiplicity_eq_maxFiberCard
#check @repeatDepth_fiberCodeDeficit_exact
#check @fiberRankChannel
#check @fiberRankChannel_val
#check @fiberRank_channel_licenses_repeatDepth
#check @fiberRank_channel_cardinality_exact
#check @repeatDepth_minimal_record_cost
#check @index_channel_licenses_every_target
#check @index_channel_licenses_repeat_targets
#check @exists_observationFiber_card_gt_one_of_not_injective
#check @repeat_status_collision_of_large_fiber
#check @repeat_status_collision_of_not_injective
#check @repeatStatus_factorsThrough_iff_injective
#check @repeat_status_unlicensed_iff_not_injective
#check @repeatStatus_fiberMultiplicity_le_two
#check @repeatStatus_fiberMultiplicity_eq_two_of_not_injective
#check @repeatStatus_fiberMultiplicity_eq_one_of_injective
#check @repeatStatus_fiberMultiplicity_eq_zero_of_empty
#check @repeatStatus_fiberMultiplicity_eq_zero_iff
#check @repeatStatus_fiberMultiplicity_eq_one_iff
#check @repeatStatus_fiberMultiplicity_eq_two_iff
#check @repeatStatus_fiberCodeDeficit_eq_zero_iff_injective
#check @repeatStatus_fiberCodeDeficit_eq_one_iff_not_injective
#check @repeatStatus_fiberCodeDeficit_dichotomy
#check @exists_observationFiber_card_gt_one
#check @repeat_status_collision
#check @repeat_status_unlicensed_by_current_observation
#check @repeatStatus_fiberMultiplicity_eq_two
#check @repeatStatus_fiberCodeDeficit_eq_one
#check @maxFiberCard_ge_ceiling_div
#check @repeatDepth_deficit_ge_ceiling_average
#check @constantObserver
#check @maxFiberCard_constantObserver
#check @repeatDepth_constantObserver
#check @constant_observer_side_channel_card_lower_bound
#check @no_fixed_finite_side_channel_licenses_all_repeatDepths
#check @repeat_depth_license_complete

/-! Concrete boundary cases for the exact classification. -/

example :
    fiberMultiplicity (constantObserver 0) (repeatStatus (constantObserver 0)) = 0 := by
  exact repeatStatus_fiberMultiplicity_eq_zero_of_empty (constantObserver 0) rfl

example :
    fiberMultiplicity (constantObserver 1) (repeatStatus (constantObserver 1)) = 1 := by
  apply repeatStatus_fiberMultiplicity_eq_one_of_injective
  · decide
  · intro i j _
    exact Subsingleton.elim i j

example :
    fiberCodeDeficit (constantObserver 3) (repeatStatus (constantObserver 3)) = 1 := by
  exact repeatStatus_fiberCodeDeficit_eq_one (constantObserver 3) (by decide)

example :
    fiberCodeDeficit (constantObserver 3) (repeatDepth (constantObserver 3)) =
      Nat.clog 2 3 := by
  simpa using repeatDepth_fiberCodeDeficit_exact (constantObserver 3)

example :
    fiberCodeDeficit (fun n : Fin 3 => n.val) (repeatStatus (fun n : Fin 3 => n.val)) = 0 := by
  apply (repeatStatus_fiberCodeDeficit_eq_zero_iff_injective
    (fun n : Fin 3 => n.val)).2
  intro i j hij
  exact Fin.ext hij

#print axioms observationFiber
#print axioms priorRepeats
#print axioms repeatDepth
#print axioms repeatStatus
#print axioms maxFiberCard
#print axioms mem_observationFiber
#print axioms mem_priorRepeats
#print axioms priorRepeats_ssubset_ownFiber
#print axioms repeatDepth_lt_ownFiberCard
#print axioms observationFiber_card_le_maxFiberCard
#print axioms repeatDepth_lt_maxFiberCard
#print axioms repeatDepth_strict_on_fiber
#print axioms repeatDepth_injective_on_fiber
#print axioms repeatDepth_values_on_fiber
#print axioms fiberVerdicts_repeatDepth_card
#print axioms repeatDepth_fiberMultiplicity_eq_maxFiberCard
#print axioms repeatDepth_fiberCodeDeficit_exact
#print axioms fiberRankChannel
#print axioms fiberRankChannel_val
#print axioms fiberRank_channel_licenses_repeatDepth
#print axioms fiberRank_channel_cardinality_exact
#print axioms repeatDepth_minimal_record_cost
#print axioms index_channel_licenses_every_target
#print axioms index_channel_licenses_repeat_targets
#print axioms exists_observationFiber_card_gt_one_of_not_injective
#print axioms repeat_status_collision_of_large_fiber
#print axioms repeat_status_collision_of_not_injective
#print axioms repeatStatus_factorsThrough_iff_injective
#print axioms repeat_status_unlicensed_iff_not_injective
#print axioms repeatStatus_fiberMultiplicity_le_two
#print axioms repeatStatus_fiberMultiplicity_eq_two_of_not_injective
#print axioms repeatStatus_fiberMultiplicity_eq_one_of_injective
#print axioms repeatStatus_fiberMultiplicity_eq_zero_of_empty
#print axioms repeatStatus_fiberMultiplicity_eq_zero_iff
#print axioms repeatStatus_fiberMultiplicity_eq_one_iff
#print axioms repeatStatus_fiberMultiplicity_eq_two_iff
#print axioms repeatStatus_fiberCodeDeficit_eq_zero_iff_injective
#print axioms repeatStatus_fiberCodeDeficit_eq_one_iff_not_injective
#print axioms repeatStatus_fiberCodeDeficit_dichotomy
#print axioms exists_observationFiber_card_gt_one
#print axioms repeat_status_collision
#print axioms repeat_status_unlicensed_by_current_observation
#print axioms repeatStatus_fiberMultiplicity_eq_two
#print axioms repeatStatus_fiberCodeDeficit_eq_one
#print axioms maxFiberCard_ge_ceiling_div
#print axioms repeatDepth_deficit_ge_ceiling_average
#print axioms constantObserver
#print axioms maxFiberCard_constantObserver
#print axioms repeatDepth_constantObserver
#print axioms constant_observer_side_channel_card_lower_bound
#print axioms no_fixed_finite_side_channel_licenses_all_repeatDepths
#print axioms repeat_depth_license_complete

end OperatorKO7.Test.RepeatDepthLicenseReach
