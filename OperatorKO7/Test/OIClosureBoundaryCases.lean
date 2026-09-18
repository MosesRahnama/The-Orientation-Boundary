import OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms
import OperatorKO7.Meta.OperationalInexpressibility.CostComparison
import OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation
import OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
import OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
import OperatorKO7.Meta.OperationalInexpressibility.RolePartitionInformation
import OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax
import OperatorKO7.Meta.OperationalInexpressibility.RelationalRecovery
import OperatorKO7.Meta.OperationalInexpressibility.RelationalSideChannel
import OperatorKO7.Meta.OperationalInexpressibility.NormalFormFaithfulTransport
import OperatorKO7.Meta.OperationalInexpressibility.CostWorkloadSemantics
import OperatorKO7.Meta.OperationalInexpressibility.BudgetedNoisyRecovery
import OperatorKO7.Meta.OperationalInexpressibility.JointTargetCapacity
import OperatorKO7.Meta.OperationalInexpressibility.SequentialMemoryRecovery

/-!
# Operational Inexpressibility boundary cases

This check file collects the edge cases required by the OI dispatch. It is a
supervisor validation target and introduces no manuscript-facing theorem.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.OIClosureBoundaryCases

open OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms
open OperatorKO7.Meta.OperationalInexpressibility.CostComparison
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
open OperatorKO7.Meta.OperationalInexpressibility.RolePartitionInformation
open OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax
open OperatorKO7.Meta.Decision.RecursorStopping

example : IsEmpty Empty := inferInstance

example : terminalMultiplicity singletonNormal () = 1 := by decide
example : terminalMultiplicity singletonLoop () = 0 := by decide
example : sourceConfluentB chain3 0 = true := by decide
example : sourceConfluentB fork3 0 = false := by decide
example : (path? chain3 0 2).isSome := by decide
example : (sourceNonjoinabilityPair? fork3 0).isSome := by decide

/-- One intervention covers two defects. -/
def sharedRepair : RepairInput (Fin 2) Unit where
  interventions := unitEnumeration
  bad := Finset.univ
  closes := fun _ => Finset.univ
  price := fun _ => 1

example : (minimumRepairCover? sharedRepair).isSome := by decide
example : (minimumPriceRepair? sharedRepair).isSome := by decide

/-- A nonempty defect set with no available intervention. -/
def uncoverableRepair : RepairInput Unit Empty where
  interventions := OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms.emptyEnumeration
  bad := {()}
  closes := fun j => nomatch j
  price := fun j => nomatch j

example : minimumRepairCover? uncoverableRepair = none := by decide
example : minimumPriceRepair? uncoverableRepair = none := by decide

example : boundedWitnessRank? 4 (fun n => decide (0 ≤ n)) = some 0 := by decide
example : boundedWitnessRank? 4 (fun n => decide (7 ≤ n)) = none := by decide

example : compareBurden 0 0 0 = .tie := by decide
example : compareBurden 0 1 0 = .carryCheaper := by decide
example : compareBurden 1 1 0 = .tie := by decide
example : compareBurden 1 0 0 = .confessCheaper := by decide
example : burdenRatio? 1 0 0 = none := by decide
example : carryResidualRatio? 1 0 = none := by decide
example : 3 * cumulativeCarryDoubled 1 2 = 3 * 4 * 5 := by
  simpa using cumulativeCarryDoubled_closed 1 2
example : cumulativeConfessDoubled 2 2 = 2 * 2 * 3 + 2 * 3 := by
  exact cumulativeConfessDoubled_closed 2 2

#check @zero_unitCost_control
#check @zero_payload_control
#check @zero_arity_marginalCost
#check @zero_current_benefit_future_reward_continues

example :
    letI := threeValueEnumeration.toFintype
    alphabetSize threeValueEnumeration (fun _ : Fin 3 => ()) (fun x => x) = 3 := by
  decide

example :
    letI := threeValueEnumeration.toFintype
    Nat.clog 2
      (alphabetSize threeValueEnumeration (fun _ : Fin 3 => ()) (fun x => x)) = 2 := by
  exact three_values_require_two_bits

#check zeroMassCollision_support_pure
#check zeroMassCollision_not_fullCarrier
#check fullyNoisyBinary_risk_half
#check @bayesRisk_le_randomizedPostProcessedRisk
#check @bestSideEncoder?_eq_none_iff
#check @bayesRisk_mem_unitInterval

/-- A nonuniform frame law for the partial-role checks. -/
noncomputable def skewFrame (i : Fin 2) : ℝ := if i = 0 then 1 / 4 else 3 / 4

example : ∑ i, skewFrame i = 1 := by
  norm_num [Fin.sum_univ_two, skewFrame]

example : ∀ i, 0 ≤ skewFrame i := by
  intro i
  fin_cases i <;> norm_num [skewFrame]

#check @activeFrame_partitionGap
#check @uniform_dp_probability_map_agrees
#check @arbitrary_binary_role_law_resolves_all
#check activeMass_zero_spent_zero
#check @activeMass_one_residual_zero
#check zero_frames_zero_entropy

#check malformed_rule_rejected
#check out_of_range_path_rejected
#check trailing_words_rejected
#check @rootStep_has_checked_certificate
#check @faithful_rootStep_has_checked_certificate
#check @checkSerializedWithBound_fst
#check @deserializeCosted_snd_le
#check @serializedBinaryBits_eq
#check @deserializeBitsPrefix_serializeBits_append

#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.rary_remaining_counter_observation
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.rary_wrapper_observation
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryConservedAlong_iff_zeroDepth_or_balance


/-! ## Closeout-sprint generalization controls -/

#check @OperatorKO7.Meta.OperationalInexpressibility.RelationalRecovery.quotientRelationalRecovery_iff_fiberCommonWitness
#check @OperatorKO7.Meta.OperationalInexpressibility.RelationalRecovery.pairwiseFiberCompatible_not_sufficient
#check @OperatorKO7.Meta.OperationalInexpressibility.RelationalRecovery.boolIdentity_falseOnlyLanguage_fails
#check @OperatorKO7.Meta.OperationalInexpressibility.RelationalSideChannel.partialRelationalSideChannel_iff_hypergraphColoring
#check @OperatorKO7.Meta.OperationalInexpressibility.RelationalSideChannel.threeWay_higherOrder_sideChannel_separation
#check @OperatorKO7.Meta.OperationalInexpressibility.NormalFormFaithfulTransport.UNred_transfer
#check @OperatorKO7.Meta.OperationalInexpressibility.NormalFormFaithfulTransport.UNconv_transfer
#check @OperatorKO7.Meta.OperationalInexpressibility.NormalFormFaithfulTransport.normalForm_injectivity_is_required
#check @OperatorKO7.Meta.OperationalInexpressibility.CostWorkloadSemantics.workload_growth_pair
#check @OperatorKO7.Meta.OperationalInexpressibility.CostWorkloadSemantics.repeatedPrefixCarryDoubled_gt_cached_of_positive
#check @OperatorKO7.Meta.OperationalInexpressibility.BudgetedNoisyRecovery.bestBudgetedSideEncoder?_minimal
#check @OperatorKO7.Meta.OperationalInexpressibility.BudgetedNoisyRecovery.bestBudgetedSideEncoder?_eq_none_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.JointTargetCapacity.licensed_pairedTarget_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.JointTargetCapacity.pairedTarget_exact_side_capacity
#check @OperatorKO7.Meta.OperationalInexpressibility.JointTargetCapacity.duplicated_target_product_bound_not_tight
#check @OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax.checkSerializedBitsStrict_rejects_trailing
#check @OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax.exists_strict_binary_certificate_iff_rootStep


#check @OperatorKO7.Meta.OperationalInexpressibility.SequentialMemoryRecovery.current_observation_can_forget_while_history_retains

end OperatorKO7.Test.OIClosureBoundaryCases
