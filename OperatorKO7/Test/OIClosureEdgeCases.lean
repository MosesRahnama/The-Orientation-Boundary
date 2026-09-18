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

set_option autoImplicit false

namespace OperatorKO7.Test.OIClosureEdgeCases

open OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms
open OperatorKO7.Meta.OperationalInexpressibility.CostComparison
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
open OperatorKO7.Meta.OperationalInexpressibility.RolePartitionInformation
open OperatorKO7.Meta.OperationalInexpressibility.RecursorCertificateSyntax
open OperatorKO7.Meta.InformationalIncompleteness.FiniteSupportEntropy

/-! ## Finite-relation edge cases -/

example : ¬ Nonempty Empty := by simp
example : terminalMultiplicity singletonNormal () = 1 := by decide
example : terminalMultiplicity singletonLoop () = 0 := by decide
example : sourceConfluentB chain3 0 = true := by decide
example : sourceConfluentB fork3 0 = false := by decide
example : boundedWitnessRank? 0 (fun n => decide (n = 0)) = some 0 := by decide
example : boundedWitnessRank? 3 (fun n => decide (7 ≤ n)) = none := by decide

/-- One intervention repairs both defects. -/
def sharedRepairInput : RepairInput (Fin 2) Unit where
  interventions := unitEnumeration
  bad := {0, 1}
  closes := fun _ => {0, 1}
  price := fun _ => 0

example : minimumRepairCover? sharedRepairInput = some {()} := by decide
example : minimumPriceRepair? sharedRepairInput = some {()} := by decide

/-- No intervention exists. -/
def uncoverableRepairInput : RepairInput Unit Empty where
  interventions := OperatorKO7.Meta.OperationalInexpressibility.FiniteCoordinateAlgorithms.emptyEnumeration
  bad := {()}
  closes := fun j => nomatch j
  price := fun j => nomatch j

example : minimumRepairCover? uncoverableRepairInput = none := by decide

/-! ## Cost edge cases -/

example : CostTie 0 0 0 := by decide
example : ¬ CostTie 0 1 0 := by decide
example : CostTie 1 1 0 := by decide
example : optimalActions 1 1 0 = {CostAction.carry, CostAction.confess} := by decide
example : burdenRatio? 1 0 0 = none := by decide
example : carryResidualRatio? 1 0 = none := by decide
example : cumulativeCarryDoubled 1 0 = 2 := by decide
example : cumulativeConfessDoubled 0 0 = 0 := by decide
example :
    OperatorKO7.Meta.Decision.RecursorStopping.raryMarginalCost 3 0 2 4 = 0 :=
  (OperatorKO7.Meta.Decision.RecursorStopping.zero_unitCost_control 3 2 4).2
example :
    OperatorKO7.Meta.Decision.RecursorStopping.raryMarginalCost 3 2 5 0 = 10 := by
  simpa using
    (OperatorKO7.Meta.Decision.RecursorStopping.zero_arity_marginalCost 3 2 5)

/-! ## Executable channel edge cases -/

/-- Complete enumeration of the empty carrier. -/
def emptyEnumeration : Enumeration Empty where
  items := []
  nodup := by simp
  complete := by intro x; exact nomatch x

example :
    letI := emptyEnumeration.toFintype
    alphabetSize emptyEnumeration (fun _ : Empty => ()) (fun _ : Empty => ()) = 0 := by
  decide

example :
    letI := threeValueEnumeration.toFintype
    alphabetSize threeValueEnumeration (fun _ : Fin 3 => ()) (fun x => x) = 3 := by
  decide

example :
    letI := threeValueEnumeration.toFintype
    Nat.clog 2 (alphabetSize threeValueEnumeration (fun _ : Fin 3 => ()) (fun x => x)) = 2 := by
  exact three_values_require_two_bits

example :
    decodeBits? threeValueEnumeration (fun _ : Fin 3 => ()) (fun x => x) ()
      (codeToBits threeValueEnumeration (fun _ : Fin 3 => ()) (fun x => x) ⟨2, by decide⟩) =
        some 2 := by
  decide

#check @stabilizedEncoder_permanent

/-! ## Noisy and support-relative edge cases -/

example : bayesRisk binaryTargetEnumeration fullyNoisyBinary (fun x => x) = 1 / 2 := by
  exact fullyNoisyBinary_risk_half

example : bayesRisk binaryTargetEnumeration zeroMassCollisionModel (fun x => x) = 0 := by
  exact zeroMassCollision_support_pure

example : 0 ≤ bayesRisk binaryTargetEnumeration fullyNoisyBinary (fun x => x) :=
  bayesRisk_nonneg _ _ _

example : ¬ FullCarrierDeterministic (fun _ : Fin 2 => ()) (fun x => x) := by
  exact zeroMassCollision_not_fullCarrier

/-! ## Role-law edge cases -/

example : activeFrameSpentBits 0 = 0 := activeMass_zero_spent_zero
example : activeFrameResidualBits 1 (fun _ : Fin 1 => 1) = 0 :=
  activeMass_one_residual_zero _
example : HBits (activeFrameProb (r := 0) 1 (fun i => Fin.elim0 i)) = 0 :=
  zero_frames_zero_entropy

/-- A normalized, nonuniform two-frame law. -/
noncomputable def nonuniformFrameLaw : Fin 2 → ℝ := fun i => if i = 0 then 1 / 4 else 3 / 4

theorem nonuniformFrameLaw_sum : ∑ i, nonuniformFrameLaw i = 1 := by
  norm_num [nonuniformFrameLaw, Fin.sum_univ_two]

example :
    HBits (activeFrameProb (1 / 3) nonuniformFrameLaw) =
      activeFrameSpentBits (1 / 3) + activeFrameResidualBits (1 / 3) nonuniformFrameLaw :=
  HBits_activeFrameProb (1 / 3) nonuniformFrameLaw nonuniformFrameLaw_sum

/-! ## Certificate rejection edge cases -/

example : deserialize [certificateVersion, 9, 0, 0, 0, 0] = none := malformed_rule_rejected
example : deserialize [certificateVersion, 1, 4, 1, 2, 1, 0] = none := out_of_range_path_rejected
example : deserialize [certificateVersion, 0, 0, 0, 0, 0, 99] = none := trailing_words_rejected
example :
    deserializeBitsPrefix (serializeBits (successorCertificate .void .void .void)) =
      some (successorCertificate .void .void .void, []) := by
  have h := deserializeBitsPrefix_serializeBits_append
    (successorCertificate .void .void .void) []
  rwa [List.append_nil] at h
example :
    (checkSerializedWithBound (.recR .void .void (.delta .void))
      (.app .void (.recR .void .void .void))
      (serialize (successorCertificate .void .void .void))).1 = true := by
  rw [checkSerializedWithBound_fst]
  exact checkSerialized_successorCertificate _ _ _


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

end OperatorKO7.Test.OIClosureEdgeCases
