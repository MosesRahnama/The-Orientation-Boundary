import OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation

set_option autoImplicit false

namespace OperatorKO7.Test.TransitionConservationReach

/-! Current public source surface, including generated structure projections and inductive constructors, for supervisor validation. -/

#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.dot
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.increment
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reading
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reading_sub_eq_dot_increment
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.ConstantFrom
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.AnnihilatesReachableIncrements
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.constantFrom_iff_annihilatesReachableIncrements
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.coeffDiff
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reading_sub_reading_eq_diff
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.ReadingsAgreeFrom
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.readingsAgreeFrom_iff_initial_and_increment_difference
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.enumerationEquiv
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.indexedRelation
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.indexedRelationDecidable
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reflTransGen_map
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.indexed_reflTransGen_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reachableFromB
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reachableFromB_eq_true_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.enumeratedPairs
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.pair_mem_enumeratedPairs
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.IsViolatingEdge
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.violatingEdgeB
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.violatingEdgeB_eq_true_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.isViolatingEdgeDecidable
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.failingReachableEdge?
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.conservedFromB
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.failingReachableEdge?_sound
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.failingReachableEdge?_eq_none_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.conservedFromB_eq_true_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.binary_trace_conservation_classification
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.binary_full_affine_conservation_classification
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.binary_trace_equivalence_classification
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.binary_trace_equivalence_offset_shift
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryAffineCoordinate
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.RaryConservedAlong
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryAffineCoordinate_step
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryConservedAlong_iff_zeroDepth_or_balance
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryFullAffineCoordinate
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.RaryTraceEquivalent
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryTraceEquivalent_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryTraceEquivalent_iff_offsetShift
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.rary_payload_observation_is_affine
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryAffineCoordinate_eq_live_payload
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.zero_depth_reading_eq_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.zero_depth_duplicate_description
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countSuccR
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countWrapR
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countSuccR_rSPow
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countWrapR_rSPow
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countSuccR_replicate_pay
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countWrapR_replicate_pay
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countSuccR_rGPow_pay
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countWrapR_rGPow_pay
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.rary_remaining_counter_observation
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.rary_wrapper_observation
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryReading
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryReading_eq_affine
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.ActualRaryConservedAlong
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryConservedAlong_iff_zeroDepth_or_balance
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryFullReading
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.ActualRaryTraceEquivalent
#check @OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryTraceEquivalent_iff

#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.dot
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.increment
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reading
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reading_sub_eq_dot_increment
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.ConstantFrom
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.AnnihilatesReachableIncrements
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.constantFrom_iff_annihilatesReachableIncrements
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.coeffDiff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reading_sub_reading_eq_diff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.ReadingsAgreeFrom
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.readingsAgreeFrom_iff_initial_and_increment_difference
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.enumerationEquiv
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.indexedRelation
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.indexedRelationDecidable
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reflTransGen_map
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.indexed_reflTransGen_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reachableFromB
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.reachableFromB_eq_true_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.enumeratedPairs
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.pair_mem_enumeratedPairs
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.IsViolatingEdge
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.violatingEdgeB
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.violatingEdgeB_eq_true_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.isViolatingEdgeDecidable
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.failingReachableEdge?
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.conservedFromB
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.failingReachableEdge?_sound
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.failingReachableEdge?_eq_none_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.conservedFromB_eq_true_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.binary_trace_conservation_classification
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.binary_full_affine_conservation_classification
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.binary_trace_equivalence_classification
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.binary_trace_equivalence_offset_shift
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryAffineCoordinate
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.RaryConservedAlong
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryAffineCoordinate_step
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryConservedAlong_iff_zeroDepth_or_balance
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryFullAffineCoordinate
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.RaryTraceEquivalent
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryTraceEquivalent_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryTraceEquivalent_iff_offsetShift
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.rary_payload_observation_is_affine
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.raryAffineCoordinate_eq_live_payload
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.zero_depth_reading_eq_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.zero_depth_duplicate_description
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countSuccR
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countWrapR
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countSuccR_rSPow
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countWrapR_rSPow
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countSuccR_replicate_pay
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countWrapR_replicate_pay
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countSuccR_rGPow_pay
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.countWrapR_rGPow_pay
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.rary_remaining_counter_observation
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.rary_wrapper_observation
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryReading
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryReading_eq_affine
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.ActualRaryConservedAlong
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryConservedAlong_iff_zeroDepth_or_balance
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryFullReading
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.ActualRaryTraceEquivalent
#print axioms OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation.actualRaryTraceEquivalent_iff
open OperatorKO7.Meta.OperationalInexpressibility.ExecutableResolvingChannel
open OperatorKO7.Meta.OperationalInexpressibility.TransitionConservation

example :
    let E : Enumeration (Fin 3) :=
      { items := [0, 1, 2]
        nodup := by decide
        complete := by intro x; fin_cases x <;> simp }
    let R : Fin 3 → Fin 3 → Prop := fun i j => i.val + 1 = j.val
    let coeff : Fin 1 → Int := fun _ => 1
    let obs : Fin 3 → Fin 1 → Int := fun s _ => s.val
    failingReachableEdge? E R 0 coeff obs = some (0, 1) := by
  decide

example :
    let E : Enumeration (Fin 3) :=
      { items := [0, 1, 2]
        nodup := by decide
        complete := by intro x; fin_cases x <;> simp }
    let R : Fin 3 → Fin 3 → Prop := fun i j => i.val + 1 = j.val
    let coeff : Fin 2 → Int := fun i => if i = 0 then 1 else -1
    let obs : Fin 3 → Fin 2 → Int := fun s _ => s.val
    failingReachableEdge? E R 0 coeff obs = none := by
  decide

example :
    let E : Enumeration (Fin 3) :=
      { items := [0, 1, 2]
        nodup := by decide
        complete := by intro x; fin_cases x <;> simp }
    let R : Fin 3 → Fin 3 → Prop := fun i j => i.val + 1 = j.val
    let coeff : Fin 0 → Int := fun i => Fin.elim0 i
    let obs : Fin 3 → Fin 0 → Int := fun _ i => Fin.elim0 i
    failingReachableEdge? E R 0 coeff obs = none := by
  decide

example :
    let E : Enumeration (Fin 3) :=
      { items := [0, 1, 2]
        nodup := by decide
        complete := by intro x; fin_cases x <;> simp }
    let R : Fin 3 → Fin 3 → Prop := fun i j => i.val = 1 ∧ j.val = 2
    let coeff : Fin 1 → Int := fun _ => 1
    let obs : Fin 3 → Fin 1 → Int := fun s _ => s.val
    failingReachableEdge? E R 0 coeff obs = none := by
  decide

example :
    let E : Enumeration (ULift.{1} (Fin 2)) :=
      { items := [ULift.up 0, ULift.up 1]
        nodup := by decide
        complete := by intro x; rcases x with ⟨x⟩; fin_cases x <;> simp }
    let R : ULift.{1} (Fin 2) → ULift.{1} (Fin 2) → Prop :=
      fun i j => i.down = 0 ∧ j.down = 1
    reachableFromB E R (ULift.up 0) (ULift.up 1) = true := by
  decide

open OperatorKO7.Meta.Recursor.RaryDuplicator

example :
    let t := rOrbit (.base 0) (.pay 0) 4 3 2
    (countSuccR t, countPayR t, countWrapR t) = (2, 7, 2) := by
  norm_num [rOrbit, rGPow, rSPow, countSuccR, countPayR, countWrapR]

example : actualRaryReading 5 1 2 0 0 4 3 2 = 21 := by
  norm_num [actualRaryReading, rOrbit, rGPow, rSPow, countSuccR, countPayR, countWrapR]

example :
    actualRaryReading 2 17 2 0 0 4 0 3 =
      actualRaryReading 2 17 2 0 0 4 0 0 := by
  norm_num [actualRaryReading, rOrbit, rGPow, rSPow, countSuccR, countPayR, countWrapR]

example : ActualRaryConservedAlong 99 7 0 0 0 0 3 := by
  exact (actualRaryConservedAlong_iff_zeroDepth_or_balance 99 7 0 0 0 0 3).2 (Or.inl rfl)

end OperatorKO7.Test.TransitionConservationReach
