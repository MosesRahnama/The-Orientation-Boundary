import OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence

/-!
Reach check for `Meta/OperationalInexpressibility/FiniteObserverRecurrence.lean`: every
public declaration is elaborated and its axiom inventory printed.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.FiniteObserverRecurrenceReach

open OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence

#check @finite_observer_orbit_has_recurrence
#check @recurrence_is_fixed_or_cycle
#check @seenBeforeOf
#check @seenBeforeOf_eq_true_iff
#check @finite_observer_has_first_repeat
#check @finite_observer_repeat_status_inexpressible
#check @finite_observer_repeatStatus_not_factorsThrough
#check @finite_observer_repeatStatus_not_verdictDeterminedBy
#check @seenBefore
#check @orbit
#check @orbit_eq
#check @parityObserve
#check @parityObserve_eq
#check @repeatStatus
#check @repeatStatus_eq
#check @current_observation_does_not_determine_repeat_status
#check @repeatStatus_not_factorsThrough

#print axioms finite_observer_orbit_has_recurrence
#print axioms recurrence_is_fixed_or_cycle
#print axioms seenBeforeOf
#print axioms seenBeforeOf_eq_true_iff
#print axioms finite_observer_has_first_repeat
#print axioms finite_observer_repeat_status_inexpressible
#print axioms finite_observer_repeatStatus_not_factorsThrough
#print axioms finite_observer_repeatStatus_not_verdictDeterminedBy
#print axioms seenBefore
#print axioms orbit
#print axioms orbit_eq
#print axioms parityObserve
#print axioms parityObserve_eq
#print axioms repeatStatus
#print axioms repeatStatus_eq
#print axioms current_observation_does_not_determine_repeat_status
#print axioms repeatStatus_not_factorsThrough


/-! ## Image dynamics, periodicity and a nonperiodic finite observation -/

#check @ObservationCompatible
#print axioms ObservationCompatible
#check @observationCompatible_iff_all_iterates
#print axioms observationCompatible_iff_all_iterates
#check @ObservedValue
#print axioms ObservedValue
#check @observedValue
#print axioms observedValue
#check @observationCompatible_iff_unique_image_dynamics
#print axioms observationCompatible_iff_unique_image_dynamics
#check @compatible_recurrence_propagates
#print axioms compatible_recurrence_propagates
#check @compatible_finite_observer_eventually_periodic
#print axioms compatible_finite_observer_eventually_periodic
#check @exponent_lt_pow_two
#print axioms exponent_lt_pow_two
#check @powerOfTwoObserve
#print axioms powerOfTwoObserve
#check @powerOfTwoObserve_eq_true_iff
#print axioms powerOfTwoObserve_eq_true_iff
#check @no_power_between_successive_powers
#print axioms no_power_between_successive_powers
#check @powerOfTwo_every_eventual_period_refuted
#print axioms powerOfTwo_every_eventual_period_refuted
#check @powerOfTwo_not_eventually_periodic
#print axioms powerOfTwo_not_eventually_periodic
#check @powerOfTwo_recurrence_not_persistent
#print axioms powerOfTwo_recurrence_not_persistent
#check @powerOfTwo_not_observationCompatible
#print axioms powerOfTwo_not_observationCompatible
#check @finite_observer_recurrence_without_eventual_periodicity
#print axioms finite_observer_recurrence_without_eventual_periodicity

example {X Q : Type} (F : X → X) (q : X → Q) :
    ObservationCompatible F q ↔
      ∃! G : ObservedValue q → ObservedValue q,
        ∀ x, G (observedValue q x) = observedValue q (F x) :=
  observationCompatible_iff_unique_image_dynamics F q

example :
    powerOfTwoObserve 1 = true ∧ powerOfTwoObserve 2 = true ∧
      powerOfTwoObserve 3 = false ∧ powerOfTwoObserve 4 = true := by
  decide

example :
    ¬ ∃ start period : Nat, 0 < period ∧ ∀ n, start ≤ n →
      powerOfTwoObserve (n + period) = powerOfTwoObserve n :=
  powerOfTwo_not_eventually_periodic

example :
    ∃ start period : Nat, start + period ≤ Fintype.card Bool ∧ 0 < period ∧
      ∀ n, start ≤ n → Bool.not^[n + period] false = Bool.not^[n] false := by
  exact compatible_finite_observer_eventually_periodic Bool.not
    (id : Bool → Bool) (fun _ _ h => congrArg Bool.not h) false


open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

#check @orbitObserver
#print axioms orbitObserver

#check @orbitObserver_coarsens_iff
#print axioms orbitObserver_coarsens_iff

#check @compatible_iterate_mul_of_return
#print axioms compatible_iterate_mul_of_return

#check @compatible_periodic_cancel
#print axioms compatible_periodic_cancel

#check @compatible_observer_returns_after_card
#print axioms compatible_observer_returns_after_card

#check @compatible_observer_kernel_stable
#print axioms compatible_observer_kernel_stable

#check @compatible_observer_kernel_eq_at_card_pred
#print axioms compatible_observer_kernel_eq_at_card_pred

#check @compatible_license_loss_dichotomy
#print axioms compatible_license_loss_dichotomy

#check @compatible_license_loss_cutoff_le_card_pred
#print axioms compatible_license_loss_cutoff_le_card_pred

#check @compatible_license_at_card_pred_iff_persistent
#print axioms compatible_license_at_card_pred_iff_persistent

#check @compatible_license_stable_after_card
#print axioms compatible_license_stable_after_card

example : ObservationCompatible (fun _ : Bool => false) (id : Bool → Bool) := by
  intro _ _ _
  rfl

example :
    Licensed (orbitObserver (fun _ : Bool => false) (id : Bool → Bool) 0) id ∧
      ¬ Licensed (orbitObserver (fun _ : Bool => false) (id : Bool → Bool) 1) id := by
  refine ⟨fun _ _ h => h, ?_⟩
  intro h
  have heq : (false : Bool) = true := h false true rfl
  cases heq

example : ∀ n, Licensed (orbitObserver Bool.not (id : Bool → Bool) n) id := by
  apply (compatible_license_at_card_pred_iff_persistent Bool.not id
    (fun _ _ h => congrArg Bool.not h) id).mp
  change Licensed Bool.not (id : Bool → Bool)
  intro x y hxy
  cases x <;> cases y <;> simp_all

example : ∀ n, Licensed (orbitObserver (id : Empty → Empty) id n) id := by
  intro n x
  cases x



#check @countdown
#print axioms countdown

#check @countdown_iterate_val
#print axioms countdown_iterate_val

#check @countdownTarget
#print axioms countdownTarget

#check @countdown_compatible
#print axioms countdown_compatible

#check @countdown_license_iff
#print axioms countdown_license_iff

#check @finite_license_bound_sharp
#print axioms finite_license_bound_sharp

example : ((countdown 3)^[2] ⟨3, by decide⟩).val = 1 := rfl

example :
    Licensed (orbitObserver (countdown 3) id 2) (countdownTarget 3) ∧
      ¬ Licensed (orbitObserver (countdown 3) id 3) (countdownTarget 3) := by
  refine ⟨(countdown_license_iff 3 (by decide) 2).mpr (by decide), ?_⟩
  intro h
  have hbad := (countdown_license_iff 3 (by decide) 3).mp h
  omega

example : ∀ n, ¬ Licensed
    (orbitObserver (id : Bool → Bool) (fun _ : Bool => ()) n) id := by
  intro n h
  have hbad : (false : Bool) = true := h false true rfl
  cases hbad


#check @observedValue_eq_iff
#print axioms observedValue_eq_iff
#check @observedValue_surjective
#print axioms observedValue_surjective
#check @observationCompatible_image_iff
#print axioms observationCompatible_image_iff
#check @orbitObserver_image_eq_iff
#print axioms orbitObserver_image_eq_iff
#check @licensed_orbitObserver_image_iff
#print axioms licensed_orbitObserver_image_iff
#check @finite_image_orbit_has_recurrence
#print axioms finite_image_orbit_has_recurrence
#check @compatible_finite_image_eventually_periodic
#print axioms compatible_finite_image_eventually_periodic
#check @compatible_image_kernel_stable
#print axioms compatible_image_kernel_stable
#check @compatible_image_kernel_eq_at_card_pred
#print axioms compatible_image_kernel_eq_at_card_pred
#check @compatible_license_loss_cutoff_le_image_card_pred
#print axioms compatible_license_loss_cutoff_le_image_card_pred
#check @compatible_license_at_image_card_pred_iff_persistent
#print axioms compatible_license_at_image_card_pred_iff_persistent
#check @compatible_license_stable_after_image_card
#print axioms compatible_license_stable_after_image_card

example :
    ∀ n, Licensed (orbitObserver Bool.not (fun b : Bool => if b then (7 : Nat) else 12) n) id := by
  let q : Bool → Nat := fun b => if b then 7 else 12
  have hq : Function.Injective q := by
    intro x y h
    cases x <;> cases y <;> simp_all [q]
  letI : Finite (ObservedValue q) := Finite.of_surjective _ (observedValue_surjective q)
  have hcard : Nat.card (ObservedValue q) = 2 := by
    let e : Bool ≃ ObservedValue q := Equiv.ofBijective (observedValue q)
      ⟨fun _ _ h => hq (congrArg Subtype.val h), observedValue_surjective q⟩
    simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using (Nat.card_congr e).symm
  have hc : ObservationCompatible Bool.not q := by
    intro x y h
    exact congrArg (fun b => q (!b)) (hq h)
  apply (compatible_license_at_image_card_pred_iff_persistent Bool.not q hc id).mp
  rw [hcard]
  change Licensed (fun b => q (!b)) id
  intro x y h
  cases x <;> cases y <;> simp_all [q]

example :
    ∃ i j : Nat, i < j ∧ j ≤ Nat.card (ObservedValue (fun _ : Nat => (42 : Nat))) ∧
      (fun _ : Nat => (42 : Nat)) (Nat.succ^[i] 0) =
        (fun _ : Nat => (42 : Nat)) (Nat.succ^[j] 0) := by
  let q : Nat → Nat := fun _ => 42
  let s : Unit → ObservedValue q := fun _ => observedValue q 0
  have hs : Function.Surjective s := by
    intro y
    refine ⟨(), ?_⟩
    apply Subtype.ext
    obtain ⟨x, hx⟩ := y.property
    exact hx
  letI : Finite (ObservedValue q) := Finite.of_surjective s hs
  exact finite_image_orbit_has_recurrence Nat.succ q 0

example : Infinite (ObservedValue (id : Nat → Nat)) :=
  Infinite.of_injective (observedValue id) (fun _ _ h => congrArg Subtype.val h)

end OperatorKO7.Test.FiniteObserverRecurrenceReach
