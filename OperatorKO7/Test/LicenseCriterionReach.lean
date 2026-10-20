import OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

/-!
Reach check for `Meta/OperationalInexpressibility/LicenseCriterion.lean`: every public
declaration is elaborated and its axiom inventory printed.
-/

set_option autoImplicit false

namespace OperatorKO7.Test.LicenseCriterionReach

open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion

#check @Licensed
#check @licensed_iff_factorsThrough
#check @licensed_iff_quotientFactorization
#check @unlicensed_iff_collision
#check @ObserverRefines
#check @observerRefines_iff_licenseTheory_inclusion
#check @ObserverRefines.refl
#check @ObserverRefines.trans
#check @Licensed.of_refinement
#check @not_licensed_coarse_of_not_licensed_fine
#check @licensed_identity_iff_injective
#check @licensed_of_injective
#check @mutual_refinement_iff_same_kernel
#check @license_of_coarser
#check @license_chain_lost_once
#check @counterObserver
#check @residualWork
#check @payloadCoordinate
#check @counter_licensed_for_residualWork
#check @constant_observer_unlicensed_for_payload
#check @constant_observer_payload_collision

#print axioms Licensed
#print axioms licensed_iff_factorsThrough
#print axioms licensed_iff_quotientFactorization
#print axioms unlicensed_iff_collision
#print axioms ObserverRefines
#print axioms observerRefines_iff_licenseTheory_inclusion
#print axioms ObserverRefines.refl
#print axioms ObserverRefines.trans
#print axioms Licensed.of_refinement
#print axioms not_licensed_coarse_of_not_licensed_fine
#print axioms licensed_identity_iff_injective
#print axioms licensed_of_injective
#print axioms mutual_refinement_iff_same_kernel
#print axioms license_of_coarser
#print axioms license_chain_lost_once
#print axioms counterObserver
#print axioms residualWork
#print axioms payloadCoordinate
#print axioms counter_licensed_for_residualWork
#print axioms constant_observer_unlicensed_for_payload
#print axioms constant_observer_payload_collision


/-! ## Fixed-codomain classification and executed dependency-pair counts -/

#check @fixedTarget_licenseTheory_inclusion_iff
#print axioms fixedTarget_licenseTheory_inclusion_iff
#check @observerRefines_iff_binary_licenseTheory
#print axioms observerRefines_iff_binary_licenseTheory
#check @same_binary_licenseTheory_iff_same_kernel
#print axioms same_binary_licenseTheory_iff_same_kernel
#check @singleton_targets_do_not_detect_refinement
#print axioms singleton_targets_do_not_detect_refinement
#check @counterObserver_injective
#print axioms counterObserver_injective
#check @counterObserver_licenses_every_target
#print axioms counterObserver_licenses_every_target
#check @freeRecursor_dp_cost_eq_rank
#print axioms freeRecursor_dp_cost_eq_rank
#check @freeRecursor_counter_licensed_for_dp_cost
#print axioms freeRecursor_counter_licensed_for_dp_cost
#check @freeRecursor_dp_execution
#print axioms freeRecursor_dp_execution
#check @freeRecursor_dp_cost_payload_independent
#print axioms freeRecursor_dp_cost_payload_independent
#check @freeRecursorPayload
#print axioms freeRecursorPayload
#check @freeRecursor_rank_not_injective
#print axioms freeRecursor_rank_not_injective
#check @freeRecursor_counter_unlicensed_for_payload
#print axioms freeRecursor_counter_unlicensed_for_payload
#check @freeRecursor_erased_payload_execution_pair
#print axioms freeRecursor_erased_payload_execution_pair
#check @freeRecursor_lossy_execution_license
#print axioms freeRecursor_lossy_execution_license

example {X Q₁ Q₂ V : Type} (q₁ : X → Q₁) (q₂ : X → Q₂) :
    (∀ P : X → V, Licensed q₂ P → Licensed q₁ P) ↔
      Subsingleton V ∨ ObserverRefines q₁ q₂ :=
  fixedTarget_licenseTheory_inclusion_iff V q₁ q₂

example {X Q₁ Q₂ : Type} (q₁ : X → Q₁) (q₂ : X → Q₂) :
    ObserverRefines q₁ q₂ ↔
      ∀ P : X → Bool, Licensed q₂ P → Licensed q₁ P :=
  observerRefines_iff_binary_licenseTheory q₁ q₂

example (k : Nat) : Function.Injective (counterObserver k) :=
  counterObserver_injective k

open OperatorKO7.Meta.Recursor.DPConfessionLicense
open OperatorKO7.Meta.OperationalInexpressibility.FreeRecursorKernel

example :
    ¬ Function.Injective dpRank ∧ Licensed dpRank dpMachine.cost ∧
      ¬ Licensed dpRank freeRecursorPayload :=
  freeRecursor_lossy_execution_license

example :
    dpMachine.Steps 2
      (.recR .void (.delta .void) (.delta (.delta .void)))
      (.recR .void (.delta .void) .void) :=
  freeRecursor_dp_execution .void (.delta .void) (.delta (.delta .void))


/-! ## Actual termination and nontermination in payload-loop extensions -/

#check @PayloadLoopStep
#print axioms PayloadLoopStep
#check @PayloadLoopStep.call
#print axioms PayloadLoopStep.call
#check @PayloadLoopStep.payloadLoop
#print axioms PayloadLoopStep.payloadLoop
#check @PayloadLoopBad
#print axioms PayloadLoopBad
#check @PayloadLoopTerminates
#print axioms PayloadLoopTerminates
#check @payloadLoop_bad_dp_iff
#print axioms payloadLoop_bad_dp_iff
#check @payloadLoop_self_of_bad
#print axioms payloadLoop_self_of_bad
#check @not_accessible_of_self_step
#print axioms not_accessible_of_self_step
#check @payloadLoop_terminates_of_not_bad
#print axioms payloadLoop_terminates_of_not_bad
#check @payloadLoop_terminates_iff
#print axioms payloadLoop_terminates_iff
#check @payloadLoop_infinite_run
#print axioms payloadLoop_infinite_run
#check @payloadLoop_licensed_iff_empty
#print axioms payloadLoop_licensed_iff_empty
#check @universal_payload_loops_rank_zero_collision
#print axioms universal_payload_loops_rank_zero_collision
#check @payloadSensitive_termination_collision
#print axioms payloadSensitive_termination_collision
#check @arbitrary_system_counter_unlicensed
#print axioms arbitrary_system_counter_unlicensed
#check @payloadSensitive_execution_witness
#print axioms payloadSensitive_execution_witness

example (P : RecursorTerm → Prop) :
    Licensed dpRank (PayloadLoopTerminates P) ↔ ∀ s, ¬ P s :=
  payloadLoop_licensed_iff_empty P

example :
    PayloadLoopTerminates (fun _ => False) (.recR .void .void (.delta .void)) :=
  (payloadLoop_terminates_iff _ _).mpr (fun h => h)

example :
    ¬ PayloadLoopTerminates (fun s => s = .delta .void)
      (.recR .void (.delta .void) (.delta .void)) := by
  intro h
  exact ((payloadLoop_terminates_iff _ _).mp h) rfl

#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.licensed_termination_of_wellFounded
#print axioms OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.licensed_termination_of_wellFounded
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.freeRecursor_termination_everywhere
#print axioms OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.freeRecursor_termination_everywhere
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.freeRecursor_termination_licensed_by_every_observer
#print axioms OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.freeRecursor_termination_licensed_by_every_observer
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.recursor_counter_licensed
#print axioms OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.recursor_counter_licensed
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.payloadLoop_false_step_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.payloadLoop_false_step_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.payloadLoop_false_termination_iff
#print axioms OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.payloadLoop_false_termination_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.counter_termination_scope_dichotomy
#print axioms OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.counter_termination_scope_dichotomy

example : Licensed (fun _ : RecursorTerm => ())
    (fun t => Acc (fun a b => FreeRecursorDPPair b a) t) :=
  freeRecursor_termination_licensed_by_every_observer (fun _ => ())

example (t : RecursorTerm) :
    PayloadLoopTerminates (fun _ => False) t ↔
      Acc (fun a b => FreeRecursorDPPair b a) t :=
  payloadLoop_false_termination_iff t


#check @coarsening_refines_of_le
#print axioms coarsening_refines_of_le

#check @licensed_of_coarsening_later
#print axioms licensed_of_coarsening_later

#check @unlicensed_of_coarsening_earlier
#print axioms unlicensed_of_coarsening_earlier

#check @first_license_loss_exists
#print axioms first_license_loss_exists

#check @first_license_loss_unique
#print axioms first_license_loss_unique

#check @license_cutoff_witness
#print axioms license_cutoff_witness

#check @license_coarsening_dichotomy
#print axioms license_coarsening_dichotomy

private def delayedCollapse (k n : Nat) (b : Bool) : Bool :=
  if n < k then b else false

example (k : Nat) : ∀ n, ObserverRefines (delayedCollapse k n)
    (delayedCollapse k (n + 1)) := by
  intro n x y hxy
  by_cases hn : n + 1 < k
  · have hprev : n < k := by omega
    simpa only [delayedCollapse, if_pos hn, if_pos hprev] using hxy
  · simp only [delayedCollapse, if_neg hn]

example (k n : Nat) :
    Licensed (delayedCollapse k n) (fun b : Bool => b) ↔ n < k := by
  constructor
  · intro h
    by_contra hn
    have heq : (false : Bool) = true := h false true (by simp [delayedCollapse, hn])
    cases heq
  · intro hn x y hxy
    simpa only [delayedCollapse, if_pos hn] using hxy

example : Licensed (fun (_ : Bool) => ()) (fun _ : Bool => ()) := by
  intro _ _ _
  rfl

private def temporaryCollapse (n : Nat) (b : Bool) : Bool :=
  if n = 1 then false else b

example :
    (Licensed (temporaryCollapse 0) (fun b => b) ∧
      ¬ Licensed (temporaryCollapse 1) (fun b => b) ∧
      Licensed (temporaryCollapse 2) (fun b => b)) ∧
      ¬ ObserverRefines (temporaryCollapse 1) (temporaryCollapse 2) := by
  change (Licensed (fun b : Bool => b) (fun b => b) ∧
      ¬ Licensed (fun _ : Bool => false) (fun b => b) ∧
      Licensed (fun b : Bool => b) (fun b => b)) ∧
      ¬ ObserverRefines (fun _ : Bool => false) (fun b => b)
  have hid : Licensed (fun b : Bool => b) (fun b => b) := fun _ _ h => h
  have hbad : ¬ Licensed (fun _ : Bool => false) (fun b => b) := by
    intro h
    have heq : (false : Bool) = true := h false true rfl
    cases heq
  exact ⟨⟨hid, hbad, hid⟩, fun href =>
    hbad ((licensed_iff_factorsThrough _ _).mpr href)⟩

example {X : Type} (P : X → Bool) :
    (∀ n : Nat, Licensed (fun x : X => (x, n)) P) := by
  intro n x y hxy
  exact congrArg P (congrArg Prod.fst hxy)


end OperatorKO7.Test.LicenseCriterionReach
