import Mathlib.Tactic
import OperatorKO7.Meta.HigherOrderRewriting_SystemTSyntax
import OperatorKO7.Meta.HigherOrderRewriting_TypeCostBoundary
import OperatorKO7.Meta.HigherOrderRewriting_ChannelCapacity
import OperatorKO7.Meta.HigherOrderRewriting_CapacityLawWeld
import OperatorKO7.Meta.HigherOrderRewriting_QuantitativeFace
import OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
import OperatorKO7.Meta.OperationalInexpressibility.LicenseCore
import OperatorKO7.Meta.OperationalInexpressibility.FiberDeficitCore
import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph
import OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence

/-!
# Finite tests of barrier and observation claims

This module proves three finite results.

- On `Prefix n`, the type observer has deficit `Nat.clog 2 (n + 1)`; adding
the Church-index channel makes the deficit zero. A polynomial-time
characterization for the unbounded domain remains open.
- On `Bool × Bool`, the coordinate probes are sufficient and irredundant,
while the combined probe is sufficient with one probe.
- On four states with one update, two labels read the current target, no
two-label observer both reads the target and respects the update, and a
three-label observer does both. The finite argument uses
`ObservationCompatible`. The recurrence theorem
`compatible_license_at_card_pred_iff_persistent` concerns orbit observers
and is not used here.

Relation: `Licensed`, `fiberMultiplicity`, `fiberDeficit`, and observation compatibility with a total update.
Closure: `Prefix n`, `Bool × Bool`, and `Fin 4`.
Strategy: leftmost-outermost cost through `betaCost` for the prefix result; not applicable otherwise.
Trust: kernel-only; finite results close by decidable computation.
Scope: the bounded prefix result and the two finite carriers stated above.
-/

set_option autoImplicit false

namespace OperatorKO7.HigherOrderRewritingPeerConjectures

open OperatorKO7.HigherOrderRewritingSystemT
open OperatorKO7.HigherOrderRewritingTypeCostBoundary
open OperatorKO7.HigherOrderRewritingChannelCapacity
open OperatorKO7.HigherOrderRewritingCapacityLawWeld
open OperatorKO7.HigherOrderRewritingQuantitativeFace
open OperatorKO7.Meta.OperationalInexpressibility.LiftOrRefuse
open OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit
open OperatorKO7.Meta.OperationalInexpressibility.Confusability
open OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion
open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel

/-! ## Imported declaration checks -/

#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.Prefix
#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.obs
#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.cost
#check @OperatorKO7.HigherOrderRewritingCapacityLawWeld.channelLicenses_iff_licensed
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.capacity_attained
#check @OperatorKO7.HigherOrderRewritingChannelCapacity.finIndexChannel
#check @OperatorKO7.HigherOrderRewritingQuantitativeFace.church_fiberDeficit
#check @OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit.fiberMultiplicity_le_one_iff
#check @OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit.fiberDeficit_eq_zero_iff_factorsThrough
#check @OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit.mem_fiberVerdicts
#check @OperatorKO7.Meta.OperationalInexpressibility.FiberDeficit.fiberVerdicts_card_le
#check @OperatorKO7.Meta.OperationalInexpressibility.LicenseCriterion.licensed_iff_factorsThrough
#check @OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence.compatible_license_at_card_pred_iff_persistent

/-! ## Bounded gap under the Church-index channel -/

/-- Maps each prefix in `Prefix n` to its Church index in `Fin (n + 1)`. -/
def prefixIndex (n : Nat) : Prefix n → Fin (n + 1) := fun t => finIndexChannel n t.1

/--
Proves: the type observer augmented by the Church-index channel licenses the prefix cost.
Does not prove: licensing outside `Prefix n`.
Relation: `Licensed (augmentObserver (obs n) (prefixIndex n)) (cost n)`.
Closure: the subtype carrier `Prefix n`.
Strategy: leftmost-outermost cost; the bridge `channelLicenses_iff_licensed` on `capacity_attained`.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem indexed_prefix_licensed (n : Nat) :
    Licensed (augmentObserver (obs n) (prefixIndex n)) (cost n) :=
  (channelLicenses_iff_licensed n (finIndexChannel n)).1 (capacity_attained n)

/--
Proves: the fiber multiplicity of the index-augmented type observer against the prefix cost is one.
Does not prove: a value for any other observer.
Relation: `fiberMultiplicity (augmentObserver (obs n) (prefixIndex n)) (cost n)`.
Closure: the subtype carrier `Prefix n`.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem indexed_fiberMultiplicity_eq_one (n : Nat) :
    fiberMultiplicity (augmentObserver (obs n) (prefixIndex n)) (cost n) = 1 := by
  apply le_antisymm
  · exact (fiberMultiplicity_le_one_iff _ _).2
      ((licensed_iff_factorsThrough _ _).1 (indexed_prefix_licensed n))
  · have hx : (⟨churchApp 0, churchApp_mem_churchPrefix n⟩ : Prefix n) =
        ⟨churchApp 0, churchApp_mem_churchPrefix n⟩ := rfl
    have hmem : cost n ⟨churchApp 0, churchApp_mem_churchPrefix n⟩ ∈
        fiberVerdicts (augmentObserver (obs n) (prefixIndex n)) (cost n)
          (augmentObserver (obs n) (prefixIndex n) ⟨churchApp 0, churchApp_mem_churchPrefix n⟩) :=
      mem_fiberVerdicts.2 ⟨_, rfl, rfl⟩
    have hpos : 0 < (fiberVerdicts (augmentObserver (obs n) (prefixIndex n)) (cost n)
        (augmentObserver (obs n) (prefixIndex n) ⟨churchApp 0, churchApp_mem_churchPrefix n⟩)).card :=
      Finset.card_pos.2 ⟨_, hmem⟩
    exact lt_of_lt_of_le hpos (fiberVerdicts_card_le _ _ _)

/--
Proves: the bounded gap-closure statement. The code deficit of the type observer against the
prefix cost is `Nat.clog 2 (n + 1)`, and the deficit of the index-augmented observer is zero: the
gap closes when the licensing channel is observed.
Relation: `fiberDeficit` of the two observers against `cost n`.
Closure: the subtype carrier `Prefix n`.
Strategy: leftmost-outermost cost.
Trust: kernel-only.
Scope: every `n : Nat`.
-/
theorem church_gap_closes_under_index (n : Nat) :
    fiberDeficit (obs n) (cost n) = Nat.clog 2 (n + 1) ∧
      fiberDeficit (augmentObserver (obs n) (prefixIndex n)) (cost n) = 0 :=
  ⟨church_fiberDeficit n,
    (fiberDeficit_eq_zero_iff_factorsThrough _ _).2
      ((licensed_iff_factorsThrough _ _).1 (indexed_prefix_licensed n))⟩

/-! ## Irredundancy and minimum probe count -/

/-- The three probes of the fixture: two coordinate fields and their combination. -/
inductive Probe where
  | a
  | b
  | z
  deriving DecidableEq, Fintype

/-- The state carrier of the fixture: two Boolean fields. -/
abbrev TwoField := Bool × Bool

/-- The value of a probe at a state, encoded in `Fin 4`. -/
def probeValue : Probe → TwoField → Fin 4
  | .a, x => if x.1 then 1 else 0
  | .b, x => if x.2 then 1 else 0
  | .z, x => if x.1 then (if x.2 then 3 else 2) else (if x.2 then 1 else 0)

/-- The joint observation of a probe set: each probe reports its value when selected. -/
def jointObservation (S : Finset Probe) (x : TwoField) :
    Option (Fin 4) × Option (Fin 4) × Option (Fin 4) :=
  (if Probe.a ∈ S then some (probeValue .a x) else none,
   if Probe.b ∈ S then some (probeValue .b x) else none,
   if Probe.z ∈ S then some (probeValue .z x) else none)

/--
Proves: nothing by itself; a probe set is sufficient when its joint observation licenses the
identity target, so the whole state is determined.
Does not prove: anything about costs other than the probe count.
Relation: `Licensed (jointObservation S) id`.
Closure: the finite carrier `Bool × Bool`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `S : Finset Probe`.
-/
def Sufficient (S : Finset Probe) : Prop := Licensed (jointObservation S) (id : TwoField → TwoField)

instance instDecidableSufficient (S : Finset Probe) : Decidable (Sufficient S) := by
  unfold Sufficient Licensed
  infer_instance

/--
Proves: nothing by itself; a probe set is irredundant when it is sufficient and removing any one of
its probes breaks sufficiency, which is what a collision pair per retained probe certifies.
Does not prove: minimality.
Relation: `Sufficient`.
Closure: the finite carrier `Bool × Bool`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `S : Finset Probe`.
-/
def Irredundant (S : Finset Probe) : Prop :=
  Sufficient S ∧ ∀ p ∈ S, ¬ Sufficient (S.erase p)

instance instDecidableIrredundant (S : Finset Probe) : Decidable (Irredundant S) := by
  unfold Irredundant
  infer_instance

/--
Proves: the two-field set is irredundant: it is sufficient, and dropping either field leaves a
collision pair.
Does not prove: minimality of the two-field set.
Relation: `Irredundant {a, b}`.
Closure: the finite carrier `Bool × Bool`.
Strategy: not applicable.
Trust: kernel-only; `decide`.
Scope: the fixture.
-/
theorem twoField_irredundant : Irredundant {Probe.a, Probe.b} := by
  decide

/--
Proves: the single combined probe is sufficient with one probe, so the irredundant two-field set is
not of least cost; irredundancy does not imply global minimality.
Does not prove: anything about weighted costs other than the probe count.
Relation: `Sufficient {z}` and probe counts.
Closure: the finite carrier `Bool × Bool`.
Strategy: not applicable.
Trust: kernel-only; `decide`.
Scope: the fixture.
-/
theorem irredundant_not_minimal :
    Irredundant {Probe.a, Probe.b} ∧ Sufficient {Probe.z} ∧
      ({Probe.z} : Finset Probe).card < ({Probe.a, Probe.b} : Finset Probe).card := by
  decide

/-! ## One-shot and updateable observation on four states -/

/-- The four-state fixture's target: one on the fourth state, zero elsewhere. -/
def fourTarget (s : Fin 4) : Bool := decide (s = 3)

/-- The single action: `a ↦ c`, `b ↦ d`, `c ↦ c`, `d ↦ d`. -/
def fourStep (s : Fin 4) : Fin 4 :=
  if s = 0 then 2 else if s = 1 then 3 else if s = 2 then 2 else 3

/--
Proves: nothing by itself; an observer is an updateable monitor when it licenses the target and is
compatible with the action, so the next observation is a function of the current one.
Does not prove: anything about longer horizons beyond what compatibility implies.
Relation: `Licensed q fourTarget` and observation compatibility with `fourStep`.
Closure: the finite carrier `Fin 4`.
Strategy: not applicable.
Trust: kernel-only.
Scope: every finite observer `q : Fin 4 → Fin k`.
-/
def UpdateableMonitor {k : Nat} (q : Fin 4 → Fin k) : Prop :=
  Licensed q fourTarget ∧ ∀ x y, q x = q y → q (fourStep x) = q (fourStep y)

instance instDecidableUpdateableMonitor {k : Nat} (q : Fin 4 → Fin k) :
    Decidable (UpdateableMonitor q) := by
  unfold UpdateableMonitor Licensed
  infer_instance

/--
Proves: two labels read the current target.
Does not prove: persistence of that reading.
Relation: `Licensed q fourTarget`.
Closure: the finite carrier `Fin 4`.
Strategy: not applicable.
Trust: kernel-only; `decide`.
Scope: the fixture.
-/
theorem oneShot_two_labels : ∃ q : Fin 4 → Fin 2, Licensed q fourTarget :=
  ⟨fun s => if fourTarget s then 1 else 0, by
    unfold Licensed
    decide⟩

/--
Proves: no two-label observer is an updateable monitor: every one of the sixteen either fails to
read the target or merges two states whose successors read differently.
Does not prove: anything about observers with more labels.
Relation: `UpdateableMonitor`.
Closure: the finite carrier `Fin 4`.
Strategy: not applicable.
Trust: kernel-only; `decide` over all sixteen functions.
Scope: the fixture.
-/
theorem no_updateable_two_labels : ∀ q : Fin 4 → Fin 2, ¬ UpdateableMonitor q := by
  decide

/--
Proves: the three-class observer `{a, c}, {b}, {d}` is an updateable monitor.
Does not prove: that three is least without `no_updateable_two_labels`.
Relation: `UpdateableMonitor`.
Closure: the finite carrier `Fin 4`.
Strategy: not applicable.
Trust: kernel-only; `decide`.
Scope: the fixture.
-/
theorem updateable_three_labels :
    UpdateableMonitor (fun s : Fin 4 => if s = 1 then (1 : Fin 3) else if s = 3 then 2 else 0) := by
  decide

/--
Proves: the separation. Two labels suffice for the one-shot reading, no two-label observer both
reads the target and is compatible with the action, and a three-label observer does both; so the
least updateable monitor has one more class than the least one-shot reading.
Does not prove: the separation on any other carrier, and nothing about orbit observers; the
recurrence theorem `compatible_license_at_card_pred_iff_persistent` of the observer framework
concerns orbit observers licensing the original-input target and is not used here.
Relation: `Licensed` and `UpdateableMonitor`.
Closure: the finite carrier `Fin 4`.
Strategy: not applicable.
Trust: kernel-only.
Scope: the fixture.
-/
theorem oneShot_updateable_separation :
    (∃ q : Fin 4 → Fin 2, Licensed q fourTarget) ∧
      (∀ q : Fin 4 → Fin 2, ¬ UpdateableMonitor q) ∧
      (∃ q : Fin 4 → Fin 3, UpdateableMonitor q) :=
  ⟨oneShot_two_labels, no_updateable_two_labels, ⟨_, updateable_three_labels⟩⟩

/-! ## Closed fixtures -/

example : fiberDeficit (augmentObserver (obs 4) (prefixIndex 4)) (cost 4) = 0 :=
  (church_gap_closes_under_index 4).2

example : ¬ Sufficient {Probe.a} := by decide
example : ¬ Sufficient {Probe.b} := by decide
example : Sufficient {Probe.a, Probe.b} := by decide
example : fourStep 0 = 2 ∧ fourStep 1 = 3 ∧ fourStep 2 = 2 ∧ fourStep 3 = 3 := by decide

end OperatorKO7.HigherOrderRewritingPeerConjectures
