import Mathlib.Data.Real.Basic

/-!
# Static record-formation bookkeeping

This module defines bit-count records and six predicates over one static `RecordFormationEvent`.
`IsObjectiveRecordState` means only that a redundancy count reaches a threshold and the reliable-bit
count is positive. No temporal dynamics, persistence, stability, or physical record-formation process
is modeled here. The thermodynamic lower bound is an explicit assumption in the importing layer.

- explicit record / certificate / overwritten / discarded bit counts;
- an `ObjectiveRecordState` data record;
- named C1-C6 bookkeeping predicates.
-/

namespace OperatorKO7.Meta.Physics.RecordFormation

/-- Count of classical bits committed to the emitted record. -/
structure EmittedRecordBits where
  count : Nat
deriving DecidableEq, Repr

/-- Count of bits carried by the emitted certificate payload. -/
structure EmittedCertificateBits where
  count : Nat
deriving DecidableEq, Repr

/-- Count of overwritten bits during stage-2 stabilization. -/
structure OverwrittenBits where
  count : Nat
deriving DecidableEq, Repr

/-- Count of discarded bits that must be paid for thermodynamically if the
Landauer conditions apply. -/
structure DiscardedBits where
  count : Nat
deriving DecidableEq, Repr

/-- Reliable-bit and redundancy-count fields. The structure itself asserts no dynamics or
persistence. -/
structure ObjectiveRecordState where
  reliableBits : Nat
  redundancyCount : Nat
  redundancyThreshold : Nat
deriving DecidableEq, Repr

/-- Two natural-number fields for represented bits and redundant copies. -/
structure RedundantRepresentation where
  representedBits : Nat
  redundantCopies : Nat
deriving DecidableEq, Repr

/-- Static collection of bit counts, bookkeeping propositions, entropy-debt counts, and external
work. -/
structure RecordFormationEvent where
  recordBits : EmittedRecordBits
  certificateBits : EmittedCertificateBits
  overwrittenBits : OverwrittenBits
  discardedBits : DiscardedBits
  objectiveState : ObjectiveRecordState
  redundantRepresentation : RedundantRepresentation
  cyclicStage2 : Prop
  entropyBudgetClosed : Prop
  bathIrreversible : Prop
  noUnaccountedWorkReservoir : Prop
  systemEntropyDebtBits : Nat
  memoryEntropyDebtBits : Nat
  externalWork : ℝ

/-- Reliable classical bits carried by the objective record. -/
def reliableRecordBitCount (E : RecordFormationEvent) : Nat :=
  E.objectiveState.reliableBits

/-- Redundancy reaches the stored threshold and the reliable-bit count is positive. -/
def IsObjectiveRecordState (E : RecordFormationEvent) : Prop :=
  E.objectiveState.redundancyThreshold ≤ E.objectiveState.redundancyCount ∧
    0 < reliableRecordBitCount E

/-- Alias for `IsObjectiveRecordState`. -/
abbrev IsObjective (E : RecordFormationEvent) : Prop :=
  IsObjectiveRecordState E

/-- Positive redundant-copy count together with the negation of the static objective-state
predicate. -/
def IsOnlyRedundantRepresentation (E : RecordFormationEvent) : Prop :=
  0 < E.redundantRepresentation.redundantCopies ∧
    ¬ IsObjectiveRecordState E

/-- C1: a thermal bath at positive temperature is present during stage 2. -/
def C1_ThermalBathPresent (T : ℝ) : Prop :=
  0 < T

/-- C2 is definitionally the static `IsObjectiveRecordState` predicate. -/
def C2_ClassicalRegisterCreated (E : RecordFormationEvent) : Prop :=
  IsObjectiveRecordState E

/-- C3: the apparatus is cyclic or the entropy bookkeeping is closed, and the
tracked system/memory entropy debts are zero. -/
def C3_CyclicApparatusOrEntropyAccounted (E : RecordFormationEvent) : Prop :=
  (E.cyclicStage2 ∨ E.entropyBudgetClosed) ∧
    E.systemEntropyDebtBits = 0 ∧
    E.memoryEntropyDebtBits = 0

/-- C4 projects the stored proposition `bathIrreversible`. -/
def C4_BathIrreversible (E : RecordFormationEvent) : Prop :=
  E.bathIrreversible

/-- C5 combines the stored proposition `noUnaccountedWorkReservoir` with `externalWork = 0`. -/
def C5_NoUnaccountedWorkReservoir (E : RecordFormationEvent) : Prop :=
  E.noUnaccountedWorkReservoir ∧ E.externalWork = 0

/-- C6 equates three stored bit counts with `reliableRecordBitCount`. -/
def C6_HonestBitBookkeeping (E : RecordFormationEvent) : Prop :=
  E.recordBits.count = reliableRecordBitCount E ∧
    E.certificateBits.count = reliableRecordBitCount E ∧
    E.discardedBits.count = reliableRecordBitCount E

theorem objectiveRecordState_has_positive_bits
    {E : RecordFormationEvent} (hObj : IsObjectiveRecordState E) :
    0 < reliableRecordBitCount E :=
  hObj.2

theorem honestBitBookkeeping_projects_recordBits
    {E : RecordFormationEvent} (hC6 : C6_HonestBitBookkeeping E) :
    E.recordBits.count = reliableRecordBitCount E :=
  hC6.1

theorem honestBitBookkeeping_projects_certificateBits
    {E : RecordFormationEvent} (hC6 : C6_HonestBitBookkeeping E) :
    E.certificateBits.count = reliableRecordBitCount E :=
  hC6.2.1

theorem honestBitBookkeeping_projects_discardedBits
    {E : RecordFormationEvent} (hC6 : C6_HonestBitBookkeeping E) :
    E.discardedBits.count = reliableRecordBitCount E :=
  hC6.2.2

theorem objectiveRecordState_yields_positive_discardedBits
    {E : RecordFormationEvent}
    (hObj : IsObjectiveRecordState E)
    (hC6 : C6_HonestBitBookkeeping E) :
    0 < E.discardedBits.count := by
  simpa [honestBitBookkeeping_projects_discardedBits hC6] using
    objectiveRecordState_has_positive_bits hObj

theorem cyclicOrEntropyAccounted_zero_systemEntropyDebt
    {E : RecordFormationEvent} (hC3 : C3_CyclicApparatusOrEntropyAccounted E) :
    E.systemEntropyDebtBits = 0 :=
  hC3.2.1

theorem cyclicOrEntropyAccounted_zero_memoryEntropyDebt
    {E : RecordFormationEvent} (hC3 : C3_CyclicApparatusOrEntropyAccounted E) :
    E.memoryEntropyDebtBits = 0 :=
  hC3.2.2

theorem noUnaccountedWorkReservoir_zero_externalWork
    {E : RecordFormationEvent} (hC5 : C5_NoUnaccountedWorkReservoir E) :
    E.externalWork = 0 :=
  hC5.2

theorem objectiveRecordState_not_onlyRedundant
    {E : RecordFormationEvent}
    (hObj : IsObjectiveRecordState E) :
    ¬ IsOnlyRedundantRepresentation E := by
  intro hRedundant
  exact hRedundant.2 hObj

end OperatorKO7.Meta.Physics.RecordFormation
