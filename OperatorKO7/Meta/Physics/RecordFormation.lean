import Mathlib.Data.Real.Basic

/-!
# Record Formation

Per-cert record-formation bookkeeping for the procedure-side Landauer upgrade.

This module does not prove any thermodynamic inequality. It isolates the
theorem-facing carriers needed by the later Landauer-bound surface:

- explicit record / certificate / overwritten / discarded bit counts;
- an objective-record carrier separated from merely redundant representation;
- named C1-C6 applicability predicates for stage-2 record formation.

The thermodynamic lower bound itself remains an explicit physical assumption in
`LandauerHeatBound.lean`.
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

/-- Objective classical record state: a reliable bit payload together with the
redundancy threshold bookkeeping used to mark objectivity. -/
structure ObjectiveRecordState where
  reliableBits : Nat
  redundancyCount : Nat
  redundancyThreshold : Nat
deriving DecidableEq, Repr

/-- Merely redundant representation data. This records duplication/bookkeeping
below the objectivity threshold without claiming a classical record. -/
structure RedundantRepresentation where
  representedBits : Nat
  redundantCopies : Nat
deriving DecidableEq, Repr

/-- Stage-2 record-formation event used by the procedure-side Landauer upgrade. -/
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

/-- Stage-2 objectivity means that redundancy clears the threshold and that the
resulting classical record carries a positive reliable payload. -/
def IsObjectiveRecordState (E : RecordFormationEvent) : Prop :=
  E.objectiveState.redundancyThreshold ≤ E.objectiveState.redundancyCount ∧
    0 < reliableRecordBitCount E

/-- Short theorem-facing alias used by the example and calibration layers. -/
abbrev IsObjective (E : RecordFormationEvent) : Prop :=
  IsObjectiveRecordState E

/-- Merely redundant representation means that copies exist but the event does
not yet support an objective classical record. -/
def IsOnlyRedundantRepresentation (E : RecordFormationEvent) : Prop :=
  0 < E.redundantRepresentation.redundantCopies ∧
    ¬ IsObjectiveRecordState E

/-- C1: a thermal bath at positive temperature is present during stage 2. -/
def C1_ThermalBathPresent (T : ℝ) : Prop :=
  0 < T

/-- C2: the event has produced an objective classical register. -/
def C2_ClassicalRegisterCreated (E : RecordFormationEvent) : Prop :=
  IsObjectiveRecordState E

/-- C3: the apparatus is cyclic or the entropy bookkeeping is closed, and the
tracked system/memory entropy debts are zero. -/
def C3_CyclicApparatusOrEntropyAccounted (E : RecordFormationEvent) : Prop :=
  (E.cyclicStage2 ∨ E.entropyBudgetClosed) ∧
    E.systemEntropyDebtBits = 0 ∧
    E.memoryEntropyDebtBits = 0

/-- C4: the irreversible stage-2 map does not allow a bath-inclusive reversal
inside the bookkeeping surface. -/
def C4_BathIrreversible (E : RecordFormationEvent) : Prop :=
  E.bathIrreversible

/-- C5: there is no unaccounted work reservoir, and the tracked external work
term is therefore zero. -/
def C5_NoUnaccountedWorkReservoir (E : RecordFormationEvent) : Prop :=
  E.noUnaccountedWorkReservoir ∧ E.externalWork = 0

/-- C6: the record, certificate, and discarded-bit ledgers agree on the same
objective reliable-bit count. -/
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
