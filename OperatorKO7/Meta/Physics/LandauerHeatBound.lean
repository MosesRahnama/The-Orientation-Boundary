import OperatorKO7.Meta.Physics.RecordFormation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Landauer Heat Bound

Conditional Landauer bookkeeping for stage-2 record formation.

This module keeps the thermodynamic inequality honest: the physical lower bound
appears only as an explicit field of `LandauerHeatLaw`. Lean then derives the
cleaner per-bit floor only after the named C1-C6 applicability conditions close
the entropy/work bookkeeping gaps.
-/

namespace OperatorKO7.Meta.Physics.LandauerHeatBound

open OperatorKO7.Meta.Physics.RecordFormation

/-- Explicit C1-C6 applicability package for the conditional Landauer bound. -/
structure LandauerApplicable (E : RecordFormationEvent) (T : ℝ) where
  C1_thermalBath : C1_ThermalBathPresent T
  C2_classicalRegister : C2_ClassicalRegisterCreated E
  C3_cyclicOrEntropyAccounted : C3_CyclicApparatusOrEntropyAccounted E
  C4_bathIrreversible : C4_BathIrreversible E
  C5_noUnaccountedWorkReservoir : C5_NoUnaccountedWorkReservoir E
  C6_honestBitBookkeeping : C6_HonestBitBookkeeping E

/-- Named four-way non-applicability partition used by the roadmap. -/
inductive NonApplicabilityClass where
  | premeasurementOnly
  | pendingRecord
  | freshMemory
  | weakInformation
deriving DecidableEq, Repr

/-- The per-event bound is either available as a number or unavailable with an
explicit non-applicability reason. -/
inductive LandauerBoundStatus (E : RecordFormationEvent) (kB T : ℝ) where
  | available (lowerBound : ℝ)
  | unavailable (reason : NonApplicabilityClass)

/-- Premeasurement only: no objective classical register has yet formed. -/
def PremeasurementOnly (E : RecordFormationEvent) : Prop :=
  ¬ C2_ClassicalRegisterCreated E

/-- Pending record: no record bits have yet been committed at stage 2. -/
def PendingRecord (E : RecordFormationEvent) : Prop :=
  E.recordBits.count = 0

/-- Fresh memory: no discarded classical payload is being overwritten. -/
def FreshMemory (E : RecordFormationEvent) : Prop :=
  E.discardedBits.count = 0

/-- Weak-information case: the event carries zero reliable record bits. -/
def WeakInformation (E : RecordFormationEvent) : Prop :=
  reliableRecordBitCount E = 0

/-- Explicit witness carrier for the roadmap's four non-applicability classes. -/
inductive NonApplicabilityWitness (E : RecordFormationEvent) where
  | premeasurementOnly (h : PremeasurementOnly E)
  | pendingRecord (h : PendingRecord E)
  | freshMemory (h : FreshMemory E)
  | weakInformation (h : WeakInformation E)

/-- The stage-2 Landauer price of one reliable bit at temperature `T`. -/
noncomputable def landauerPerBitCost (kB T : ℝ) : ℝ :=
  kB * T * Real.log 2

/-- The clean per-cert lower bound obtained once the bookkeeping corrections
have been discharged. -/
noncomputable def landauerLowerBound (E : RecordFormationEvent) (kB T : ℝ) : ℝ :=
  landauerPerBitCost kB T * (reliableRecordBitCount E : ℝ)

/-- Full physical law payload. The inequality is explicit here rather than
smuggled into a pure arithmetic proof. -/
structure LandauerHeatLaw
    (E : RecordFormationEvent) (kB T releasedHeat : ℝ) where
  kB_pos : 0 < kB
  lowerBound :
    releasedHeat ≥
      landauerPerBitCost kB T * (E.discardedBits.count : ℝ)
        - kB * T * ((E.systemEntropyDebtBits : ℝ) + (E.memoryEntropyDebtBits : ℝ))
        - E.externalWork

/-- Record/applicability trigger surface: the bound is relevant exactly when a
`LandauerApplicable` package exists. -/
def TriggersLandauerBound (E : RecordFormationEvent) (T : ℝ) : Prop :=
  Nonempty (LandauerApplicable E T)

/-- Unavailable status surface for the roadmap's non-applicability classes. -/
def unavailableOfNonApplicability
    {E : RecordFormationEvent} {kB T : ℝ}
    (w : NonApplicabilityWitness E) :
    LandauerBoundStatus E kB T :=
  match w with
  | .premeasurementOnly _ => .unavailable .premeasurementOnly
  | .pendingRecord _ => .unavailable .pendingRecord
  | .freshMemory _ => .unavailable .freshMemory
  | .weakInformation _ => .unavailable .weakInformation

/-- Available status surface once explicit applicability and the physical law
have both been supplied. -/
noncomputable def availableBound
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
  (_hApp : LandauerApplicable E T)
    (_law : LandauerHeatLaw E kB T releasedHeat) :
    LandauerBoundStatus E kB T :=
  .available (landauerLowerBound E kB T)

theorem landauer_heat_bound
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
    (hApp : LandauerApplicable E T)
    (law : LandauerHeatLaw E kB T releasedHeat) :
    releasedHeat ≥
      landauerPerBitCost kB T * (E.discardedBits.count : ℝ)
        - kB * T * ((E.systemEntropyDebtBits : ℝ) + (E.memoryEntropyDebtBits : ℝ))
        - E.externalWork := by
  have _ := hApp.C1_thermalBath
  simpa [landauerPerBitCost] using law.lowerBound

theorem landauer_per_bit_floor
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
    (hApp : LandauerApplicable E T)
    (law : LandauerHeatLaw E kB T releasedHeat) :
    releasedHeat ≥ landauerLowerBound E kB T := by
  have hBase := landauer_heat_bound hApp law
  have hSys :=
    cyclicOrEntropyAccounted_zero_systemEntropyDebt hApp.C3_cyclicOrEntropyAccounted
  have hMem :=
    cyclicOrEntropyAccounted_zero_memoryEntropyDebt hApp.C3_cyclicOrEntropyAccounted
  have hWork :=
    noUnaccountedWorkReservoir_zero_externalWork hApp.C5_noUnaccountedWorkReservoir
  have hDiscarded :=
    honestBitBookkeeping_projects_discardedBits hApp.C6_honestBitBookkeeping
  simpa [landauerLowerBound, landauerPerBitCost, hSys, hMem, hWork, hDiscarded] using hBase

theorem premeasurementOnly_not_applicable
    {E : RecordFormationEvent} {T : ℝ}
    (h : PremeasurementOnly E) :
    ¬ TriggersLandauerBound E T := by
  intro hTrig
  rcases hTrig with ⟨hApp⟩
  exact h hApp.C2_classicalRegister

theorem pendingRecord_not_applicable
    {E : RecordFormationEvent} {T : ℝ}
    (h : PendingRecord E) :
    ¬ TriggersLandauerBound E T := by
  intro hTrig
  rcases hTrig with ⟨hApp⟩
  have hPos : 0 < E.recordBits.count := by
    have hObjPos := objectiveRecordState_has_positive_bits hApp.C2_classicalRegister
    have hRec := honestBitBookkeeping_projects_recordBits hApp.C6_honestBitBookkeeping
    simpa [hRec] using hObjPos
  rw [h] at hPos
  exact Nat.lt_irrefl 0 hPos

theorem freshMemory_not_applicable
    {E : RecordFormationEvent} {T : ℝ}
    (h : FreshMemory E) :
    ¬ TriggersLandauerBound E T := by
  intro hTrig
  rcases hTrig with ⟨hApp⟩
  have hPos : 0 < E.discardedBits.count :=
    objectiveRecordState_yields_positive_discardedBits
      hApp.C2_classicalRegister
      hApp.C6_honestBitBookkeeping
  rw [h] at hPos
  exact Nat.lt_irrefl 0 hPos

theorem weakInformation_not_applicable
    {E : RecordFormationEvent} {T : ℝ}
    (h : WeakInformation E) :
    ¬ TriggersLandauerBound E T := by
  intro hTrig
  rcases hTrig with ⟨hApp⟩
  have hPos := objectiveRecordState_has_positive_bits hApp.C2_classicalRegister
  rw [h] at hPos
  exact Nat.lt_irrefl 0 hPos

theorem nonApplicabilityWitness_not_applicable
    {E : RecordFormationEvent} {T : ℝ}
    (w : NonApplicabilityWitness E) :
    ¬ TriggersLandauerBound E T := by
  cases w with
  | premeasurementOnly h => exact premeasurementOnly_not_applicable h
  | pendingRecord h => exact pendingRecord_not_applicable h
  | freshMemory h => exact freshMemory_not_applicable h
  | weakInformation h => exact weakInformation_not_applicable h

theorem unavailableOfNonApplicability_isUnavailable
    {E : RecordFormationEvent} {kB T : ℝ}
    (w : NonApplicabilityWitness E) :
    ∃ reason,
      unavailableOfNonApplicability (kB := kB) (T := T) w =
        LandauerBoundStatus.unavailable reason := by
  cases w with
  | premeasurementOnly _ => exact ⟨.premeasurementOnly, rfl⟩
  | pendingRecord _ => exact ⟨.pendingRecord, rfl⟩
  | freshMemory _ => exact ⟨.freshMemory, rfl⟩
  | weakInformation _ => exact ⟨.weakInformation, rfl⟩

end OperatorKO7.Meta.Physics.LandauerHeatBound
