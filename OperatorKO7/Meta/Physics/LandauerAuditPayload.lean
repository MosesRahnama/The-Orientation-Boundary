import OperatorKO7.Meta.Physics.LandauerHeatBound

/-!
# Landauer applicability payload

The applicable constructor stores the lower-bound expression when supplied with applicability and
heat-law witnesses. The non-applicable constructor stores no bound and records one
`NonApplicabilityClass`. Its six condition fields are all marked `uncertified`; that snapshot means
that a complete six-condition package was not supplied, not that every individual condition failed.
-/

namespace OperatorKO7.Meta.Physics.LandauerAuditPayload

set_option linter.dupNamespace false

open OperatorKO7.Meta.Physics.RecordFormation
open OperatorKO7.Meta.Physics.LandauerHeatBound

/-- Per-condition certification state for the C1-C6 surface. -/
inductive ConditionCertificationStatus where
  | certified
  | uncertified
deriving DecidableEq, Repr

/-- Audit-facing snapshot of the C1-C6 applicability checklist. -/
structure LandauerApplicabilitySnapshot where
  C1_thermalBath : ConditionCertificationStatus
  C2_classicalRegister : ConditionCertificationStatus
  C3_cyclicOrEntropyAccounted : ConditionCertificationStatus
  C4_bathIrreversible : ConditionCertificationStatus
  C5_noUnaccountedWorkReservoir : ConditionCertificationStatus
  C6_honestBitBookkeeping : ConditionCertificationStatus
deriving DecidableEq, Repr

/-- Fully certified applicability snapshot. -/
def fullyCertifiedApplicabilitySnapshot : LandauerApplicabilitySnapshot where
  C1_thermalBath := .certified
  C2_classicalRegister := .certified
  C3_cyclicOrEntropyAccounted := .certified
  C4_bathIrreversible := .certified
  C5_noUnaccountedWorkReservoir := .certified
  C6_honestBitBookkeeping := .certified

/-- Snapshot indicating that no complete C1-C6 certification package is represented. It does not
assert the failure of each individual condition. -/
def unavailableApplicabilitySnapshot : LandauerApplicabilitySnapshot where
  C1_thermalBath := .uncertified
  C2_classicalRegister := .uncertified
  C3_cyclicOrEntropyAccounted := .uncertified
  C4_bathIrreversible := .uncertified
  C5_noUnaccountedWorkReservoir := .uncertified
  C6_honestBitBookkeeping := .uncertified

/-- Stored bit count, condition-status snapshot, optional lower-bound expression, and optional
non-applicability class. -/
structure LandauerAuditPayload where
  discarded_bits : Nat
  c1c6_status : LandauerApplicabilitySnapshot
  lowerBoundJoules? : Option ℝ
  nonApplicabilityClass? : Option NonApplicabilityClass

/-- Extract the non-applicability class named by a witness. -/
def nonApplicabilityClassOfWitness
    {E : RecordFormationEvent} (w : NonApplicabilityWitness E) :
    NonApplicabilityClass :=
  match w with
  | .premeasurementOnly _ => .premeasurementOnly
  | .pendingRecord _ => .pendingRecord
  | .freshMemory _ => .freshMemory
  | .weakInformation _ => .weakInformation

/-- Payload produced when applicability and the physical heat law are both
available. -/
noncomputable def payloadOfApplicable
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
    (_hApp : LandauerApplicable E T)
    (_law : LandauerHeatLaw E kB T releasedHeat) :
    LandauerAuditPayload where
  discarded_bits := E.discardedBits.count
  c1c6_status := fullyCertifiedApplicabilitySnapshot
  lowerBoundJoules? := some (landauerLowerBound E kB T)
  nonApplicabilityClass? := none

/-- Payload with no lower bound, one named non-applicability class, and the all-uncertified snapshot.
The snapshot records absence of a complete package rather than six separate failure proofs. -/
def payloadOfNonApplicability
  {E : RecordFormationEvent}
    (w : NonApplicabilityWitness E) :
    LandauerAuditPayload where
  discarded_bits := E.discardedBits.count
  c1c6_status := unavailableApplicabilitySnapshot
  lowerBoundJoules? := none
  nonApplicabilityClass? := some (nonApplicabilityClassOfWitness w)

theorem payloadOfApplicable_projects_discarded_bits
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
    (hApp : LandauerApplicable E T)
    (law : LandauerHeatLaw E kB T releasedHeat) :
    (payloadOfApplicable hApp law).discarded_bits = E.discardedBits.count :=
  rfl

theorem payloadOfApplicable_projects_c1c6_status
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
    (hApp : LandauerApplicable E T)
    (law : LandauerHeatLaw E kB T releasedHeat) :
    (payloadOfApplicable hApp law).c1c6_status = fullyCertifiedApplicabilitySnapshot :=
  rfl

theorem payloadOfApplicable_projects_some_lowerBound
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
    (hApp : LandauerApplicable E T)
    (law : LandauerHeatLaw E kB T releasedHeat) :
    (payloadOfApplicable hApp law).lowerBoundJoules? =
      some (landauerLowerBound E kB T) :=
  rfl

theorem payloadOfApplicable_projects_no_reason
    {E : RecordFormationEvent} {kB T releasedHeat : ℝ}
    (hApp : LandauerApplicable E T)
    (law : LandauerHeatLaw E kB T releasedHeat) :
    (payloadOfApplicable hApp law).nonApplicabilityClass? = none :=
  rfl

theorem payloadOfNonApplicability_projects_none
    {E : RecordFormationEvent}
    (w : NonApplicabilityWitness E) :
    (payloadOfNonApplicability w).lowerBoundJoules? = none :=
  rfl

theorem payloadOfNonApplicability_projects_uncertified_status
    {E : RecordFormationEvent}
    (w : NonApplicabilityWitness E) :
    (payloadOfNonApplicability w).c1c6_status =
      unavailableApplicabilitySnapshot :=
  rfl

theorem payloadOfNonApplicability_projects_reason
    {E : RecordFormationEvent}
    (w : NonApplicabilityWitness E) :
    (payloadOfNonApplicability w).nonApplicabilityClass? =
      some (nonApplicabilityClassOfWitness w) := by
  cases w <;> rfl

end OperatorKO7.Meta.Physics.LandauerAuditPayload
