import OperatorKO7.Meta.LicensedBoundaryCalculus.ProofCarryingLicense
import OperatorKO7.Meta.DistinctionBoundary.WriteClosure

/-!
# Recovery and forward capability separation

The live positional `confluenceRepair` is many-to-one.  This module treats a
recovery token as extra typed evidence identifying one history compatible with
a repaired record.  No cryptographic authenticity claim is derived here.
Forward admission remains a distinct `ProofCarryingLicense` capability and
cannot be manufactured from recovery evidence.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.FreezePositions
open OperatorKO7.Meta.DistinctionBoundary.WriteClosure

/-- The concrete policy carrier used by the live positional repair compiler. -/
abbrev RecoveryPolicy := CtorPos → Prop

/-- Empty starting policy for the forward/recovery separation fixture. -/
def emptyRecoveryPolicy : RecoveryPolicy :=
  fun _ => False

/-- One-step fixture: from the empty policy, request either the raw `recD` seed
or its canonical repaired policy. -/
def recoveryForwardStep (source target : RecoveryPolicy) : Prop :=
  source = emptyRecoveryPolicy ∧
    (target = recDSeed ∨ target = confluenceRepair recDSeed)

/-- Forward-license predicate is actual confluence of the live positional relation. -/
def ConfluentRecoveryPolicy (policy : RecoveryPolicy) : Prop :=
  ConfluentOnPos policy EqGuardedStep

/-- The empty starting policy is confluent. -/
theorem emptyRecoveryPolicy_confluent :
    ConfluentRecoveryPolicy emptyRecoveryPolicy := by
  exact (confluentOnPos_eqGuarded_iff emptyRecoveryPolicy).2
    ⟨(fun h => h), (fun h => False.elim h), (fun h => False.elim h)⟩

/-- The raw requested seed is the known nonconfluent boundary state. -/
theorem rawRecoveryPolicy_not_confluent :
    ¬ ConfluentRecoveryPolicy recDSeed :=
  recDSeed_not_confluent

/-- The canonical repaired record is confluent. -/
theorem repairedRecoveryPolicy_confluent :
    ConfluentRecoveryPolicy (confluenceRepair recDSeed) :=
  confluenceRepair_confluent recDSeed

/-- Exact raw forward request. -/
def rawRecoveryForwardRequest : ForwardRequest recoveryForwardStep where
  source := emptyRecoveryPolicy
  target := recDSeed
  rawEdge := ⟨rfl, Or.inl rfl⟩

/-- Exact repaired forward request. -/
def repairedRecoveryForwardRequest : ForwardRequest recoveryForwardStep where
  source := emptyRecoveryPolicy
  target := confluenceRepair recDSeed
  rawEdge := ⟨rfl, Or.inr rfl⟩

/-- The raw request carries an exact boundary crossing. -/
theorem rawRecoveryForward_boundary :
    BoundaryEdge recoveryForwardStep ConfluentRecoveryPolicy
      rawRecoveryForwardRequest.source rawRecoveryForwardRequest.target :=
  ⟨rawRecoveryForwardRequest.rawEdge,
    emptyRecoveryPolicy_confluent,
    rawRecoveryPolicy_not_confluent⟩

/-- The repaired request is safe under the same raw relation/predicate pair. -/
theorem repairedRecoveryForward_safeRel :
    SafeRel recoveryForwardStep ConfluentRecoveryPolicy
      repairedRecoveryForwardRequest.source repairedRecoveryForwardRequest.target :=
  ⟨repairedRecoveryForwardRequest.rawEdge,
    fun _ => repairedRecoveryPolicy_confluent⟩

/-- Positive forward capability for the repaired request. -/
def repairedRecoveryForwardLicense :
    ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
      repairedRecoveryForwardRequest (confluenceRepair recDSeed)
      .forward .authorize :=
  .completedDynamics repairedRecoveryForward_safeRel

/-- Typed refusal for the raw nonconfluent request. -/
def rawRecoveryForwardRefusal :
    ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
      rawRecoveryForwardRequest recDSeed .forward .refuse :=
  .boundaryRefusal rawRecoveryForward_boundary

/-- Recovery evidence is an external-history token: it identifies a particular
history and proves only that replaying the live repair compiler yields the
observed record.  It does not assert cryptographic authenticity. -/
structure ExternalRecoveryToken (record history : RecoveryPolicy) : Type where
  replay : confluenceRepair history = record

namespace ExternalRecoveryToken

/-- Recovery is possible because the additional token supplies the history index. -/
def recover {record history : RecoveryPolicy}
    (_token : ExternalRecoveryToken record history) : RecoveryPolicy :=
  history

/-- Recovery replay is generated from the typed token. -/
theorem recover_replays {record history : RecoveryPolicy}
    (token : ExternalRecoveryToken record history) :
    confluenceRepair (recover token) = record :=
  token.replay

end ExternalRecoveryToken

/-- Extra evidence selecting the raw history behind the repaired record. -/
def rawHistoryRecoveryToken :
    ExternalRecoveryToken (confluenceRepair recDSeed) recDSeed :=
  ⟨rfl⟩

/-- Extra evidence selecting the already-write-closed history behind the same record. -/
def closedHistoryRecoveryToken :
    ExternalRecoveryToken (confluenceRepair recDSeed) (writeClosure recDSeed) :=
  ⟨recDSeed_two_histories_same_repair.symm⟩

/-- The same repaired record is compatible with two genuinely different histories. -/
theorem same_record_multiple_histories :
    recDSeed ≠ writeClosure recDSeed ∧
    confluenceRepair recDSeed = confluenceRepair (writeClosure recDSeed) :=
  ⟨recDSeed_ne_writeClosure, recDSeed_two_histories_same_repair⟩

/-- No internal deterministic left inverse can reconstruct every discarded history. -/
theorem confluenceRepair_no_global_left_inverse :
    ¬ ∃ recover : RecoveryPolicy → RecoveryPolicy,
      ∀ history, recover (confluenceRepair history) = history := by
  rintro ⟨recover, hrecover⟩
  have hraw := hrecover recDSeed
  have hclosed := hrecover (writeClosure recDSeed)
  have hsame := recDSeed_two_histories_same_repair
  apply recDSeed_ne_writeClosure
  calc
    recDSeed = recover (confluenceRepair recDSeed) := hraw.symm
    _ = recover (confluenceRepair (writeClosure recDSeed)) := congrArg recover hsame
    _ = writeClosure recDSeed := hclosed

/-- Recovery evidence can identify the raw history, but it cannot turn that
nonconfluent raw request into a forward authorization. -/
theorem recovery_evidence_cannot_manufacture_forward_admission :
    ExternalRecoveryToken.recover rawHistoryRecoveryToken = recDSeed ∧
    ¬ Nonempty
      (ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
        rawRecoveryForwardRequest recDSeed .forward .authorize) := by
  constructor
  · rfl
  · exact ProofCarryingLicense.boundary_no_authorization
      rawRecoveryForwardRequest rawRecoveryForward_boundary

/-- Conversely, a valid forward license for the repaired record cannot identify
which of the two preimages was the actual history. -/
theorem forward_admission_does_not_reconstruct_history :
    Nonempty
      (ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
        repairedRecoveryForwardRequest (confluenceRepair recDSeed)
        .forward .authorize) ∧
    ∃ first second : RecoveryPolicy,
      first ≠ second ∧
      confluenceRepair first = repairedRecoveryForwardRequest.target ∧
      confluenceRepair second = repairedRecoveryForwardRequest.target := by
  refine ⟨⟨repairedRecoveryForwardLicense⟩, ?_⟩
  refine ⟨recDSeed, writeClosure recDSeed, recDSeed_ne_writeClosure, rfl, ?_⟩
  exact recDSeed_two_histories_same_repair.symm

/-- Capability-role separation is type-level: recovery-role proof-carrying
forward licenses do not exist. -/
theorem recovery_role_is_not_forward_license
    {output : RecoveryPolicy} {verdict : LicenseVerdict}
    (certificate : ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
      repairedRecoveryForwardRequest output .recovery verdict) : False :=
  ProofCarryingLicense.no_recovery_certificate certificate

end OperatorKO7.Meta.LicensedBoundaryCalculus
