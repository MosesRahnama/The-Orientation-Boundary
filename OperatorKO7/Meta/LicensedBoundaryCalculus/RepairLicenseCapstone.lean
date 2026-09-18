import OperatorKO7.Meta.LicensedBoundaryCalculus.GuardFreezeGrammar
import OperatorKO7.Meta.LicensedBoundaryCalculus.RecoveryForwardCapabilitySeparation

/-!
# S1 dependency-coupled repair/license capstone

This is one concrete construction, not a conjunction of independent results:

raw policy dynamics + confluence predicate
→ exact failed path and `FailureObject`
→ grammar representation of the failing endpoint
→ grammar-driven least confluence repair
→ `SafeRel` completed request
→ proof-carrying forward authorization
→ typed raw refusal
→ external recovery token identifying the pre-repair history without upgrading
  that history to forward-admissible.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.FreezePositions
open OperatorKO7.Meta.DistinctionBoundary.WriteClosure

/-- Exact raw path whose endpoint violates the confluence predicate. -/
def capstoneRawPath :
    FinitePath recoveryForwardStep emptyRecoveryPolicy recDSeed :=
  .cons rawRecoveryForwardRequest.rawEdge (.refl recDSeed)

/-- First layer: a genuine first-crossing object for the raw policy path. -/
def capstoneFailureObject :
    FailureObject recoveryForwardStep ConfluentRecoveryPolicy
      emptyRecoveryPolicy recDSeed capstoneRawPath where
  lastSafe := emptyRecoveryPolicy
  firstFail := recDSeed
  sourceSafe := emptyRecoveryPolicy_confluent
  endpointFails := rawRecoveryPolicy_not_confluent
  safePrefix := .refl emptyRecoveryPolicy
  safePrefixProof := .refl emptyRecoveryPolicy_confluent
  crossing := rawRecoveryForward_boundary
  suffix := .refl recDSeed
  decomposition := rfl

/-- The failed endpoint is consumed as the predicate compiled by the grammar. -/
def capstoneFailedPolicyDecidable :
    DecidablePred capstoneFailureObject.firstFail := by
  intro c
  change Decidable (c = CtorPos.recD)
  cases c with
  | void => exact isFalse (by intro h; cases h)
  | delta => exact isFalse (by intro h; cases h)
  | integrate => exact isFalse (by intro h; cases h)
  | merge => exact isFalse (by intro h; cases h)
  | appL => exact isFalse (by intro h; cases h)
  | appR => exact isFalse (by intro h; cases h)
  | recD => exact isTrue rfl
  | eqW => exact isFalse (by intro h; cases h)

/-- Second layer: compile the actual first failing policy into closed freeze syntax. -/
def capstoneFailedGrammar : FreezePolicyGrammar :=
  @compileFreezePolicy capstoneFailureObject.firstFail capstoneFailedPolicyDecidable

/-- The grammar replay is exactly the failing policy obtained from the failure object. -/
theorem capstoneFailedGrammar_exact :
    interpretFreezePolicy capstoneFailedGrammar = capstoneFailureObject.firstFail :=
  @freezePolicy_semantic_complete capstoneFailureObject.firstFail capstoneFailedPolicyDecidable

/-- Third layer: the grammar applies the live least confluence repair to the failed policy. -/
def capstoneRepairGrammar : FreezePolicyGrammar :=
  .repair capstoneFailedGrammar

/-- The repaired policy is the semantic output of the preceding grammar node. -/
def capstoneRepairedPolicy : RecoveryPolicy :=
  interpretFreezePolicy capstoneRepairGrammar

/-- Grammar repair agrees exactly with the canonical repair of the failed endpoint. -/
theorem capstoneRepairedPolicy_eq_failureRepair :
    capstoneRepairedPolicy = confluenceRepair capstoneFailureObject.firstFail := by
  rw [capstoneRepairedPolicy, capstoneRepairGrammar, interpretFreezePolicy_repair,
    capstoneFailedGrammar_exact]

/-- In this fixture the first failing endpoint is the raw `recD` seed. -/
theorem capstoneFirstFail_eq_recDSeed :
    capstoneFailureObject.firstFail = recDSeed :=
  rfl

/-- Hence the dependency-coupled grammar output is the live canonical repaired record. -/
theorem capstoneRepairedPolicy_eq_canonical :
    capstoneRepairedPolicy = confluenceRepair recDSeed := by
  rw [capstoneRepairedPolicy_eq_failureRepair, capstoneFirstFail_eq_recDSeed]

/-- The grammar-produced repair is confluent. -/
theorem capstoneRepairedPolicy_confluent :
    ConfluentRecoveryPolicy capstoneRepairedPolicy := by
  rw [capstoneRepairedPolicy_eq_canonical]
  exact repairedRecoveryPolicy_confluent

/-- Fourth layer: build the exact forward request using the failure object's
last-safe point and the grammar repair output. -/
def capstoneRepairedRequest : ForwardRequest recoveryForwardStep where
  source := capstoneFailureObject.lastSafe
  target := capstoneRepairedPolicy
  rawEdge := by
    refine ⟨rfl, Or.inr ?_⟩
    exact capstoneRepairedPolicy_eq_canonical

/-- The request is in the universal dynamics completion. -/
theorem capstoneRepairedRequest_safe :
    SafeRel recoveryForwardStep ConfluentRecoveryPolicy
      capstoneRepairedRequest.source capstoneRepairedRequest.target :=
  ⟨capstoneRepairedRequest.rawEdge, fun _ => capstoneRepairedPolicy_confluent⟩

/-- Fifth layer: the completed request receives a non-forgeable forward license. -/
def capstoneForwardLicense :
    ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
      capstoneRepairedRequest capstoneRepairedPolicy .forward .authorize :=
  .completedDynamics capstoneRepairedRequest_safe

/-- An actual admitted path in the completed dynamics. -/
def capstoneAdmittedPath :
    FinitePath (SafeRel recoveryForwardStep ConfluentRecoveryPolicy)
      capstoneRepairedRequest.source capstoneRepairedRequest.target :=
  .cons capstoneRepairedRequest_safe (.refl capstoneRepairedRequest.target)

/-- The original failure object's exact crossing is reified as a request. -/
def capstoneRawRequest : ForwardRequest recoveryForwardStep where
  source := capstoneFailureObject.lastSafe
  target := capstoneFailureObject.firstFail
  rawEdge := capstoneFailureObject.crossing.1

/-- Sixth layer: the original boundary-crossing request receives typed refusal. -/
def capstoneRawRefusal :
    ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
      capstoneRawRequest capstoneFailureObject.firstFail .forward .refuse :=
  .boundaryRefusal capstoneFailureObject.crossing

/-- The refused raw input cannot also carry forward authorization. -/
theorem capstoneRawRequest_not_authorizable :
    ¬ Nonempty
      (ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
        capstoneRawRequest capstoneFailureObject.firstFail .forward .authorize) :=
  ProofCarryingLicense.boundary_no_authorization
    capstoneRawRequest capstoneFailureObject.crossing

/-- Seventh layer: recovery evidence points from the grammar-produced repaired
record back to the actual failed endpoint. -/
def capstoneRecoveryToken :
    ExternalRecoveryToken capstoneRepairedPolicy capstoneFailureObject.firstFail :=
  ⟨capstoneRepairedPolicy_eq_failureRepair.symm⟩

/-- Recovery really returns the pre-repair failed policy. -/
theorem capstoneRecovery_returns_failed_policy :
    ExternalRecoveryToken.recover capstoneRecoveryToken =
      capstoneFailureObject.firstFail :=
  rfl

/-- The capstone's recovery evidence does not upgrade the recovered raw history
to a forward-admission proof. -/
theorem capstone_recovery_forward_separation :
    ExternalRecoveryToken.recover capstoneRecoveryToken =
        capstoneFailureObject.firstFail ∧
    ¬ Nonempty
      (ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
        capstoneRawRequest capstoneFailureObject.firstFail .forward .authorize) :=
  ⟨capstoneRecovery_returns_failed_policy, capstoneRawRequest_not_authorizable⟩

/-- Positive admitted-path receipt: the generated forward certificate derives
confluence of its exact grammar-produced target. -/
theorem capstone_admitted_path_sound :
    Nonempty
      (ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
        capstoneRepairedRequest capstoneRepairedPolicy .forward .authorize) ∧
    ConfluentRecoveryPolicy capstoneRepairedRequest.target :=
  ⟨⟨capstoneForwardLicense⟩,
    ProofCarryingLicense.authorized_target capstoneForwardLicense
      emptyRecoveryPolicy_confluent⟩

/-- Refused-path receipt: the concrete FailureObject crossing is exactly the
boundary replayed by the refusal certificate. -/
theorem capstone_refused_path_sound :
    Nonempty
      (ProofCarryingLicense recoveryForwardStep ConfluentRecoveryPolicy
        capstoneRawRequest capstoneFailureObject.firstFail .forward .refuse) ∧
    BoundaryEdge recoveryForwardStep ConfluentRecoveryPolicy
      capstoneRawRequest.source capstoneRawRequest.target :=
  ⟨⟨capstoneRawRefusal⟩,
    ProofCarryingLicense.refused_boundary capstoneRawRefusal⟩

/-- The capstone still exposes the real many-to-one history boundary inherited
from the live write/freeze repair compiler. -/
theorem capstone_many_to_one_recovery_boundary :
    recDSeed ≠ writeClosure recDSeed ∧
      confluenceRepair recDSeed = confluenceRepair (writeClosure recDSeed) :=
  same_record_multiple_histories

end OperatorKO7.Meta.LicensedBoundaryCalculus
