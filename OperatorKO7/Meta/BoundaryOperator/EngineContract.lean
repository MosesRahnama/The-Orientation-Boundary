import OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness
import OperatorKO7.Meta.BoundaryOperator.LandauerBridge
import OperatorKO7.Meta.Physics.LandauerAuditPayload

/-!
# Boundary-operator contract record

`EngineContract` stores a boundary operator and optional typed-refusal and Landauer-audit payloads.
The typed-refusal constructor requires a classifier and its support proof. The applicable Landauer
constructor is noncomputable and requires a boundary-to-record link, an applicability witness, and
a heat-law witness. The alternative Landauer constructor requires a non-applicability witness.
-/

namespace OperatorKO7.Meta.BoundaryOperator

open OperatorKO7.MetaHalt.Predicate
open OperatorKO7.Meta.Physics.RecordFormation
open OperatorKO7.Meta.Physics.LandauerHeatBound
open OperatorKO7.Meta.Physics.LandauerAuditPayload

universe u v

/-- A typed-refusal classifier together with its support proof. -/
structure TypedRefusalRuntimeStatus (Y : Type v) where
  classifier : TypedRefusalClassifier Y
  support : ∀ y, classifier.classify y ∈ refusalTypeSupport

/-- Boundary operator with optional typed-refusal and Landauer-audit payloads. -/
structure EngineContract (X : Type u) (Y : Type v) where
  boundaryOperator : BoundaryOperator X Y
  refusalStatus? : Option (TypedRefusalRuntimeStatus Y)
  landauerAuditPayload? : Option LandauerAuditPayload

/-- Contract containing a boundary operator and empty optional payloads. -/
def baseContract
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) : EngineContract X Y where
  boundaryOperator := B
  refusalStatus? := none
  landauerAuditPayload? := none

/-- Add a typed-refusal runtime package to a boundary operator. -/
def withTypedRefusalStatus
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y)
    (C : TypedRefusalClassifier Y)
    (hSupport : ∀ y, C.classify y ∈ refusalTypeSupport) :
    EngineContract X Y where
  boundaryOperator := B
  refusalStatus? := some ⟨C, hSupport⟩
  landauerAuditPayload? := none

/-- Contract using the supplied `TypedOutput` classifier and support theorem. -/
def withTypedOutputStatus
    {X : Type u}
    (B : BoundaryOperator X TypedOutput) :
    EngineContract X TypedOutput :=
  withTypedRefusalStatus B typedOutputClassifier typedOutputToRefusalType_mem_support

/-- If a contract exposes a typed-refusal status, the advertised classifier lands in the refusal support. -/
theorem EngineContract.refusal_support
    {X : Type u} {Y : Type v}
    {C : EngineContract X Y}
    {status : TypedRefusalRuntimeStatus Y}
    (_hStatus : C.refusalStatus? = some status)
    (y : Y) :
    status.classifier.classify y ∈ refusalTypeSupport :=
  status.support y

/-- Constructor-level projection for the generic typed-refusal contract surface. -/
theorem withTypedRefusalStatus_projects_support
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y)
    (C : TypedRefusalClassifier Y)
    (hSupport : ∀ y, C.classify y ∈ refusalTypeSupport)
    (y : Y) :
    ∃ status : TypedRefusalRuntimeStatus Y,
      (withTypedRefusalStatus B C hSupport).refusalStatus? = some status ∧
      status.classifier.classify y ∈ refusalTypeSupport := by
  refine ⟨⟨C, hSupport⟩, rfl, ?_⟩
  exact hSupport y

/-- Constructor-level projection for the canonical `TypedOutput` runtime package. -/
theorem withTypedOutputStatus_projects_support
    {X : Type u}
    (B : BoundaryOperator X TypedOutput)
    (y : TypedOutput) :
    ∃ status : TypedRefusalRuntimeStatus TypedOutput,
      (withTypedOutputStatus B).refusalStatus? = some status ∧
      status.classifier.classify y ∈ refusalTypeSupport := by
  simpa [withTypedOutputStatus] using
    withTypedRefusalStatus_projects_support B typedOutputClassifier
      typedOutputToRefusalType_mem_support y

/-- Attach a Landauer payload from an explicit record-formation link, applicability witness, and
heat-law witness. -/
noncomputable def withApplicableLandauerAudit
    {X : Type u} {Y : Type v}
    (C : EngineContract X Y)
    (L : BoundaryRecordFormationLink C.boundaryOperator)
    (hApp : LandauerApplicable L.event C.boundaryOperator.temperature)
    (hLaw : LandauerHeatLaw L.event C.boundaryOperator.kB C.boundaryOperator.temperature L.releasedHeat) :
    EngineContract X Y where
  boundaryOperator := C.boundaryOperator
  refusalStatus? := C.refusalStatus?
  landauerAuditPayload? := some (payloadOfApplicable hApp hLaw)

/-- Attach a Landauer payload whose lower-bound field is `none`, using a non-applicability witness. -/
def withNonApplicableLandauerAudit
    {X : Type u} {Y : Type v}
    (C : EngineContract X Y)
    (L : BoundaryRecordFormationLink C.boundaryOperator)
    (w : NonApplicabilityWitness L.event) :
    EngineContract X Y where
  boundaryOperator := C.boundaryOperator
  refusalStatus? := C.refusalStatus?
  landauerAuditPayload? :=
    some (payloadOfNonApplicability w)

/-- Project the lower bound stored by `withApplicableLandauerAudit`. -/
theorem withApplicableLandauerAudit_projects_some_lowerBound
    {X : Type u} {Y : Type v}
    (C : EngineContract X Y)
    (L : BoundaryRecordFormationLink C.boundaryOperator)
    (hApp : LandauerApplicable L.event C.boundaryOperator.temperature)
    (hLaw : LandauerHeatLaw L.event C.boundaryOperator.kB C.boundaryOperator.temperature L.releasedHeat) :
    ∃ payload : LandauerAuditPayload,
      (withApplicableLandauerAudit C L hApp hLaw).landauerAuditPayload? = some payload ∧
      payload.lowerBoundJoules? =
        some (landauerLowerBound L.event C.boundaryOperator.kB C.boundaryOperator.temperature) := by
  refine ⟨payloadOfApplicable hApp hLaw, rfl, ?_⟩
  exact payloadOfApplicable_projects_some_lowerBound hApp hLaw

/-- Project the `none` lower-bound field stored by `withNonApplicableLandauerAudit`. -/
theorem withNonApplicableLandauerAudit_projects_none_lowerBound
    {X : Type u} {Y : Type v}
    (C : EngineContract X Y)
    (L : BoundaryRecordFormationLink C.boundaryOperator)
    (w : NonApplicabilityWitness L.event) :
    ∃ payload : LandauerAuditPayload,
      (withNonApplicableLandauerAudit C L w).landauerAuditPayload? = some payload ∧
      payload.lowerBoundJoules? = none := by
  refine ⟨payloadOfNonApplicability w, rfl, ?_⟩
  exact payloadOfNonApplicability_projects_none w

/-- Derive cost domination from the explicit link, applicability witness, and heat law. -/
theorem boundary_cost_dominates_contract_lowerBound
    {X : Type u} {Y : Type v}
    (C : EngineContract X Y)
    (L : BoundaryRecordFormationLink C.boundaryOperator)
    (hApp : LandauerApplicable L.event C.boundaryOperator.temperature)
    (hLaw : LandauerHeatLaw L.event C.boundaryOperator.kB C.boundaryOperator.temperature L.releasedHeat) :
    landauerLowerBound L.event C.boundaryOperator.kB C.boundaryOperator.temperature ≤
      C.boundaryOperator.landauer_cost L.point.1 L.point.2 :=
  boundaryLandauerCostDominatesPerBitFloor L hApp hLaw

end OperatorKO7.Meta.BoundaryOperator
