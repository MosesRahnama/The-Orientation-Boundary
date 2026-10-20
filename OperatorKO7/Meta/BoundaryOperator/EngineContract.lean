import OperatorKO7.Meta.BoundaryOperator.TypedRefusalCompleteness

/-!
# Boundary-operator contract record

`EngineContract` stores a boundary operator and an optional typed-refusal payload.
The typed-refusal constructor requires a classifier and its support proof. The audit-payload
constructor is noncomputable and requires a boundary-to-record link, an applicability witness, and
layer lives in the companion module `EngineContractLandauer`.
-/

namespace OperatorKO7.Meta.BoundaryOperator

open OperatorKO7.MetaHalt.Predicate

universe u v

/-- A typed-refusal classifier together with its support proof. -/
structure TypedRefusalRuntimeStatus (Y : Type v) where
  classifier : TypedRefusalClassifier Y
  support : ∀ y, classifier.classify y ∈ refusalTypeSupport

/-- Boundary operator with an optional typed-refusal payload. -/
structure EngineContract (X : Type u) (Y : Type v) where
  boundaryOperator : BoundaryOperator X Y
  refusalStatus? : Option (TypedRefusalRuntimeStatus Y)

/-- Contract containing a boundary operator and empty optional payloads. -/
def baseContract
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y) : EngineContract X Y where
  boundaryOperator := B
  refusalStatus? := none

/-- Add a typed-refusal runtime package to a boundary operator. -/
def withTypedRefusalStatus
    {X : Type u} {Y : Type v}
    (B : BoundaryOperator X Y)
    (C : TypedRefusalClassifier Y)
    (hSupport : ∀ y, C.classify y ∈ refusalTypeSupport) :
    EngineContract X Y where
  boundaryOperator := B
  refusalStatus? := some ⟨C, hSupport⟩

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

end OperatorKO7.Meta.BoundaryOperator
