import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.MinimalBoundary

/-!
# Optional committed-record capability

## Formal scope

Relation: each domain point, its mapped output, and an emitted record.
Closure: decoding an emitted record equals the committed output.
Trust: kernel-only.
Scope: boundaries with an explicit record carrier.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v r

structure RecordCapability
    {A : ARS.{u}} {B : ARS.{v}} (F : MinimalBoundary A B) where
  Record : Type r
  emit : MinimalBoundary.DomainPoint F → Record
  recordedOutput : Record → B.Carrier
  record_sound : ∀ x, recordedOutput (emit x) = F.morphism.map x

/-- Projection of the replay equality stored in `record_sound`. -/
theorem RecordCapability.output_replay
    {A : ARS.{u}} {B : ARS.{v}} {F : MinimalBoundary A B}
    (capability : RecordCapability F) (x : MinimalBoundary.DomainPoint F) :
    capability.recordedOutput (capability.emit x) = F.morphism.map x :=
  capability.record_sound x

#check @RecordCapability.output_replay
#print axioms RecordCapability.output_replay

end OperatorKO7.Meta.LicensedBoundaryCalculus
