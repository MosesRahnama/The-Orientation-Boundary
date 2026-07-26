import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.MinimalBoundary
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Optional thermal-erasure capability

`ThermalErasureCapability` packages physical labels, numerical fields, and an
explicit proof of the stated lower bound. The projection theorem returns that
stored `landauerFloor` field. It does not derive the inequality from the other
fields of the record.

## Formal scope

Relation: domain points and their named physical erasure implementation.
Closure: one caller-supplied lower-bound proof per domain point.
Trust: kernel-only real arithmetic over supplied physical hypotheses.
Scope: the supplied capability record, not an independent physical derivation.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v

structure ThermalErasureCapability
    {A : ARS.{u}} {B : ARS.{v}} (F : MinimalBoundary A B) where
  physicalImplementation : Prop
  implementationWitness : physicalImplementation
  discardedInformationBits : MinimalBoundary.DomainPoint F → Real
  discardedInformation_nonneg : ∀ x, 0 ≤ discardedInformationBits x
  boltzmannConstant : Real
  boltzmannConstant_pos : 0 < boltzmannConstant
  temperature : Real
  temperature_nonneg : 0 ≤ temperature
  energyCost : MinimalBoundary.DomainPoint F → Real
  energyCalibration : MinimalBoundary.DomainPoint F → Real → Prop
  calibrationHolds : ∀ x, energyCalibration x (energyCost x)
  energyCost_nonneg : ∀ x, 0 ≤ energyCost x
  landauerFloor : ∀ x,
    boltzmannConstant * temperature * Real.log 2 *
        discardedInformationBits x ≤ energyCost x

/-- Projects the lower-bound proof stored in `capability.landauerFloor`. -/
theorem ThermalErasureCapability.landauer_floor
    {A : ARS.{u}} {B : ARS.{v}} {F : MinimalBoundary A B}
    (capability : ThermalErasureCapability F)
    (x : MinimalBoundary.DomainPoint F) :
    capability.boltzmannConstant * capability.temperature * Real.log 2 *
        capability.discardedInformationBits x ≤ capability.energyCost x :=
  capability.landauerFloor x

#check @ThermalErasureCapability.landauer_floor
#print axioms ThermalErasureCapability.landauer_floor

end OperatorKO7.Meta.LicensedBoundaryCalculus
