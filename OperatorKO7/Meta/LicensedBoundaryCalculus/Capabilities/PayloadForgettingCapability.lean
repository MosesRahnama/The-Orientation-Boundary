import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.MinimalBoundary

/-!
This module defines a capability whose `no_recovery` field rules out a
deterministic payload-recovery map on admitted domain points. The theorem is
the direct projection of that stored proposition; it does not derive
non-recoverability from the minimal boundary alone.

-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v p

structure PayloadForgettingCapability
    {A : ARS.{u}} {B : ARS.{v}} (F : MinimalBoundary A B) where
  Payload : Type p
  payload : A.Carrier → Payload
  no_recovery : ¬ ∃ recover : B.Carrier → Payload,
    ∀ x : MinimalBoundary.DomainPoint F,
      recover (F.morphism.map x) = payload x.1

theorem PayloadForgettingCapability.forgetting
    {A : ARS.{u}} {B : ARS.{v}} {F : MinimalBoundary A B}
    (capability : PayloadForgettingCapability F) :
    ¬ ∃ recover : B.Carrier → capability.Payload,
      ∀ x : MinimalBoundary.DomainPoint F,
        recover (F.morphism.map x) = capability.payload x.1 :=
  capability.no_recovery

#check @PayloadForgettingCapability.forgetting
#print axioms PayloadForgettingCapability.forgetting

end OperatorKO7.Meta.LicensedBoundaryCalculus
