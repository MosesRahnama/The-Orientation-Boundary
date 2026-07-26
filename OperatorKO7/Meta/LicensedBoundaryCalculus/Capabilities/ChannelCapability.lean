import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.MinimalBoundary

/-!
# Optional channel capability

`ChannelCapability` adds an option-valued channel to a minimal boundary. On the partial morphism's
domain, the channel returns the mapped value. Outside that domain, it returns `none`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v

structure ChannelCapability
    {A : ARS.{u}} {B : ARS.{v}} (F : MinimalBoundary A B) where
  send : A.Carrier → Option B.Carrier
  sends_domain : ∀ x (hx : F.morphism.domain x),
    send x = some (F.morphism.map ⟨x, hx⟩)
  silent_outside : ∀ x, ¬ F.morphism.domain x → send x = none

theorem ChannelCapability.send_eq_map
    {A : ARS.{u}} {B : ARS.{v}} {F : MinimalBoundary A B}
    (capability : ChannelCapability F) (x : A.Carrier)
    (hx : F.morphism.domain x) :
    capability.send x = some (F.morphism.map ⟨x, hx⟩) :=
  capability.sends_domain x hx

#check @ChannelCapability.send_eq_map
#print axioms ChannelCapability.send_eq_map

end OperatorKO7.Meta.LicensedBoundaryCalculus
