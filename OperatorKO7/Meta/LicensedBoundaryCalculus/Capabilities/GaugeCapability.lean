import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.MinimalBoundary

/-!
# Optional gauge capability

Gauge covariance is additional structure on a minimal boundary, not a field of
the minimal carrier.

The capability supplies a group, source and target actions, their action laws, preservation of the
partial morphism's domain, and covariance of its map.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v g

structure GaugeCapability
    {A : ARS.{u}} {B : ARS.{v}} (F : MinimalBoundary A B) where
  Gauge : Type g
  gaugeGroup : Group Gauge
  actSource : Gauge → A.Carrier → A.Carrier
  actTarget : Gauge → B.Carrier → B.Carrier
  source_one : ∀ x, actSource 1 x = x
  source_mul : ∀ g h x, actSource (g * h) x = actSource g (actSource h x)
  target_one : ∀ y, actTarget 1 y = y
  target_mul : ∀ g h y, actTarget (g * h) y = actTarget g (actTarget h y)
  domain_preserved : ∀ g x, F.morphism.domain x →
    F.morphism.domain (actSource g x)
  map_covariant : ∀ g x (hx : F.morphism.domain x),
    F.morphism.map ⟨actSource g x, domain_preserved g x hx⟩ =
      actTarget g (F.morphism.map ⟨x, hx⟩)

attribute [instance] GaugeCapability.gaugeGroup

theorem GaugeCapability.covariant
    {A : ARS.{u}} {B : ARS.{v}} {F : MinimalBoundary A B}
    (capability : GaugeCapability F) (g : capability.Gauge)
    (x : A.Carrier) (hx : F.morphism.domain x) :
    F.morphism.map
        ⟨capability.actSource g x, capability.domain_preserved g x hx⟩ =
      capability.actTarget g (F.morphism.map ⟨x, hx⟩) :=
  capability.map_covariant g x hx

#check @GaugeCapability.covariant
#print axioms GaugeCapability.covariant

end OperatorKO7.Meta.LicensedBoundaryCalculus
