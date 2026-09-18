import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.DomainRestrictedARS

/-!
# Admitted-edge reduction systems

After restricting the carrier to the domain, the second canonical factor keeps
the edges admitted by the license. The state carrier and state map are
unchanged; only the relation is restricted.

## Formal scope

Relation: admitted source edges on the domain subtype.
Closure: one step; path closure is inherited from `ARS`.
Trust: kernel-only.
Scope: universal edge restriction and the residual state map.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v

variable {A : ARS.{u}} {B : ARS.{v}}

/-- The domain carrier equipped with the admitted source relation. -/
def admittedEdgeARS (F : PartialLicensedReductionMorphism A B) : ARS.{u} where
  Carrier := DomainCarrier F
  step := fun x y => F.admitted x.val y.val
  scope := { A.scope with admission := .guarded }

/-- Canonical edge restriction from raw domain dynamics to admitted dynamics. -/
def edgeRestrictionOnDomain (F : PartialLicensedReductionMorphism A B) :
    LicensedReductionMorphism F.domainRestrictedARS F.admittedEdgeARS where
  admitted := fun x y => F.admitted x.val y.val
  admitted_sub_raw := fun h => F.admitted_sub_raw h
  map := fun x => x
  map_step := fun h => h

/-- Residual state map after domain and edge restriction. -/
def admittedStateMap (F : PartialLicensedReductionMorphism A B) :
    LicensedReductionMorphism F.admittedEdgeARS B where
  admitted := F.admittedEdgeARS.step
  admitted_sub_raw := fun h => h
  map := F.map
  map_step := by
    intro x y h
    convert F.map_step h

/-- Membership in the edge factor's admitted relation is definitionally equivalent to the
original admitted relation on the underlying values. -/
theorem edgeRestrictionOnDomain_admitted_iff
    (F : PartialLicensedReductionMorphism A B) (x y : DomainCarrier F) :
    F.edgeRestrictionOnDomain.admitted x y <-> F.admitted x.val y.val :=
  Iff.rfl

/-- The residual state map is the original partial map on every domain point. -/
theorem admittedStateMap_map_eq
    (F : PartialLicensedReductionMorphism A B) (x : DomainCarrier F) :
    F.admittedStateMap.map x = F.map x :=
  rfl

/-- The pure edge-rejection fixture has no admitted edge after restriction. -/
theorem pureEdgeRejection_admittedEdge_empty_fixture
    (x y : DomainCarrier pureEdgeRejection_fixture) :
    Not (pureEdgeRejection_fixture.admittedEdgeARS.step x y) := by
  intro h
  exact h

#check @admittedEdgeARS
#check @edgeRestrictionOnDomain
#check @admittedStateMap
#check @edgeRestrictionOnDomain_admitted_iff
#check @admittedStateMap_map_eq
#check pureEdgeRejection_admittedEdge_empty_fixture
#print axioms admittedEdgeARS
#print axioms edgeRestrictionOnDomain
#print axioms admittedStateMap
#print axioms edgeRestrictionOnDomain_admitted_iff
#print axioms admittedStateMap_map_eq
#print axioms pureEdgeRejection_admittedEdge_empty_fixture

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
