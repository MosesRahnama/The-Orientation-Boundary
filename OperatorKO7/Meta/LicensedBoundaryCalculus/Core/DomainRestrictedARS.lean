import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.RestrictionLaws

/-!
# Domain-restricted reduction systems

The first canonical factor of a partial licensed morphism replaces the source
carrier by the subtype on which the morphism is defined.  This construction is
available for every partial morphism and requires no inhabitance assumption.

## Audit slots

Relation: the raw source relation restricted to domain-certified endpoints.
Closure: one step; path closure is inherited from `ARS`.
Trust: kernel-only.
Scope: universal source-domain restriction and its canonical partial map.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v

variable {A : ARS.{u}} {B : ARS.{v}}

/-- Carrier of states on which a partial morphism is defined. -/
abbrev DomainCarrier (F : PartialLicensedReductionMorphism A B) :=
  {x // F.domain x}

/-- Raw source dynamics restricted to domain-certified states. -/
def domainRestrictedARS (F : PartialLicensedReductionMorphism A B) : ARS.{u} where
  Carrier := DomainCarrier F
  step := fun x y => A.step x.val y.val
  scope := A.scope

/-- Canonical partial projection from the source into its domain restriction. -/
def domainRestriction (F : PartialLicensedReductionMorphism A B) :
    PartialLicensedReductionMorphism A F.domainRestrictedARS where
  domain := F.domain
  admitted := fun x y => A.step x y ∧ F.domain x ∧ F.domain y
  admitted_sub_raw := fun h => h.1
  admitted_source_domain := fun h => h.2.1
  admitted_target_domain := fun h => h.2.2
  map := fun x => x
  map_step := fun h => h.1

/-- Domain restriction is defined exactly on the original domain. -/
theorem domainRestriction_domain_iff
    (F : PartialLicensedReductionMorphism A B) (x : A.Carrier) :
    F.domainRestriction.domain x <-> F.domain x :=
  Iff.rfl

/-- The canonical domain map preserves the source state exactly. -/
theorem domainRestriction_map_eq
    (F : PartialLicensedReductionMorphism A B) (x : DomainCarrier F) :
    F.domainRestriction.map x = x :=
  rfl

/-- The domain carrier is empty exactly when the domain predicate is empty. -/
theorem domainCarrier_nonempty_iff
    (F : PartialLicensedReductionMorphism A B) :
    Nonempty (DomainCarrier F) <-> exists x, F.domain x := by
  constructor
  · rintro ⟨x⟩
    exact ⟨x.val, x.property⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩

/-- The partial-chain domain restriction has one canonical source point. -/
theorem partialChain_domainRestriction_fixture :
    partialChain_fixture.domainRestriction.map
      ⟨ChainNode.source, rfl⟩ = ⟨ChainNode.source, rfl⟩ :=
  rfl

#check @domainRestrictedARS
#check @domainRestriction
#check @domainRestriction_domain_iff
#check @domainRestriction_map_eq
#check @domainCarrier_nonempty_iff
#check partialChain_domainRestriction_fixture
#print axioms domainRestrictedARS
#print axioms domainRestriction
#print axioms domainRestriction_domain_iff
#print axioms domainRestriction_map_eq
#print axioms domainCarrier_nonempty_iff
#print axioms partialChain_domainRestriction_fixture

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
