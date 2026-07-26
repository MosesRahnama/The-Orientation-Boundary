import OperatorKO7.Meta.LicensedBoundaryCalculus.Capabilities.MinimalBoundary

/-!
# Licensed Boundary Calculus structural API

This dependency-light entry point exposes `MinimalBoundary`, whose carrier is
a partial licensed-reduction morphism, together with the structural identity
fixture below.

## Formal scope

Relation: the admitted relation of a partial licensed-reduction morphism.
Closure: identity and composition of the minimal carrier.
Trust: kernel-only.
Scope: structural Licensed Boundary Calculus fields and operations.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.API.Structural

open OperatorKO7.Meta.LicensedBoundaryCalculus

universe u

abbrev Boundary := MinimalBoundary

/-- Chosen-data fixture showing that every ARS has a canonical structural
identity boundary. -/
def identityBoundary_fixture (A : ARS.{u}) : Boundary A A :=
  MinimalBoundary.id A

theorem identityBoundary_fixture_total (A : ARS.{u}) (x : A.Carrier) :
    (identityBoundary_fixture A).morphism.domain x :=
  trivial

#check @identityBoundary_fixture_total
#print axioms identityBoundary_fixture_total

end OperatorKO7.Meta.LicensedBoundaryCalculus.API.Structural
