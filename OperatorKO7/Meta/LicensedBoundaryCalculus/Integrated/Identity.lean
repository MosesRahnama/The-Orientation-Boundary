import OperatorKO7.Meta.LicensedBoundaryCalculus.Integrated.BoundaryTransaction

/-!
# Identity integrated transaction

## Formal Scope

The conditional identity construction preserves the supplied equalities, and the ledger specialization uses an empty event list. These are equality statements rather than optimality claims.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace IntegratedBoundaryTransaction

universe u d a

variable {A : ARS.{u}} [Fintype A.Carrier]
variable {Defect : Type d} {Action : Type a}
variable [DecidableEq Defect] [Fintype Action] [DecidableEq Action]

/-- Identity builder with no event cost. -/
def identity
    (semantics : SemanticConstructionData A Defect Action)
    (relation_iff : forall x y,
      semantics.scope.relation x y ↔ A.step x y) :
    IntegratedBoundaryTransaction A A Defect Action :=
  build
    { morphism := PartialLicensedReductionMorphism.id A
      semantics := semantics
      semantic_relation_iff := relation_iff
      eventTrace := [] }

theorem identity_morphism
    (semantics : SemanticConstructionData A Defect Action)
    (relation_iff : forall x y,
      semantics.scope.relation x y ↔ A.step x y) :
    (identity semantics relation_iff).morphism =
      PartialLicensedReductionMorphism.id A :=
  rfl

theorem identity_eventTrace
    (semantics : SemanticConstructionData A Defect Action)
    (relation_iff : forall x y,
      semantics.scope.relation x y ↔ A.step x y) :
    (identity semantics relation_iff).eventTrace = [] :=
  rfl

theorem identity_ledger
    (semantics : SemanticConstructionData A Defect Action)
    (relation_iff : forall x y,
      semantics.scope.relation x y ↔ A.step x y) :
    (identity semantics relation_iff).ledger = 0 :=
  rfl

#check @identity
#check @identity_morphism
#check @identity_ledger
#print axioms identity_morphism
#print axioms identity_eventTrace
#print axioms identity_ledger

end IntegratedBoundaryTransaction
end OperatorKO7.Meta.LicensedBoundaryCalculus
