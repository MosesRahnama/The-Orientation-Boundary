import OperatorKO7.Meta.LicensedBoundaryCalculus.Integrated.ConstructionData
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.StructuralProfile

/-!
# Integrated quantitative boundary transaction

An integrated transaction wraps one construction datum.  Structural profile,
semantic profile, and event ledger are functions of that datum, so an
incoherent morphism/profile/ledger tuple is not constructible through this API.

## Audit slots

Relation: the construction's coherent admitted and semantic relations.
Closure: finite structural/semantic computation and finite trace counting.
Trust: kernel-only, with classical finite enumeration.
Scope: integrated finite quantitative LBC transactions.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v d a

/-- The production object contains construction data only. -/
structure IntegratedBoundaryTransaction
    (A : ARS.{u}) (B : ARS.{v}) [Fintype A.Carrier] [Fintype B.Carrier]
    (Defect : Type d) (Action : Type a)
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action] where
  construction : BoundaryConstructionData A B Defect Action

namespace IntegratedBoundaryTransaction

variable {A : ARS.{u}} {B : ARS.{v}}
variable [Fintype A.Carrier] [Fintype B.Carrier]
variable {Defect : Type d} {Action : Type a}
variable [DecidableEq Defect] [Fintype Action] [DecidableEq Action]

/-- Public builder; it accepts no profile or ledger. -/
def build (data : BoundaryConstructionData A B Defect Action) :
    IntegratedBoundaryTransaction A B Defect Action :=
  ⟨data⟩

def morphism (transaction : IntegratedBoundaryTransaction A B Defect Action) :
    PartialLicensedReductionMorphism A B :=
  transaction.construction.morphism

def semanticData
    (transaction : IntegratedBoundaryTransaction A B Defect Action) :
    SemanticConstructionData A Defect Action :=
  transaction.construction.semantics

def eventTrace (transaction : IntegratedBoundaryTransaction A B Defect Action) :
    EventTrace :=
  transaction.construction.eventTrace

noncomputable def structuralProfile
    (transaction : IntegratedBoundaryTransaction A B Defect Action) :
    PartialLicensedReductionMorphism.StructuralProfile :=
  PartialLicensedReductionMorphism.structuralProfile transaction.morphism

noncomputable def semanticProfile
    (transaction : IntegratedBoundaryTransaction A B Defect Action) :
    SemanticProfile :=
  OperatorKO7.Meta.LicensedBoundaryCalculus.semanticProfile
    transaction.semanticData

noncomputable def ledger
    (transaction : IntegratedBoundaryTransaction A B Defect Action) :
    EventLedger :=
  countEvents transaction.eventTrace

theorem semantic_relation_iff
    (transaction : IntegratedBoundaryTransaction A B Defect Action)
    (x y : A.Carrier) :
    transaction.semanticData.scope.relation x y ↔
      transaction.morphism.admitted x y :=
  transaction.construction.semantic_relation_iff x y

/-- All three quantitative outputs are derivations from the one construction. -/
theorem outputs_eq_derived
    (transaction : IntegratedBoundaryTransaction A B Defect Action) :
    transaction.structuralProfile =
        PartialLicensedReductionMorphism.structuralProfile transaction.morphism ∧
      transaction.semanticProfile =
        OperatorKO7.Meta.LicensedBoundaryCalculus.semanticProfile
          transaction.semanticData ∧
      transaction.ledger = countEvents transaction.eventTrace :=
  ⟨rfl, rfl, rfl⟩

#check @build
#check @outputs_eq_derived
#check @semantic_relation_iff
#print axioms outputs_eq_derived
#print axioms semantic_relation_iff

end IntegratedBoundaryTransaction
end OperatorKO7.Meta.LicensedBoundaryCalculus
