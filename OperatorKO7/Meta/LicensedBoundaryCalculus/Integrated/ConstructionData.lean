import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.SemanticProfile
import OperatorKO7.Meta.LicensedBoundaryCalculus.Accounting.EventLedger

/-!
# Integrated boundary construction data

`BoundaryConstructionData` combines a partial licensed reduction morphism, semantic construction
data, a pointwise equivalence between the semantic scope relation and the morphism's admitted
relation, and an event trace. The theorem below projects the stored pointwise equivalence.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v d a

/-- Data package used to construct an integrated boundary transaction. -/
structure BoundaryConstructionData
    (A : ARS.{u}) (B : ARS.{v}) [Fintype A.Carrier] [Fintype B.Carrier]
    (Defect : Type d) (Action : Type a)
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action] where
  morphism : PartialLicensedReductionMorphism A B
  semantics : SemanticConstructionData A Defect Action
  semantic_relation_iff : forall x y,
    semantics.scope.relation x y ↔ morphism.admitted x y
  eventTrace : EventTrace

/-- Project the stored equivalence between the semantic scope relation and admitted relation. -/
theorem BoundaryConstructionData.scope_relation_iff
    {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier] [Fintype B.Carrier]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (data : BoundaryConstructionData A B Defect Action) (x y : A.Carrier) :
    data.semantics.scope.relation x y ↔ data.morphism.admitted x y :=
  data.semantic_relation_iff x y

#check @BoundaryConstructionData
#check @BoundaryConstructionData.scope_relation_iff
#print axioms BoundaryConstructionData.scope_relation_iff

end OperatorKO7.Meta.LicensedBoundaryCalculus
