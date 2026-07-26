import OperatorKO7.Meta.LicensedBoundaryCalculus.Integrated.Identity

/-!
This module composes integrated records under caller-supplied semantic-capability and finiteness
data. Its ledger laws are structural list append and associativity results.











-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v w d a d₁ a₁ d₂ a₂

/-- Data record whose requirements are the fields displayed below.
-/
structure CompositeSemanticCapability
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C)
    (Defect : Type d) (Action : Type a)
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action] where
  semantics : SemanticConstructionData A Defect Action
  relation_iff : forall x y,
    semantics.scope.relation x y ↔
      (PartialLicensedReductionMorphism.comp F G).admitted x y

namespace IntegratedBoundaryTransaction

/-- Definition with formal content given by the displayed type and body.
-/
def comp
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CompositeSemanticCapability
      first.morphism second.morphism Defect Action) :
    IntegratedBoundaryTransaction A C Defect Action :=
  build
    { morphism :=
        PartialLicensedReductionMorphism.comp first.morphism second.morphism
      semantics := semantic.semantics
      semantic_relation_iff := semantic.relation_iff
      eventTrace := first.eventTrace ++ second.eventTrace }

theorem comp_morphism
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CompositeSemanticCapability
      first.morphism second.morphism Defect Action) :
    (comp first second semantic).morphism =
      PartialLicensedReductionMorphism.comp first.morphism second.morphism :=
  rfl

theorem comp_eventTrace
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CompositeSemanticCapability
      first.morphism second.morphism Defect Action) :
    (comp first second semantic).eventTrace =
      first.eventTrace ++ second.eventTrace :=
  rfl

/-- The displayed proposition follows from the stated hypotheses. -/
theorem comp_ledger
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CompositeSemanticCapability
      first.morphism second.morphism Defect Action) :
    (comp first second semantic).ledger = first.ledger + second.ledger := by
  change countEvents (first.eventTrace ++ second.eventTrace) =
    countEvents first.eventTrace + countEvents second.eventTrace
  exact countEvents_append first.eventTrace second.eventTrace

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem comp_semanticProfile_eq_derived
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CompositeSemanticCapability
      first.morphism second.morphism Defect Action) :
    (comp first second semantic).semanticProfile =
      OperatorKO7.Meta.LicensedBoundaryCalculus.semanticProfile
        semantic.semantics :=
  rfl

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem composition_backbone_assoc
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}} {D : ARS}
    [Fintype A.Carrier] [Fintype B.Carrier]
    [Fintype C.Carrier] [Fintype D.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (third : IntegratedBoundaryTransaction C D Defect Action) :
    PartialLicensedReductionMorphism.comp
        (PartialLicensedReductionMorphism.comp first.morphism second.morphism)
        third.morphism =
      PartialLicensedReductionMorphism.comp first.morphism
        (PartialLicensedReductionMorphism.comp second.morphism third.morphism) ∧
    (first.eventTrace ++ second.eventTrace) ++ third.eventTrace =
      first.eventTrace ++ (second.eventTrace ++ third.eventTrace) := by
  exact
    ⟨PartialLicensedReductionMorphism.comp_assoc
        first.morphism second.morphism third.morphism,
      List.append_assoc _ _ _⟩

#check @comp
#check @comp_ledger
#check @comp_semanticProfile_eq_derived
#check @composition_backbone_assoc
#print axioms comp_morphism
#print axioms comp_eventTrace
#print axioms comp_ledger
#print axioms comp_semanticProfile_eq_derived
#print axioms composition_backbone_assoc

end IntegratedBoundaryTransaction
end OperatorKO7.Meta.LicensedBoundaryCalculus
