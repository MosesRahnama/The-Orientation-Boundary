import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.PartialComposition

/-!
# Minimal boundary carrier

## Formal Scope

The category contains one morphism; identity and composition follow definitionally. Additional gauge, transport, and reconstruction structures are outside this minimal carrier.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v w

structure MinimalBoundary (A : ARS.{u}) (B : ARS.{v}) where
  morphism : PartialLicensedReductionMorphism A B

namespace MinimalBoundary

def id (A : ARS.{u}) : MinimalBoundary A A :=
  ⟨PartialLicensedReductionMorphism.id A⟩

def comp {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : MinimalBoundary A B) (G : MinimalBoundary B C) :
    MinimalBoundary A C :=
  ⟨PartialLicensedReductionMorphism.comp F.morphism G.morphism⟩

abbrev DomainPoint {A : ARS.{u}} {B : ARS.{v}}
    (F : MinimalBoundary A B) :=
  {x : A.Carrier // F.morphism.domain x}

theorem id_comp {A : ARS.{u}} {B : ARS.{v}}
    (F : MinimalBoundary A B) : comp (id A) F = F := by
  cases F
  simp [comp, id, PartialLicensedReductionMorphism.id_comp]

theorem comp_id {A : ARS.{u}} {B : ARS.{v}}
    (F : MinimalBoundary A B) : comp F (id B) = F := by
  cases F
  simp [comp, id, PartialLicensedReductionMorphism.comp_id]

theorem comp_assoc {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}} {D : ARS}
    (F : MinimalBoundary A B) (G : MinimalBoundary B C)
    (H : MinimalBoundary C D) :
    comp (comp F G) H = comp F (comp G H) := by
  cases F
  cases G
  cases H
  simp [comp, PartialLicensedReductionMorphism.comp_assoc]

#check @id_comp
#check @comp_id
#check @comp_assoc
#print axioms id_comp
#print axioms comp_id
#print axioms comp_assoc

end MinimalBoundary
end OperatorKO7.Meta.LicensedBoundaryCalculus
