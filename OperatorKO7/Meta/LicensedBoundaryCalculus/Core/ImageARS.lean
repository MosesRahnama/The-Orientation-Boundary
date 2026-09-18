import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.KernelQuotientARS

/-!
# Image reduction systems

## Formal Scope

The construction is Set.range factorization with inclusion and surjectivity. No universal property or uniqueness theorem for the range object is claimed.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v

variable {A : ARS.{u}} {B : ARS.{v}}

/-- Carrier of target states reached by the domain-defined state map. -/
abbrev ImageCarrier (F : PartialLicensedReductionMorphism A B) :=
  Set.range F.map

/-- Target dynamics restricted to endpoints in the state-map range. -/
def imageARS (F : PartialLicensedReductionMorphism A B) : ARS.{v} where
  Carrier := ImageCarrier F
  step := fun x y => B.step x.val y.val
  scope := { B.scope with layer := .projected }

/-- The state map with codomain restricted to its specified range. -/
def imageMap (F : PartialLicensedReductionMorphism A B) :
    LicensedReductionMorphism F.admittedEdgeARS F.imageARS where
  admitted := F.admittedEdgeARS.step
  admitted_sub_raw := fun h => h
  map := fun x => ⟨F.map x, ⟨x, rfl⟩⟩
  map_step := by
    intro x y h
    change B.step (F.map x) (F.map y)
    convert F.map_step h

/-- Inclusion of the specified range into the full target. -/
def imageInclusion (F : PartialLicensedReductionMorphism A B) :
    LicensedReductionMorphism F.imageARS B where
  admitted := F.imageARS.step
  admitted_sub_raw := fun h => h
  map := Subtype.val
  map_step := fun h => h

/-- Image-map values carry the original state-map value. -/
theorem imageMap_value
    (F : PartialLicensedReductionMorphism A B) (x : DomainCarrier F) :
    (F.imageMap.map x).val = F.map x :=
  rfl

/-- Inclusion after range restriction is directly the original state map. -/
theorem imageInclusion_imageMap
    (F : PartialLicensedReductionMorphism A B) (x : DomainCarrier F) :
    F.imageInclusion.map (F.imageMap.map x) = F.map x :=
  rfl

/-- Every image state has a domain-state preimage, by construction. -/
theorem imageMap_surjective
    (F : PartialLicensedReductionMorphism A B) :
    Function.Surjective F.imageMap.map := by
  intro y
  rcases y.property with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact hx

/-- Pure state collapse has a one-point image even though its domain has two points. -/
theorem pureStateCollapse_image_identifies_fixture :
    pureStateCollapse_fixture.imageMap.map ⟨ChainNode.source, trivial⟩ =
      pureStateCollapse_fixture.imageMap.map ⟨ChainNode.target, trivial⟩ := by
  apply Subtype.ext
  rfl

#check @imageARS
#check @imageMap
#check @imageInclusion
#check @imageInclusion_imageMap
#check @imageMap_surjective
#check pureStateCollapse_image_identifies_fixture
#print axioms imageARS
#print axioms imageMap
#print axioms imageInclusion
#print axioms imageInclusion_imageMap
#print axioms imageMap_surjective
#print axioms pureStateCollapse_image_identifies_fixture

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
