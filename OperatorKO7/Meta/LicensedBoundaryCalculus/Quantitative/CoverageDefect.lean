import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.FiberDefect

/-!
# Finite target-coverage defects

The image of a composite is contained in the image of its second morphism, so
composition weakly increases the final-target coverage gap. Gap zero is
equivalent to surjectivity of the proof-carrying partial map.

## Audit slots

Relation: the state maps carried by partial morphisms.
Closure: finite images and target complements.
Trust: kernel-only, with classical finite enumeration.
Scope: final-target coverage under partial composition.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v w

noncomputable section

/-- The image of a composite is contained in the image of its second map. -/
theorem mapImage_comp_subset_second
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    mapImage (comp F G) ⊆ mapImage G := by
  classical
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨x, _, rfl⟩
  apply Finset.mem_image.mpr
  exact ⟨compositeIntermediateMap F G x, Finset.mem_univ _, rfl⟩

/-- Composite image cardinality is bounded by the second-stage image. -/
theorem mapImage_comp_card_le_second
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    (mapImage (comp F G)).card ≤ (mapImage G).card :=
  Finset.card_le_card (mapImage_comp_subset_second F G)

/-- Composition weakly increases the coverage gap of the final target. -/
theorem targetCoverageGap_second_le_comp
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    targetCoverageGap G ≤ targetCoverageGap (comp F G) := by
  have hcard := mapImage_comp_card_le_second F G
  unfold targetCoverageGap
  omega

/-- Zero finite coverage gap is equivalent to surjectivity onto the target
carrier. -/
theorem targetCoverageGap_eq_zero_iff_surjective
    {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B) :
    targetCoverageGap F = 0 ↔ Function.Surjective F.map := by
  classical
  constructor
  · intro hzero
    have hle : Fintype.card B.Carrier ≤ (mapImage F).card := by
      exact Nat.sub_eq_zero_iff_le.mp hzero
    have himage : mapImage F = (Finset.univ : Finset B.Carrier) := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa using hle
    intro y
    have hy : y ∈ mapImage F := by
      rw [himage]
      exact Finset.mem_univ y
    rcases Finset.mem_image.mp hy with ⟨x, _, hx⟩
    exact ⟨x, hx⟩
  · intro hsurj
    have himage : mapImage F = (Finset.univ : Finset B.Carrier) := by
      ext y
      constructor
      · intro _
        exact Finset.mem_univ y
      · intro _
        rcases hsurj y with ⟨x, hx⟩
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩
    unfold targetCoverageGap
    rw [himage]
    simp

/-- The pure state-collapse fixture still covers its one-point target. -/
theorem pureStateCollapse_surjective_fixture :
    Function.Surjective pureStateCollapse_fixture.map := by
  intro y
  cases y
  exact ⟨⟨ChainNode.source, trivial⟩, rfl⟩

#check @mapImage_comp_subset_second
#check @targetCoverageGap_second_le_comp
#check @targetCoverageGap_eq_zero_iff_surjective
#check pureStateCollapse_surjective_fixture
#print axioms mapImage_comp_subset_second
#print axioms targetCoverageGap_second_le_comp
#print axioms targetCoverageGap_eq_zero_iff_surjective
#print axioms pureStateCollapse_surjective_fixture

end
end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
