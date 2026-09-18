import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.ImageARS

/-!
# Quotient-to-image equivalence

The kernel quotient and the state-map image are canonically equivalent as
carriers for every partial licensed morphism. The forward map is also a
one-step simulation. Surjectivity is to the image subtype; the inclusion factor
records its placement in the ambient target.

## Audit slots

Relation: quotient direct-image steps and target steps restricted to the image.
Closure: one-step forward simulation. A reverse simulation requires an
additional hypothesis.
Trust: kernel-only; quotient equality uses `Quot.sound`, and construction of
the inverse equivalence uses baseline `Classical.choice`.
Scope: universal carrier equivalence and forward dynamic transport.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v

variable {A : ARS.{u}} {B : ARS.{v}}

/-- Canonical map from a kernel class to its state-map value in the image. -/
def quotientToImage (F : PartialLicensedReductionMorphism A B) :
    KernelQuotient F -> ImageCarrier F :=
  Quotient.lift
    (fun x => ⟨F.map x, ⟨x, rfl⟩⟩)
    (by
      intro x y h
      exact Subtype.ext h)

/-- The quotient-to-image map sends a projected point to its range-restricted
state-map value. -/
@[simp] theorem quotientToImage_kernelProjection
    (F : PartialLicensedReductionMorphism A B) (x : DomainCarrier F) :
    F.quotientToImage (F.kernelProjection x) = F.imageMap.map x :=
  rfl

/-- The quotient-to-image map is injective. -/
theorem quotientToImage_injective
    (F : PartialLicensedReductionMorphism A B) :
    Function.Injective F.quotientToImage := by
  intro q r h
  induction q using Quotient.inductionOn with
  | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
          apply (kernelProjection_eq_iff F x y).2
          exact congrArg Subtype.val h

/-- The quotient-to-image map is surjective. -/
theorem quotientToImage_surjective
    (F : PartialLicensedReductionMorphism A B) :
    Function.Surjective F.quotientToImage := by
  intro y
  rcases y.property with ⟨x, hx⟩
  refine ⟨F.kernelProjection x, ?_⟩
  apply Subtype.ext
  exact hx

/-- Carrier equivalence between quotient by the state-map kernel and the
state-map image. -/
noncomputable def quotientImageEquiv
    (F : PartialLicensedReductionMorphism A B) :
    KernelQuotient F ≃ ImageCarrier F :=
  Equiv.ofBijective F.quotientToImage
    ⟨F.quotientToImage_injective, F.quotientToImage_surjective⟩

/-- The quotient-to-image map is a forward one-step simulation. -/
def quotientToImageMorphism (F : PartialLicensedReductionMorphism A B) :
    LicensedReductionMorphism F.kernelQuotientARS F.imageARS where
  admitted := F.kernelQuotientARS.step
  admitted_sub_raw := fun h => h
  map := F.quotientToImage
  map_step := by
    intro q r h
    rcases h with ⟨x, y, hxy, rfl, rfl⟩
    change B.step (F.map x) (F.map y)
    convert F.map_step hxy

/-- The carrier equivalence has the same forward map as the canonical morphism. -/
theorem quotientImageEquiv_apply
    (F : PartialLicensedReductionMorphism A B) (q : KernelQuotient F) :
    F.quotientImageEquiv q = F.quotientToImageMorphism.map q :=
  rfl

/-- Fixture whose image is a proper subset of its ambient target. -/
theorem partialChain_imageInclusion_not_surjective_fixture :
    Not (Function.Surjective partialChain_fixture.imageInclusion.map) := by
  intro hsurj
  rcases hsurj ChainNode.target with ⟨y, hy⟩
  rcases y.property with ⟨x, hx⟩
  have hxMap : x.val = y.val := by
    simpa [partialChain_fixture] using hx
  have hsource : x.val = ChainNode.source := x.property
  have htarget : y.val = ChainNode.target := hy
  have : ChainNode.source = ChainNode.target :=
    hsource.symm.trans (hxMap.trans htarget)
  cases this

#check @quotientToImage
#check @quotientToImage_injective
#check @quotientToImage_surjective
#check @quotientImageEquiv
#check @quotientToImageMorphism
#check partialChain_imageInclusion_not_surjective_fixture
#print axioms quotientToImage
#print axioms quotientToImage_injective
#print axioms quotientToImage_surjective
#print axioms quotientImageEquiv
#print axioms quotientToImageMorphism
#print axioms partialChain_imageInclusion_not_surjective_fixture

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
