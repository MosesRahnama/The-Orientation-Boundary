import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.QuotientImageEquiv
import OperatorKO7.Meta.LicensedBoundaryCalculus.OrientationFace
import OperatorKO7.Meta.LicensedBoundaryCalculus.DistinctionFace

/-!
# Universal canonical boundary factorization

Every partial licensed reduction morphism factors through domain restriction,
edge restriction, quotient by the state-map kernel, the state-map image, and
image inclusion. The theorem is quantified over the entire partial-morphism
type; its construction uses the fields already present in that type.

## Audit slots

Relation: source raw relation, admitted relation, quotient direct image, image
target relation, and full target relation.
Closure: one-step simulation; path and reachability transport follow from the
component morphisms.
Trust: kernel-only; equality uses `propext` and quotient equality uses
`Quot.sound`, both within the baseline.
Scope: universal and unconditional canonical factorization of partial licensed
reduction morphisms.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v

variable {A : ARS.{u}} {B : ARS.{v}}

/-- Domain restriction followed by admitted-edge restriction. -/
def domainEdgeComposite (F : PartialLicensedReductionMorphism A B) :
    PartialLicensedReductionMorphism A F.admittedEdgeARS :=
  comp F.domainRestriction F.edgeRestrictionOnDomain.toPartial

/-- Add quotient by the state-map kernel. -/
def domainEdgeKernelComposite (F : PartialLicensedReductionMorphism A B) :
    PartialLicensedReductionMorphism A F.kernelQuotientARS :=
  comp F.domainEdgeComposite F.kernelProjectionMorphism.toPartial

/-- Add the quotient-to-image map. -/
def domainEdgeKernelImageComposite (F : PartialLicensedReductionMorphism A B) :
    PartialLicensedReductionMorphism A F.imageARS :=
  comp F.domainEdgeKernelComposite F.quotientToImageMorphism.toPartial

/-- Full five-factor canonical composite. -/
def canonicalComposite (F : PartialLicensedReductionMorphism A B) :
    PartialLicensedReductionMorphism A B :=
  comp F.domainEdgeKernelImageComposite F.imageInclusion.toPartial

/-- The canonical composite has the original domain. -/
theorem canonicalComposite_domain_iff
    (F : PartialLicensedReductionMorphism A B) (x : A.Carrier) :
    F.canonicalComposite.domain x <-> F.domain x := by
  constructor
  · intro h
    exact h.1.1.1.1
  · intro hF
    have hD : F.domainRestriction.domain x := hF
    have hDE : F.domainEdgeComposite.domain x := ⟨hD, fun _ => trivial⟩
    have hDEK : F.domainEdgeKernelComposite.domain x :=
      ⟨hDE, fun _ => trivial⟩
    have hDEKI : F.domainEdgeKernelImageComposite.domain x :=
      ⟨hDEK, fun _ => trivial⟩
    exact ⟨hDEKI, fun _ => trivial⟩

/-- The canonical composite admits the original licensed source edges. -/
theorem canonicalComposite_admitted_iff
    (F : PartialLicensedReductionMorphism A B) (x y : A.Carrier) :
    F.canonicalComposite.admitted x y <-> F.admitted x y := by
  constructor
  · intro h
    rcases h with ⟨hDEKI, _⟩
    rcases hDEKI with ⟨hDEK, _⟩
    rcases hDEK with ⟨hDE, _⟩
    rcases hDE with ⟨_, hF⟩
    exact hF
  · intro hF
    have hD : F.domainRestriction.admitted x y :=
      ⟨F.admitted_sub_raw hF, F.admitted_source_domain hF,
        F.admitted_target_domain hF⟩
    have hDE : F.domainEdgeComposite.admitted x y := by
      refine ⟨hD, ?_⟩
      exact hF
    have hDEK : F.domainEdgeKernelComposite.admitted x y := by
      refine ⟨hDE, ?_⟩
      convert F.domainEdgeComposite.map_step hDE
    have hDEKI : F.domainEdgeKernelImageComposite.admitted x y := by
      refine ⟨hDEK, ?_⟩
      convert F.domainEdgeKernelComposite.map_step hDEK
    refine ⟨hDEKI, ?_⟩
    convert F.domainEdgeKernelImageComposite.map_step hDEKI

/-- Universal and unconditional five-factor equality. -/
theorem canonical_boundary_factorization_universal_unconditional
    (F : PartialLicensedReductionMorphism A B) :
    F.canonicalComposite = F := by
  apply PartialLicensedReductionMorphism.ext
  · exact F.canonicalComposite_domain_iff
  · exact F.canonicalComposite_admitted_iff
  · intro x hxComposite hxF
    rfl

/-- A packaged certificate exposing all five canonical factors and their
composite equality. -/
structure CanonicalBoundaryFactorization
    (F : PartialLicensedReductionMorphism A B) where
  domainFactor : PartialLicensedReductionMorphism A F.domainRestrictedARS
  edgeFactor : LicensedReductionMorphism F.domainRestrictedARS F.admittedEdgeARS
  kernelFactor : LicensedReductionMorphism F.admittedEdgeARS F.kernelQuotientARS
  quotientImageFactor : LicensedReductionMorphism F.kernelQuotientARS F.imageARS
  inclusionFactor : LicensedReductionMorphism F.imageARS B
  composite_eq : canonicalComposite F = F

/-- Every partial licensed morphism has the canonical factorization certificate. -/
def canonicalFactorization (F : PartialLicensedReductionMorphism A B) :
    CanonicalBoundaryFactorization F where
  domainFactor := F.domainRestriction
  edgeFactor := F.edgeRestrictionOnDomain
  kernelFactor := F.kernelProjectionMorphism
  quotientImageFactor := F.quotientToImageMorphism
  inclusionFactor := F.imageInclusion
  composite_eq := F.canonical_boundary_factorization_universal_unconditional

/-- Orientation is an instance of the universal canonical factorization. -/
theorem orientation_canonical_factorization_fixture :
    canonicalComposite
        OrientationFace.boolOrientationFace_fixture.toMorphism.toPartial =
      OrientationFace.boolOrientationFace_fixture.toMorphism.toPartial :=
  canonical_boundary_factorization_universal_unconditional _

/-- Distinction is an instance of the same universal canonical factorization. -/
theorem distinction_canonical_factorization_fixture :
    canonicalComposite
        DistinctionFace.ko7DistinctionFace_fixture.toMorphism.toPartial =
      DistinctionFace.ko7DistinctionFace_fixture.toMorphism.toPartial :=
  canonical_boundary_factorization_universal_unconditional _

#check @canonicalComposite
#check @canonicalComposite_domain_iff
#check @canonicalComposite_admitted_iff
#check @canonical_boundary_factorization_universal_unconditional
#check @canonicalFactorization
#check orientation_canonical_factorization_fixture
#check distinction_canonical_factorization_fixture
#print axioms canonicalComposite
#print axioms canonicalComposite_domain_iff
#print axioms canonicalComposite_admitted_iff
#print axioms canonical_boundary_factorization_universal_unconditional
#print axioms canonicalFactorization
#print axioms orientation_canonical_factorization_fixture
#print axioms distinction_canonical_factorization_fixture

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
