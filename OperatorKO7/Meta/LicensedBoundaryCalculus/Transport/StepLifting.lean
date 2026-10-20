import OperatorKO7.Meta.LicensedBoundaryCalculus.Transport.Strength
import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.QuotientImageEquiv

/-!
# Exact quotient-image transport criterion

The quotient-to-image carrier equivalence is always a forward simulation.  It
is a dynamic equivalence exactly when every image step lifts.  This replaces a
loose conditional upgrade with an unconditional equivalence theorem and a
finite counterexample showing why the lifting field cannot be deleted.

## Audit slots

Relation: kernel-quotient direct-image relation and target relation on the image.
Closure: one step; reachability equivalence follows from the resulting ARS
isomorphism.
Trust: kernel-only; quotient injectivity uses baseline `Quot.sound`, and the
equivalence inverse uses baseline `Classical.choice`.
Scope: exact necessary-and-sufficient condition for dynamic quotient-image
equivalence.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

open TransportStrength

universe u v

variable {A : ARS.{u}} {B : ARS.{v}}

/-- The quotient-to-image carrier equivalence also preserves and reflects the
one-step relation. -/
def QuotientImageExact (F : PartialLicensedReductionMorphism A B) : Prop :=
  forall q r,
    F.kernelQuotientARS.step q r <->
      F.imageARS.step (F.quotientToImage q) (F.quotientToImage r)

/-- Exact quotient-image dynamics is equivalent to the missing step-lifting
field.  This theorem is unconditional and identifies the precise upgrade gate. -/
theorem quotientImageExact_iff_stepLifting
    (F : PartialLicensedReductionMorphism A B) :
    F.QuotientImageExact <->
      StepLifting
        (A := F.kernelQuotientARS) (B := F.imageARS) F.quotientToImage := by
  constructor
  · intro hExact q z hqz
    rcases F.quotientToImage_surjective z with ⟨r, rfl⟩
    exact ⟨r, (hExact q r).2 hqz, rfl⟩
  · intro hLift q r
    constructor
    · exact F.quotientToImageMorphism.map_step
    · intro hqr
      rcases hLift q (F.quotientToImage r) hqr with ⟨r', hSource, hImage⟩
      have hr : r' = r := F.quotientToImage_injective hImage
      simpa [hr] using hSource

/-- Exactness is equivalent to bisimulation on the image because forward
simulation is already canonical. -/
theorem quotientImageExact_iff_bisimulationOnImage
    (F : PartialLicensedReductionMorphism A B) :
    F.QuotientImageExact <->
      BisimulationOnImage
        (A := F.kernelQuotientARS) (B := F.imageARS) F.quotientToImage := by
  constructor
  · intro hExact
    exact
      ⟨F.quotientToImageMorphism.map_step,
        (F.quotientImageExact_iff_stepLifting).1 hExact⟩
  · intro hBisim
    exact (F.quotientImageExact_iff_stepLifting).2 hBisim.lift

/-- Under the exact criterion, the canonical carrier equivalence is an ARS
isomorphism. -/
noncomputable def quotientImageARSIsomorphism
    (F : PartialLicensedReductionMorphism A B) (hExact : F.QuotientImageExact) :
    ARSIsomorphism F.kernelQuotientARS F.imageARS where
  toEquiv := F.quotientImageEquiv
  step_iff := hExact

/-- The combined partial-edge-collapse fixture falsifies unconditional dynamic
equivalence: its image target has a self-step while its quotient has no edge. -/
theorem combinedPartialEdgeCollapse_not_quotientImageExact_fixture :
    Not combinedPartialEdgeCollapse_fixture.QuotientImageExact := by
  intro hExact
  let q := combinedPartialEdgeCollapse_fixture.kernelProjection
    ⟨ChainNode.source, rfl⟩
  have hImage : combinedPartialEdgeCollapse_fixture.imageARS.step
      (combinedPartialEdgeCollapse_fixture.quotientToImage q)
      (combinedPartialEdgeCollapse_fixture.quotientToImage q) :=
    trivial
  rcases (hExact q q).2 hImage with ⟨x, y, hxy, _, _⟩
  exact hxy

#check @QuotientImageExact
#check @quotientImageExact_iff_stepLifting
#check @quotientImageExact_iff_bisimulationOnImage
#check @quotientImageARSIsomorphism
#check combinedPartialEdgeCollapse_not_quotientImageExact_fixture
#print axioms quotientImageExact_iff_stepLifting
#print axioms quotientImageExact_iff_bisimulationOnImage
#print axioms quotientImageARSIsomorphism
#print axioms combinedPartialEdgeCollapse_not_quotientImageExact_fixture

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
