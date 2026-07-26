import OperatorKO7.Meta.LicensedBoundaryCalculus.Observer.Galois
import OperatorKO7.Meta.LicensedBoundaryCalculus.Transport.StepLifting

/-!
# Abstract post and dynamic completeness

Forward simulation makes direct-image abstraction sound for one-step post.
Equality for every source set is equivalent to step lifting. The canonical
quotient-image map inherits the same relation-specific criterion.

## Audit slots

Relation: source and target one-step post operators.
Closure: one step only.
Trust: kernel-only; set equality uses baseline propositional extensionality.
Scope: universal post soundness and necessary-and-sufficient completeness.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace ObserverAbstraction

open TransportStrength
open PartialLicensedReductionMorphism

universe u v

variable {A : ARS.{u}} {B : ARS.{v}}

/-- One-step successors of a set. -/
def post (A : ARS.{u}) (S : Set A.Carrier) : Set A.Carrier :=
  {y | exists x, x ∈ S ∧ A.step x y}

/-- Forward simulation universally gives sound abstract post. -/
theorem alpha_post_subset_post_alpha
    (f : A.Carrier -> B.Carrier) (hForward : ForwardStepSimulation f)
    (S : Set A.Carrier) :
    alpha f (post A S) ⊆ post B (alpha f S) := by
  rintro z ⟨y, ⟨x, hx, hxy⟩, rfl⟩
  exact ⟨f x, ⟨x, hx, rfl⟩, hForward hxy⟩

/-- Equality of abstract and concrete post for every set is equivalent to step
lifting. -/
theorem alpha_post_eq_post_alpha_all_iff_stepLifting
    (f : A.Carrier -> B.Carrier) (hForward : ForwardStepSimulation f) :
    (forall S : Set A.Carrier,
      alpha f (post A S) = post B (alpha f S)) <-> StepLifting f := by
  constructor
  · intro hExact x z hxz
    have hz : z ∈ post B (alpha f ({x} : Set A.Carrier)) :=
      ⟨f x, ⟨x, Set.mem_singleton x, rfl⟩, hxz⟩
    rw [← hExact ({x} : Set A.Carrier)] at hz
    rcases hz with ⟨y, ⟨x', hx', hx'y⟩, hyz⟩
    have hxx : x' = x := Set.mem_singleton_iff.mp hx'
    subst x'
    exact ⟨y, hx'y, hyz⟩
  · intro hLift S
    apply Set.Subset.antisymm
    · exact alpha_post_subset_post_alpha f hForward S
    · rintro z ⟨w, ⟨x, hx, rfl⟩, hwz⟩
      rcases hLift x z hwz with ⟨y, hxy, hyz⟩
      exact ⟨y, ⟨x, hx, hxy⟩, hyz⟩

/-- For the canonical quotient-image map, abstract-post equality is equivalent
to quotient-image step lifting. -/
theorem quotientImage_alpha_post_exact_iff
    (F : PartialLicensedReductionMorphism A B) :
    (forall S : Set F.kernelQuotientARS.Carrier,
      alpha F.quotientToImage (post F.kernelQuotientARS S) =
        post F.imageARS (alpha F.quotientToImage S)) <->
      F.QuotientImageExact := by
  have hForward : ForwardStepSimulation
      (A := F.kernelQuotientARS) (B := F.imageARS) F.quotientToImage := by
    intro q r hqr
    exact F.quotientToImageMorphism.map_step hqr
  calc
    _ <-> StepLifting
        (A := F.kernelQuotientARS) (B := F.imageARS) F.quotientToImage :=
      alpha_post_eq_post_alpha_all_iff_stepLifting
        (A := F.kernelQuotientARS) (B := F.imageARS)
        F.quotientToImage hForward
    _ <-> F.QuotientImageExact := F.quotientImageExact_iff_stepLifting.symm

/-- Finite fixture where abstract-post equality fails for a displayed source
set. -/
theorem combinedPartialEdgeCollapse_abstractPost_not_exact_fixture :
    Not (forall S : Set combinedPartialEdgeCollapse_fixture.kernelQuotientARS.Carrier,
      alpha combinedPartialEdgeCollapse_fixture.quotientToImage
          (post combinedPartialEdgeCollapse_fixture.kernelQuotientARS S) =
        post combinedPartialEdgeCollapse_fixture.imageARS
          (alpha combinedPartialEdgeCollapse_fixture.quotientToImage S)) := by
  intro h
  exact combinedPartialEdgeCollapse_not_quotientImageExact_fixture
    ((quotientImage_alpha_post_exact_iff
      combinedPartialEdgeCollapse_fixture).1 h)

#check @alpha_post_subset_post_alpha
#check @alpha_post_eq_post_alpha_all_iff_stepLifting
#check @quotientImage_alpha_post_exact_iff
#check combinedPartialEdgeCollapse_abstractPost_not_exact_fixture
#print axioms alpha_post_subset_post_alpha
#print axioms alpha_post_eq_post_alpha_all_iff_stepLifting
#print axioms quotientImage_alpha_post_exact_iff
#print axioms combinedPartialEdgeCollapse_abstractPost_not_exact_fixture

end ObserverAbstraction
end OperatorKO7.Meta.LicensedBoundaryCalculus
