import OperatorKO7.Meta.LicensedBoundaryCalculus.Observer.Galois
import OperatorKO7.Meta.LicensedBoundaryCalculus.Transport.StepLifting

/-!
# Abstract post and dynamic completeness

Forward simulation makes direct-image abstraction sound for one-step post.
Equality for every source set is equivalent to step lifting. The canonical
quotient-image map inherits the same relation-specific criterion.
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

/-! ## Lifting on classes against lifting from each state

Two source states share one record and only one of them has an edge. The canonical quotient
map is exact, while the observation itself fails pointwise lifting. -/

/-- Source of the control: `some true` and `some false` share a record, and the only edge is
`some true → none`. -/
def repLiftSource_fixture : ARS.{0} where
  Carrier := Option Bool
  step := fun x y => x = some true ∧ y = none
  scope := ⟨.root, .oneStep, .full, .original⟩

/-- Target of the control: the one edge `true → false`. -/
def repLiftTarget_fixture : ARS.{0} where
  Carrier := Bool
  step := fun x y => x = true ∧ y = false
  scope := ⟨.root, .oneStep, .full, .original⟩

/-- The total observation recording whether a state is `some`, admitting every source edge. -/
def repLift_fixture :
    PartialLicensedReductionMorphism repLiftSource_fixture repLiftTarget_fixture where
  domain := fun _ => True
  admitted := repLiftSource_fixture.step
  admitted_sub_raw := fun h => h
  admitted_source_domain := fun _ => trivial
  admitted_target_domain := fun _ => trivial
  map := fun x => Option.isSome x.val
  map_step := by
    rintro x y ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The observation is a forward simulation. -/
theorem repLift_forward :
    ForwardStepSimulation (A := repLiftSource_fixture) (B := repLiftTarget_fixture)
      (fun x : Option Bool => x.isSome) := by
  rintro x y ⟨rfl, rfl⟩
  exact ⟨rfl, rfl⟩

/-- The canonical quotient-to-image map of the control is exact. -/
theorem repLift_quotientImageExact : repLift_fixture.QuotientImageExact := by
  refine (repLift_fixture.quotientImageExact_iff_stepLifting).2 ?_
  intro q z hz
  obtain ⟨x, rfl⟩ := repLift_fixture.kernelProjection_surjective q
  let a : DomainCarrier repLift_fixture := ⟨some true, trivial⟩
  let b : DomainCarrier repLift_fixture := ⟨none, trivial⟩
  obtain ⟨hx, hzv⟩ := hz
  refine ⟨repLift_fixture.kernelProjection b, ⟨a, b, ⟨rfl, rfl⟩, ?_, rfl⟩, ?_⟩
  · exact (repLift_fixture.kernelProjection_eq_iff a x).2 hx.symm
  · exact Subtype.ext hzv.symm

/-- The observation fails pointwise lifting: `some false` has the record `true`, the target
edge `true → false` leaves that record, and `some false` has no source edge. -/
theorem repLift_not_stepLifting :
    ¬ StepLifting (A := repLiftSource_fixture) (B := repLiftTarget_fixture)
      (fun x : Option Bool => x.isSome) := by
  intro h
  obtain ⟨y, ⟨hx, -⟩, -⟩ := h (some false) false ⟨rfl, rfl⟩
  exact absurd hx (by decide)

/-- At one observation, the canonical quotient map commutes with `Post` on every set of
classes, while the observation does not commute with `Post` on every set of states. -/
theorem repLift_quotient_exact_pointwise_not :
    (∀ S : Set repLift_fixture.kernelQuotientARS.Carrier,
      alpha repLift_fixture.quotientToImage (post repLift_fixture.kernelQuotientARS S) =
        post repLift_fixture.imageARS (alpha repLift_fixture.quotientToImage S)) ∧
    ¬ (∀ S : Set repLiftSource_fixture.Carrier,
      alpha (fun x : Option Bool => x.isSome) (post repLiftSource_fixture S) =
        post repLiftTarget_fixture (alpha (fun x : Option Bool => x.isSome) S)) :=
  ⟨(quotientImage_alpha_post_exact_iff repLift_fixture).2 repLift_quotientImageExact,
    fun h => repLift_not_stepLifting
      ((alpha_post_eq_post_alpha_all_iff_stepLifting
        (A := repLiftSource_fixture) (B := repLiftTarget_fixture) _ repLift_forward).1 h)⟩

#check @repLiftSource_fixture
#print axioms repLiftSource_fixture
#check @repLiftTarget_fixture
#print axioms repLiftTarget_fixture
#check @repLift_fixture
#print axioms repLift_fixture
#check @repLift_forward
#print axioms repLift_forward
#check @repLift_quotientImageExact
#print axioms repLift_quotientImageExact
#check @repLift_not_stepLifting
#print axioms repLift_not_stepLifting
#check @repLift_quotient_exact_pointwise_not
#print axioms repLift_quotient_exact_pointwise_not
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
