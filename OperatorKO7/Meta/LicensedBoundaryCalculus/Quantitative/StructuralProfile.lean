import OperatorKO7.Meta.LicensedBoundaryCalculus.Core.PartialComposition

/-!
# Intrinsic finite structural profiles

For values returned by `structuralProfile F`, every coordinate is computed
from the partial licensed reduction morphism `F`. The public
`StructuralProfile` record also permits independent construction.

## Formal scope

Relation: source raw relation and the morphism's admitted subrelation.
Closure: finite carrier counting.
Trust: kernel-only, with classical finite enumeration.
Scope: finite structural defects, fibers, and target coverage.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v w

noncomputable section

/-- Source states at which a partial morphism is defined. -/
abbrev DomainState {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) :=
  {x : A.Carrier // F.domain x}

/-- Raw source edges as a finite subtype. -/
abbrev RawEdge (A : ARS.{u}) :=
  {e : A.Carrier × A.Carrier // A.step e.1 e.2}

/-- Admitted source edges as a finite subtype. -/
abbrev AdmittedEdge {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) :=
  {e : A.Carrier × A.Carrier // F.admitted e.1 e.2}

/-- Raw source edges rejected by the license. -/
abbrev RejectedEdge {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) :=
  {e : RawEdge A // ¬ F.admitted e.val.1 e.val.2}

/-- A function fiber over one target value. -/
abbrev FiniteFiber {α : Type u} {β : Type v} (f : α → β) (y : β) :=
  {x : α // f x = y}

/-- Number of source states outside the intrinsic domain. -/
def undefinedStateCount {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Nat := by
  classical
  exact Fintype.card {x : A.Carrier // ¬ F.domain x}

/-- Number of raw source edges. -/
def rawEdgeCount (A : ARS.{u}) [Fintype A.Carrier] : Nat := by
  classical
  exact Fintype.card (RawEdge A)

/-- Number of source edges admitted by the license. -/
def admittedEdgeCount {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Nat := by
  classical
  exact Fintype.card (AdmittedEdge F)

/-- Number of raw source edges rejected by the license. -/
def rejectedEdgeCount {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Nat := by
  classical
  exact Fintype.card (RejectedEdge F)

/-- Cardinality of one finite function fiber. -/
def finiteFiberCard {α : Type u} {β : Type v} [Fintype α]
    (f : α → β) (y : β) : Nat := by
  classical
  exact Fintype.card (FiniteFiber f y)

/-- Maximum finite fiber cardinality, with value zero on an empty target. -/
def maximumFiberCardinalityOf {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] (f : α → β) : Nat := by
  classical
  exact (Finset.univ : Finset β).sup (finiteFiberCard f)

/-- Total excess above one representative in every nonempty fiber. -/
def fiberExcessOf {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] (f : α → β) : Nat := by
  classical
  exact ∑ y : β, finiteFiberCard f y - 1

/-- Number of target points with a genuinely nontrivial fiber. -/
def nontrivialFiberCountOf {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] (f : α → β) : Nat := by
  classical
  exact ((Finset.univ : Finset β).filter (fun y => 1 < finiteFiberCard f y)).card

/-- The finite image of the proof-carrying partial state map. -/
def mapImage {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Finset B.Carrier := by
  classical
  exact Finset.univ.image F.map

/-- Maximum cardinality of a state-identification fiber. -/
def maximumFiberCardinality {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Nat := by
  classical
  exact maximumFiberCardinalityOf F.map

/-- Total state-identification excess. -/
def fiberExcess {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Nat := by
  classical
  exact fiberExcessOf F.map

/-- Number of nontrivial state-identification fibers. -/
def nontrivialFiberCount {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Nat := by
  classical
  exact nontrivialFiberCountOf F.map

/-- Number of target states outside the image of the partial state map. -/
def targetCoverageGap {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Nat :=
  Fintype.card B.Carrier - (mapImage F).card

/-- A finite structural-profile record. The constructor below derives one from
a morphism. -/
structure StructuralProfile where
  undefinedStates : Nat
  rawEdges : Nat
  admittedEdges : Nat
  rejectedEdges : Nat
  maximumFiber : Nat
  fiberExcess : Nat
  nontrivialFibers : Nat
  targetCoverageGap : Nat
  deriving DecidableEq, Repr

/-- Compute all structural-profile coordinates from one morphism. -/
def structuralProfile {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B) : StructuralProfile where
  undefinedStates := undefinedStateCount F
  rawEdges := rawEdgeCount A
  admittedEdges := admittedEdgeCount F
  rejectedEdges := rejectedEdgeCount F
  maximumFiber := maximumFiberCardinality F
  fiberExcess := PartialLicensedReductionMorphism.fiberExcess F
  nontrivialFibers := nontrivialFiberCount F
  targetCoverageGap := PartialLicensedReductionMorphism.targetCoverageGap F

/-- Every admitted edge is a raw edge, quantitatively. -/
theorem admittedEdgeCount_le_rawEdgeCount
    {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B) :
    admittedEdgeCount F ≤ rawEdgeCount A := by
  classical
  let edgeInclusion : AdmittedEdge F → RawEdge A := fun e =>
    ⟨e.val, F.admitted_sub_raw e.property⟩
  have hinjective : Function.Injective edgeInclusion := by
    intro e₁ e₂ h
    apply Subtype.ext
    exact congrArg (fun e : RawEdge A => e.val) h
  exact Fintype.card_le_of_injective edgeInclusion hinjective

/-- Every individual fiber is bounded by the computed maximum. -/
theorem finiteFiberCard_le_maximum {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] (f : α → β) (y : β) :
    finiteFiberCard f y ≤ maximumFiberCardinalityOf f := by
  classical
  exact Finset.le_sup (s := (Finset.univ : Finset β)) (f := finiteFiberCard f)
    (Finset.mem_univ y)

/-- The computed image cardinality is bounded by the finite target carrier. -/
theorem mapImage_card_le_target {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B) :
    (mapImage F).card ≤ Fintype.card B.Carrier := by
  classical
  simpa using Finset.card_le_univ (s := mapImage F)

/-- The profile returned by `structuralProfile` lists the quantities computed
above. -/
theorem structuralProfile_eq_computed {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B) :
    structuralProfile F =
      { undefinedStates := undefinedStateCount F
        rawEdges := rawEdgeCount A
        admittedEdges := admittedEdgeCount F
        rejectedEdges := rejectedEdgeCount F
        maximumFiber := maximumFiberCardinality F
        fiberExcess := PartialLicensedReductionMorphism.fiberExcess F
        nontrivialFibers := nontrivialFiberCount F
        targetCoverageGap := PartialLicensedReductionMorphism.targetCoverageGap F } :=
  rfl

/-- One exhibited out-of-domain state forces a positive undefined-state count. -/
theorem undefinedStateCount_pos_of_not_domain
    {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B) (x : A.Carrier)
    (hx : ¬ F.domain x) : 0 < undefinedStateCount F := by
  classical
  unfold undefinedStateCount
  exact Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩

/-- The genuinely partial chain gives a nonzero undefined-state coordinate. -/
theorem partialChain_undefinedStateCount_pos_fixture :
    0 < @undefinedStateCount chainARS_fixture chainARS_fixture
      (by change Fintype ChainNode; infer_instance) partialChain_fixture := by
  exact @undefinedStateCount_pos_of_not_domain
    chainARS_fixture chainARS_fixture
    (by change Fintype ChainNode; infer_instance)
    partialChain_fixture ChainNode.target partialChain_fixture_undefined_target

#check @structuralProfile
#check @admittedEdgeCount_le_rawEdgeCount
#check @finiteFiberCard_le_maximum
#check @mapImage_card_le_target
#check @undefinedStateCount_pos_of_not_domain
#check partialChain_undefinedStateCount_pos_fixture
#print axioms structuralProfile_eq_computed
#print axioms admittedEdgeCount_le_rawEdgeCount
#print axioms finiteFiberCard_le_maximum
#print axioms mapImage_card_le_target
#print axioms undefinedStateCount_pos_of_not_domain
#print axioms partialChain_undefinedStateCount_pos_fixture

end
end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
