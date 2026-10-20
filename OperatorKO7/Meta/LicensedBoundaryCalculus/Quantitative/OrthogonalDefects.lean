import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.CoverageDefect

/-!
# Orthogonal structural defect algebra

The compatibility type `RejectedEdge` contains every excluded raw edge.
This module splits it into edges excluded by
endpoint-domain failure and edges whose endpoints are in-domain but whose
license refuses the edge.  State identification and target coverage remain
separate map-derived coordinates.

## Audit slots

Relation: raw source edges, endpoint domains, and admitted edges.
Closure: pointwise disjoint sum and finite cardinality.
Trust: kernel-only classical finite case analysis.
Scope: structural defects of finite partial licensed-reduction morphisms.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v w

noncomputable section

/-- Raw edges whose two endpoints lie in the morphism domain. -/
abbrev DomainResidentRawEdge
    {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) :=
  {e : A.Carrier × A.Carrier //
    A.step e.1 e.2 ∧ F.domain e.1 ∧ F.domain e.2}

/-- Domain-resident raw edges refused by the edge license. -/
abbrev LicenseRejectedEdge
    {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) :=
  {e : DomainResidentRawEdge F //
    ¬ F.admitted e.val.1 e.val.2}

/-- Raw edges excluded because at least one endpoint lies outside the domain. -/
abbrev DomainExcludedRawEdge
    {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) :=
  {e : A.Carrier × A.Carrier //
    A.step e.1 e.2 ∧ (¬ F.domain e.1 ∨ ¬ F.domain e.2)}

/-- Compatibility name for `RejectedEdge`: every excluded raw edge,
partitioned by cause below. -/
abbrev NonAdmittedRawEdge
    {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) :=
  RejectedEdge F

/-- Disjoint split of excluded raw edges by domain and license causes. -/
def nonAdmittedRawEdge_equiv_domainExcluded_sum_licenseRejected
    {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B) :
    NonAdmittedRawEdge F ≃
      Sum (DomainExcludedRawEdge F) (LicenseRejectedEdge F) := by
  classical
  refine
    { toFun := fun e =>
        if hsource : F.domain e.val.val.1 then
          if htarget : F.domain e.val.val.2 then
            Sum.inr
              ⟨⟨e.val.val, e.val.property, hsource, htarget⟩, e.property⟩
          else
            Sum.inl
              ⟨e.val.val, e.val.property, Or.inr htarget⟩
        else
          Sum.inl
            ⟨e.val.val, e.val.property, Or.inl hsource⟩
      invFun := fun split =>
        match split with
        | Sum.inl e =>
            ⟨⟨e.val, e.property.1⟩, by
              intro admitted
              rcases e.property.2 with hsource | htarget
              · exact hsource (F.admitted_source_domain admitted)
              · exact htarget (F.admitted_target_domain admitted)⟩
        | Sum.inr e =>
            ⟨⟨e.val.val, e.val.property.1⟩, e.property⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    by_cases hsource : F.domain e.val.val.1
    · by_cases htarget : F.domain e.val.val.2
      · simp [hsource, htarget]
      · simp [hsource, htarget]
    · simp [hsource]
  · intro split
    cases split with
    | inl e =>
        rcases e.property.2 with hsource | htarget
        · simp [hsource]
        · by_cases hsource : F.domain e.val.1
          · simp [hsource, htarget]
          · simp [hsource]
    | inr e =>
        simp [e.val.property.2.1, e.val.property.2.2]

def nonAdmittedRawEdgeCount
    {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Nat := by
  classical
  exact Fintype.card (NonAdmittedRawEdge F)

def domainExcludedRawEdgeCount
    {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Nat := by
  classical
  exact Fintype.card (DomainExcludedRawEdge F)

def licenseRejectedEdgeCount
    {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B) : Nat := by
  classical
  exact Fintype.card (LicenseRejectedEdge F)

/-- Count decomposition for the compatibility edge count. -/
theorem nonAdmittedRawEdgeCount_eq_domainExcluded_plus_licenseRejected
    {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B) :
    nonAdmittedRawEdgeCount F =
      domainExcludedRawEdgeCount F + licenseRejectedEdgeCount F := by
  classical
  unfold nonAdmittedRawEdgeCount domainExcludedRawEdgeCount
    licenseRejectedEdgeCount
  calc
    Fintype.card (NonAdmittedRawEdge F) =
        Fintype.card
          (Sum (DomainExcludedRawEdge F) (LicenseRejectedEdge F)) :=
      Fintype.card_congr
        (nonAdmittedRawEdge_equiv_domainExcluded_sum_licenseRejected F)
    _ = Fintype.card (DomainExcludedRawEdge F) +
        Fintype.card (LicenseRejectedEdge F) := Fintype.card_sum

/-- The retained count name is definitionally the compatibility count. -/
theorem rejectedEdgeCount_eq_nonAdmittedRawEdgeCount
    {A : ARS.{u}} {B : ARS.{v}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B) :
    rejectedEdgeCount F = nonAdmittedRawEdgeCount F := by
  classical
  unfold rejectedEdgeCount nonAdmittedRawEdgeCount
  rfl

/-- Domain-excluded and license-rejected edges have disjoint underlying raw
edges. -/
theorem state_domain_edge_defects_disjoint
    {A : ARS.{u}} {B : ARS.{v}}
    (F : PartialLicensedReductionMorphism A B)
    (domainExcluded : DomainExcludedRawEdge F)
    (licenseRejected : LicenseRejectedEdge F) :
    domainExcluded.val ≠ licenseRejected.val.val := by
  intro heq
  have hsource : F.domain domainExcluded.val.1 := by
    rw [heq]
    exact licenseRejected.val.property.2.1
  have htarget : F.domain domainExcluded.val.2 := by
    rw [heq]
    exact licenseRejected.val.property.2.2
  rcases domainExcluded.property.2 with hnot | hnot
  · exact hnot hsource
  · exact hnot htarget

/-! ## In-domain refusal composition -/

/-- Composite-domain-resident edges already refused by the first license. -/
abbrev UpstreamCompositeLicenseRejected
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :=
  {e : DomainResidentRawEdge (comp F G) //
    ¬ F.admitted e.val.1 e.val.2}

/-- Composite-domain-resident edges admitted first and refused downstream. -/
abbrev DownstreamCompositeLicenseRejected
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :=
  {e : DomainResidentRawEdge (comp F G) //
    ∃ admitted : F.admitted e.val.1 e.val.2,
      ¬ G.admitted
        (F.map ⟨e.val.1, F.admitted_source_domain admitted⟩)
        (F.map ⟨e.val.2, F.admitted_target_domain admitted⟩)}

/-- Disjoint split of in-domain composite license refusals. -/
def compositeLicenseRejectedEdgeEquiv
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    LicenseRejectedEdge (comp F G) ≃
      Sum (UpstreamCompositeLicenseRejected F G)
        (DownstreamCompositeLicenseRejected F G) := by
  classical
  refine
    { toFun := fun e =>
        if hfirst : F.admitted e.val.val.1 e.val.val.2 then
          Sum.inr
            ⟨e.val, hfirst, by
              intro hsecond
              exact e.property ⟨hfirst, hsecond⟩⟩
        else
          Sum.inl ⟨e.val, hfirst⟩
      invFun := fun split =>
        match split with
        | Sum.inl e =>
            ⟨e.val, by
              rintro ⟨hfirst, _⟩
              exact e.property hfirst⟩
        | Sum.inr e =>
            ⟨e.val, by
              rintro ⟨hfirst, hsecond⟩
              rcases e.property with ⟨hfirst', hreject⟩
              apply hreject
              simpa only [Subsingleton.elim hfirst hfirst'] using hsecond⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    by_cases hfirst : F.admitted e.val.val.1 e.val.val.2
    · simp [hfirst]
    · simp [hfirst]
  · intro split
    cases split with
    | inl e => simp [e.property]
    | inr e =>
        rcases e.property with ⟨hfirst, hreject⟩
        simp [hfirst]

def upstreamCompositeLicenseRejectedCount
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) : Nat := by
  classical
  exact Fintype.card (UpstreamCompositeLicenseRejected F G)

def downstreamCompositeLicenseRejectedCount
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) : Nat := by
  classical
  exact Fintype.card (DownstreamCompositeLicenseRejected F G)

/-- Composition law for the in-domain refusal coordinate. -/
theorem licenseRejected_comp_exact
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    licenseRejectedEdgeCount (comp F G) =
      upstreamCompositeLicenseRejectedCount F G +
        downstreamCompositeLicenseRejectedCount F G := by
  classical
  unfold licenseRejectedEdgeCount upstreamCompositeLicenseRejectedCount
    downstreamCompositeLicenseRejectedCount
  calc
    Fintype.card (LicenseRejectedEdge (comp F G)) =
        Fintype.card
          (Sum (UpstreamCompositeLicenseRejected F G)
            (DownstreamCompositeLicenseRejected F G)) :=
      Fintype.card_congr (compositeLicenseRejectedEdgeEquiv F G)
    _ = Fintype.card (UpstreamCompositeLicenseRejected F G) +
        Fintype.card (DownstreamCompositeLicenseRejected F G) :=
      Fintype.card_sum

/-- Five structural coordinates separating state, domain, license,
identification, and target-coverage defects. -/
structure OrthogonalStructuralProfile where
  undefinedStates : Nat
  domainExcludedRawEdges : Nat
  licenseRejectedEdges : Nat
  stateIdentificationExcess : Nat
  targetCoverageGap : Nat
  deriving DecidableEq, Repr

def orthogonalStructuralProfile
    {A : ARS.{u}} {B : ARS.{v}}
    [Fintype A.Carrier] [Fintype B.Carrier]
    (F : PartialLicensedReductionMorphism A B) :
    OrthogonalStructuralProfile where
  undefinedStates := undefinedStateCount F
  domainExcludedRawEdges := domainExcludedRawEdgeCount F
  licenseRejectedEdges := licenseRejectedEdgeCount F
  stateIdentificationExcess := fiberExcess F
  targetCoverageGap := PartialLicensedReductionMorphism.targetCoverageGap F

/-! ## Disjoint-edge fixtures -/

def pureEdgeRejection_domainExcluded_isEmpty :
    IsEmpty (DomainExcludedRawEdge pureEdgeRejection_fixture) :=
  ⟨fun e => by
    rcases e.property.2 with hsource | htarget
    · exact hsource trivial
    · exact htarget trivial⟩

def pureEdgeRejection_licenseRejected_equiv_unit :
    LicenseRejectedEdge pureEdgeRejection_fixture ≃ Unit := by
  refine
    { toFun := fun _ => ()
      invFun := fun _ =>
        ⟨⟨(ChainNode.source, ChainNode.target), ChainStep.descend,
          trivial, trivial⟩, by
            simp [pureEdgeRejection_fixture]⟩
      left_inv := ?_
      right_inv := by intro x; cases x; rfl }
  rintro ⟨⟨⟨x, y⟩, hstep, hsource, htarget⟩, hreject⟩
  cases hstep
  rfl

def partialChain_domainExcluded_equiv_unit :
    DomainExcludedRawEdge partialChain_fixture ≃ Unit := by
  refine
    { toFun := fun _ => ()
      invFun := fun _ =>
        ⟨(ChainNode.source, ChainNode.target), ChainStep.descend,
          Or.inr partialChain_fixture_undefined_target⟩
      left_inv := ?_
      right_inv := by intro x; cases x; rfl }
  rintro ⟨⟨x, y⟩, hstep, hexcluded⟩
  cases hstep
  rfl

def partialChain_licenseRejected_isEmpty :
    IsEmpty (LicenseRejectedEdge partialChain_fixture) :=
  ⟨fun e => by
    rcases e with ⟨⟨⟨x, y⟩, hstep, hsource, htarget⟩, hreject⟩
    cases hstep
    exact partialChain_fixture_undefined_target htarget⟩

theorem pureEdgeRejection_orthogonal_fixture :
    @domainExcludedRawEdgeCount chainARS_fixture chainARS_fixture
        (by change Fintype ChainNode; infer_instance)
        pureEdgeRejection_fixture = 0 ∧
      @licenseRejectedEdgeCount chainARS_fixture chainARS_fixture
        (by change Fintype ChainNode; infer_instance)
        pureEdgeRejection_fixture = 1 := by
  classical
  letI : Fintype chainARS_fixture.Carrier := by
    change Fintype ChainNode
    infer_instance
  constructor
  · unfold domainExcludedRawEdgeCount
    exact Fintype.card_eq_zero_iff.mpr
      pureEdgeRejection_domainExcluded_isEmpty
  · unfold licenseRejectedEdgeCount
    calc
      Fintype.card (LicenseRejectedEdge pureEdgeRejection_fixture) =
          Fintype.card Unit :=
        Fintype.card_congr pureEdgeRejection_licenseRejected_equiv_unit
      _ = 1 := by simp

theorem partialChain_orthogonal_fixture :
    @domainExcludedRawEdgeCount chainARS_fixture chainARS_fixture
        (by change Fintype ChainNode; infer_instance)
        partialChain_fixture = 1 ∧
      @licenseRejectedEdgeCount chainARS_fixture chainARS_fixture
        (by change Fintype ChainNode; infer_instance)
        partialChain_fixture = 0 := by
  classical
  letI : Fintype chainARS_fixture.Carrier := by
    change Fintype ChainNode
    infer_instance
  constructor
  · unfold domainExcludedRawEdgeCount
    calc
      Fintype.card (DomainExcludedRawEdge partialChain_fixture) =
          Fintype.card Unit :=
        Fintype.card_congr partialChain_domainExcluded_equiv_unit
      _ = 1 := by simp
  · unfold licenseRejectedEdgeCount
    exact Fintype.card_eq_zero_iff.mpr partialChain_licenseRejected_isEmpty

#check @nonAdmittedRawEdge_equiv_domainExcluded_sum_licenseRejected
#check @nonAdmittedRawEdgeCount_eq_domainExcluded_plus_licenseRejected
#check @state_domain_edge_defects_disjoint
#check @licenseRejected_comp_exact
#check pureEdgeRejection_orthogonal_fixture
#check partialChain_orthogonal_fixture
#print axioms nonAdmittedRawEdge_equiv_domainExcluded_sum_licenseRejected
#print axioms nonAdmittedRawEdgeCount_eq_domainExcluded_plus_licenseRejected
#print axioms rejectedEdgeCount_eq_nonAdmittedRawEdgeCount
#print axioms state_domain_edge_defects_disjoint
#print axioms compositeLicenseRejectedEdgeEquiv
#print axioms licenseRejected_comp_exact
#print axioms pureEdgeRejection_orthogonal_fixture
#print axioms partialChain_orthogonal_fixture

end
end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
