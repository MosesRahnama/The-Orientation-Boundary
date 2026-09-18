import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.StructuralProfile

/-!
# Domain-defect composition

Undefined states of a composite split into two disjoint causes: failure of the
first domain check, or success of that check followed by failure of the second.
The cardinality theorem is derived from an explicit equivalence of finite
types, not from an arithmetic field supplied by a caller.

## Formal scope

Relation: intrinsic domains of two composable partial morphisms.
Closure: pointwise logical decomposition and finite cardinality.
Trust: kernel-only, with classical case distinction on domain membership.
Scope: domain defects under partial composition.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v w

noncomputable section

/-- Composite-domain failures. -/
abbrev CompositeDomainDefect {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :=
  {x : A.Carrier // ¬ (comp F G).domain x}

/-- Failures of the downstream domain after a successful first check. -/
abbrev DownstreamDomainDefect {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :=
  {x : DomainState F // ¬ G.domain (F.map x)}

/-- Pointwise domain-defect decomposition. -/
theorem comp_not_domain_iff {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) (x : A.Carrier) :
    ¬ (comp F G).domain x ↔
      ¬ F.domain x ∨
        ∃ hx : F.domain x, ¬ G.domain (F.map ⟨x, hx⟩) := by
  classical
  constructor
  · intro h
    by_cases hx : F.domain x
    · right
      refine ⟨hx, ?_⟩
      intro hG
      apply h
      refine ⟨hx, ?_⟩
      intro hx'
      simpa only [Subsingleton.elim hx' hx] using hG
    · exact Or.inl hx
  · rintro (hx | ⟨hx, hG⟩)
    · intro hcomp
      exact hx hcomp.1
    · intro hcomp
      exact hG (hcomp.2 hx)

/-- The logical split is a disjoint equivalence of finite defect types. -/
def compositeDomainDefectEquiv {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    CompositeDomainDefect F G ≃
      Sum {x : A.Carrier // ¬ F.domain x} (DownstreamDomainDefect F G) := by
  classical
  refine
    { toFun := fun x =>
        if hx : F.domain x.val then
          Sum.inr
            ⟨⟨x.val, hx⟩, by
              intro hG
              apply x.property
              refine ⟨hx, ?_⟩
              intro hx'
              simpa only [Subsingleton.elim hx' hx] using hG⟩
        else
          Sum.inl ⟨x.val, hx⟩
      invFun := fun s =>
        match s with
        | Sum.inl x => ⟨x.val, fun hcomp => x.property hcomp.1⟩
        | Sum.inr x =>
            ⟨x.val.val, fun hcomp => x.property (hcomp.2 x.val.property)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    by_cases hx : F.domain x.val
    · simp [hx]
    · simp [hx]
  · intro s
    cases s with
    | inl x =>
        simp [x.property]
    | inr x =>
        simp [x.val.property]

/-- Number of downstream domain failures after first-stage admission. -/
def downstreamUndefinedStateCount
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) : Nat := by
  classical
  exact Fintype.card (DownstreamDomainDefect F G)

/-- Cardinal decomposition of composite undefined states. -/
theorem undefinedStateCount_comp
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    undefinedStateCount (comp F G) =
      undefinedStateCount F + downstreamUndefinedStateCount F G := by
  classical
  unfold undefinedStateCount downstreamUndefinedStateCount
  calc
    Fintype.card (CompositeDomainDefect F G) =
        Fintype.card
          (Sum {x : A.Carrier // ¬ F.domain x} (DownstreamDomainDefect F G)) :=
      Fintype.card_congr (compositeDomainDefectEquiv F G)
    _ = Fintype.card {x : A.Carrier // ¬ F.domain x} +
        Fintype.card (DownstreamDomainDefect F G) := by
      exact Fintype.card_sum

/-- The partial-chain identity composite instantiates the stated split. -/
theorem partialChain_domainDefect_composition_fixture :
    @undefinedStateCount chainARS_fixture chainARS_fixture
        (by change Fintype ChainNode; infer_instance)
        (comp (id chainARS_fixture) partialChain_fixture) =
      @undefinedStateCount chainARS_fixture chainARS_fixture
          (by change Fintype ChainNode; infer_instance) (id chainARS_fixture) +
        @downstreamUndefinedStateCount
          chainARS_fixture chainARS_fixture chainARS_fixture
          (by change Fintype ChainNode; infer_instance)
          (id chainARS_fixture) partialChain_fixture :=
  @undefinedStateCount_comp
    chainARS_fixture chainARS_fixture chainARS_fixture
    (by change Fintype ChainNode; infer_instance)
    (id chainARS_fixture) partialChain_fixture

#check @comp_not_domain_iff
#check @compositeDomainDefectEquiv
#check @undefinedStateCount_comp
#check partialChain_domainDefect_composition_fixture
#print axioms comp_not_domain_iff
#print axioms compositeDomainDefectEquiv
#print axioms undefinedStateCount_comp
#print axioms partialChain_domainDefect_composition_fixture

end
end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
