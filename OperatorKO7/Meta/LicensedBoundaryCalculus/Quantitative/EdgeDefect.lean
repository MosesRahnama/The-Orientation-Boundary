import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.DomainDefect

/-!
# Exact rejected-edge composition

A raw source edge is rejected by a composite exactly when the first morphism
rejects it, or the first morphism admits it and the second rejects its image.
The two cases are disjoint and give an exact finite count.

## Audit slots

Relation: raw source edges and the two admitted subrelations.
Closure: one-step edge admission only.
Trust: kernel-only, with classical case distinction on admission.
Scope: exact rejected-edge decomposition under partial composition.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v w

noncomputable section

/-- First-admitted edges whose images are rejected downstream. -/
abbrev DownstreamRejectedEdge {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :=
  {e : AdmittedEdge F //
    ¬ G.admitted
      (F.map ⟨e.val.1, F.admitted_source_domain e.property⟩)
      (F.map ⟨e.val.2, F.admitted_target_domain e.property⟩)}

/-- Pointwise rejected-edge decomposition. -/
theorem comp_not_admitted_iff {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) (x y : A.Carrier) :
    ¬ (comp F G).admitted x y ↔
      ¬ F.admitted x y ∨
        ∃ hF : F.admitted x y,
          ¬ G.admitted
            (F.map ⟨x, F.admitted_source_domain hF⟩)
            (F.map ⟨y, F.admitted_target_domain hF⟩) := by
  classical
  constructor
  · intro h
    by_cases hF : F.admitted x y
    · right
      refine ⟨hF, ?_⟩
      intro hG
      exact h ⟨hF, hG⟩
    · exact Or.inl hF
  · rintro (hF | ⟨hF, hG⟩)
    · rintro ⟨hF', _⟩
      exact hF hF'
    · rintro ⟨hF', hG'⟩
      apply hG
      simpa only [Subsingleton.elim hF' hF] using hG'

/-- Composite rejected edges split into first-stage and downstream failures. -/
def compositeRejectedEdgeEquiv
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    RejectedEdge (comp F G) ≃ Sum (RejectedEdge F) (DownstreamRejectedEdge F G) := by
  classical
  refine
    { toFun := fun e =>
        if hF : F.admitted e.val.val.1 e.val.val.2 then
          Sum.inr
            ⟨⟨e.val.val, hF⟩, by
              intro hG
              exact e.property ⟨hF, hG⟩⟩
        else
          Sum.inl ⟨e.val, hF⟩
      invFun := fun s =>
        match s with
        | Sum.inl e =>
            ⟨e.val, by
              rintro ⟨hF, _⟩
              exact e.property hF⟩
        | Sum.inr e =>
            ⟨⟨e.val.val, F.admitted_sub_raw e.val.property⟩, by
              rintro ⟨hF, hG⟩
              apply e.property
              simpa only [Subsingleton.elim hF e.val.property] using hG⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro e
    by_cases hF : F.admitted e.val.val.1 e.val.val.2
    · simp [hF]
    · simp [hF]
  · intro s
    cases s with
    | inl e => simp [e.property]
    | inr e => simp [e.val.property]

/-- Number of first-admitted edges rejected by the downstream license. -/
def downstreamRejectedEdgeCount
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) : Nat := by
  classical
  exact Fintype.card (DownstreamRejectedEdge F G)

/-- Exact cardinal decomposition of composite rejected edges. -/
theorem rejectedEdgeCount_comp
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}} [Fintype A.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    rejectedEdgeCount (comp F G) =
      rejectedEdgeCount F + downstreamRejectedEdgeCount F G := by
  classical
  unfold rejectedEdgeCount downstreamRejectedEdgeCount
  calc
    Fintype.card (RejectedEdge (comp F G)) =
        Fintype.card (Sum (RejectedEdge F) (DownstreamRejectedEdge F G)) :=
      Fintype.card_congr (compositeRejectedEdgeEquiv F G)
    _ = Fintype.card (RejectedEdge F) +
        Fintype.card (DownstreamRejectedEdge F G) := by
      exact Fintype.card_sum

/-- Identity followed by the pure-rejection fixture rejects the genuine chain edge. -/
theorem pureEdgeRejection_composite_rejects_fixture :
    ¬ (comp (id chainARS_fixture) pureEdgeRejection_fixture).admitted
      ChainNode.source ChainNode.target := by
  rintro ⟨_, hRejected⟩
  exact hRejected

#check @comp_not_admitted_iff
#check @compositeRejectedEdgeEquiv
#check @rejectedEdgeCount_comp
#check pureEdgeRejection_composite_rejects_fixture
#print axioms comp_not_admitted_iff
#print axioms compositeRejectedEdgeEquiv
#print axioms rejectedEdgeCount_comp
#print axioms pureEdgeRejection_composite_rejects_fixture

end
end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
