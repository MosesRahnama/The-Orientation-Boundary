import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.CoverageDefect

/-!
# Universal finite structural composition laws

## Formal Scope

The public result is the conjunction of four imported composition laws. It is a four-law finite profile, not a complete invariant of licensed morphisms.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace PartialLicensedReductionMorphism

universe u v w

/-- The four load-bearing finite composition laws hold for every pair of
composable partial licensed morphisms. -/
theorem structural_composition_universal
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    undefinedStateCount (comp F G) =
        undefinedStateCount F + downstreamUndefinedStateCount F G ∧
      rejectedEdgeCount (comp F G) =
        rejectedEdgeCount F + downstreamRejectedEdgeCount F G ∧
      maximumFiberCardinality (comp F G) ≤
        maximumFiberCardinality F * maximumFiberCardinality G ∧
      targetCoverageGap G ≤ targetCoverageGap (comp F G) := by
  exact
    ⟨undefinedStateCount_comp F G,
      rejectedEdgeCount_comp F G,
      maximumFiberCardinality_comp_le F G,
      targetCoverageGap_second_le_comp F G⟩

/-- The following theorem yields the specified logical defect formulas as well as
their finite counts. -/
theorem structural_composition_pointwise_and_quantitative
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    (F : PartialLicensedReductionMorphism A B)
    (G : PartialLicensedReductionMorphism B C) :
    (∀ x,
      ¬ (comp F G).domain x ↔
        ¬ F.domain x ∨
          ∃ hx : F.domain x, ¬ G.domain (F.map ⟨x, hx⟩)) ∧
    (∀ x y,
      ¬ (comp F G).admitted x y ↔
        ¬ F.admitted x y ∨
          ∃ hF : F.admitted x y,
            ¬ G.admitted
              (F.map ⟨x, F.admitted_source_domain hF⟩)
              (F.map ⟨y, F.admitted_target_domain hF⟩)) ∧
    undefinedStateCount (comp F G) =
      undefinedStateCount F + downstreamUndefinedStateCount F G ∧
    rejectedEdgeCount (comp F G) =
      rejectedEdgeCount F + downstreamRejectedEdgeCount F G := by
  exact
    ⟨comp_not_domain_iff F G,
      comp_not_admitted_iff F G,
      undefinedStateCount_comp F G,
      rejectedEdgeCount_comp F G⟩

#check @structural_composition_universal
#check @structural_composition_pointwise_and_quantitative
#print axioms structural_composition_universal
#print axioms structural_composition_pointwise_and_quantitative

end PartialLicensedReductionMorphism
end OperatorKO7.Meta.LicensedBoundaryCalculus
