import OperatorKO7.Meta.QEC.FourMethodConvergence

/-!
# License-Tag Exhaustiveness for Projection Lists

This module classifies the `licenseTag` stored in each
`ConfessionCoreProjection` into the two constructors of
`ConfessionLicenseTag`. The theorem quantifies over arbitrary finite lists.
The concrete two- and five-element lists are arity fixtures. Behavioral
convergence and a common method adapter lie outside this surface.
-/

namespace OperatorKO7.Meta.BoundaryOperator.UniversalNMethodConvergence

open OperatorKO7.Meta.QEC.FourMethodConvergence

/-- Every confession-core projection's license tag lies in the
`{abstention, leakage}` disjoint union (the union is the full two-element tag
enum). -/
theorem confessionTag_in_union (p : ConfessionCoreProjection) :
    p.licenseTag = ConfessionLicenseTag.abstention ∨
    p.licenseTag = ConfessionLicenseTag.leakage := by
  cases h : p.licenseTag
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Every projection in the list carries one of the two license-tag constructors. -/
theorem stack_all_tags_in_union (stack : List ConfessionCoreProjection) :
    ∀ p ∈ stack,
      p.licenseTag = ConfessionLicenseTag.abstention ∨
      p.licenseTag = ConfessionLicenseTag.leakage :=
  fun p _ => confessionTag_in_union p

/-- Two-element projection-list fixture satisfying license-tag exhaustiveness. -/
theorem two_method_stack_converges :
    ∀ p ∈ [({ projectedAwaySyndromeDimension := 5,
              licenseTag := ConfessionLicenseTag.abstention } : ConfessionCoreProjection),
            { projectedAwaySyndromeDimension := 7,
              licenseTag := ConfessionLicenseTag.leakage }],
      p.licenseTag = ConfessionLicenseTag.abstention ∨
      p.licenseTag = ConfessionLicenseTag.leakage :=
  stack_all_tags_in_union _

/-- Five-element projection-list fixture satisfying license-tag exhaustiveness. -/
theorem five_method_stack_converges :
    ∀ p ∈ [({ projectedAwaySyndromeDimension := 1,
              licenseTag := ConfessionLicenseTag.abstention } : ConfessionCoreProjection),
            { projectedAwaySyndromeDimension := 2, licenseTag := ConfessionLicenseTag.abstention },
            { projectedAwaySyndromeDimension := 3, licenseTag := ConfessionLicenseTag.leakage },
            { projectedAwaySyndromeDimension := 4, licenseTag := ConfessionLicenseTag.leakage },
            { projectedAwaySyndromeDimension := 5, licenseTag := ConfessionLicenseTag.abstention }],
      p.licenseTag = ConfessionLicenseTag.abstention ∨
      p.licenseTag = ConfessionLicenseTag.leakage :=
  stack_all_tags_in_union _

/-- Exported alias for license-tag exhaustiveness over a projection list. -/
def universal_n_method_convergence_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalNMethodConvergence.stack_all_tags_in_union"

end OperatorKO7.Meta.BoundaryOperator.UniversalNMethodConvergence
