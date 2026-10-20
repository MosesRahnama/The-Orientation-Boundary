import OperatorKO7.Meta.RDRSConditionalTypedAtlas
import OperatorKO7.Meta.RDRSSemanticStructuralAtlas

/-!
# RDRS Transformation-Method Atlas (T7 shim)

Roadmap row: `Expansion/RDRS_Termination_Methods_Roadmap.md` milestone T7,
"Transformation, Conditional, And Constrained Methods" -- semantic labeling /
predictive labeling / root labeling / self-labeling, CTRS operational
termination, 2D DP framework, integer term rewriting, LCTRS / higher-order
LCTRS, categorical / topos niche.

This module exists as a stable import path for the historical T7 file name.
The conditional / constrained / higher-order content landed inside the
conditional-typed atlas; the semantic-labeling and topos rows landed inside
the semantic / structural atlas under the `importTransformation` and
`schemaInterfaceMismatch` mechanisms.

Supersession map:

  semantic / predictive / root / self labeling
                                        -> OperatorKO7.RDRSSemanticStructuralAtlas
                                           (mechanism `importTransformation`)
  CTRS operational termination, quasi-decreasing classification
                                        -> OperatorKO7.RDRSConditionalTypedAtlas
                                           (`operationalTerminationCTRS`,
                                            `twoDDPForCTRS`)
  integer term rewriting, LCTRS, higher-order LCTRS
                                        -> OperatorKO7.RDRSConditionalTypedAtlas
                                           (`integerTermRewriting`, `lctrs`,
                                            `higherOrderLCTRS`)
  categorical / topos niche row         -> OperatorKO7.RDRSSemanticStructuralAtlas
                                           (mechanism `schemaInterfaceMismatch`)

The T7 closure marker `rdrs_conditional_typed_layer_closed` is exposed by
`OperatorKO7.RDRSConditionalTypedAtlas`; the semantic-row closure marker
`rdrs_semantic_structural_layer_closed` is exposed by
`OperatorKO7.RDRSSemanticStructuralAtlas`. No `sorry`, `axiom`,
`native_decide`, `@[csimp]`, `unsafe`, `partial`, or `opaque` is introduced.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSTransformationMethodAtlas

def supersededBy : List String :=
  ["OperatorKO7.RDRSConditionalTypedAtlas",
   "OperatorKO7.RDRSSemanticStructuralAtlas"]

theorem rdrs_transformation_method_atlas_shim_marker :
    supersededBy.length = 2 ∧ supersededBy.Nodup := by
  refine ⟨rfl, ?_⟩
  simp [supersededBy, List.Nodup]

end OperatorKO7.RDRSTransformationMethodAtlas
