import OperatorKO7.Meta.DistinctionBoundary.GodelObject
import OperatorKO7.Meta.DistinctionBoundary.GodelFixedPoint

/-!
# Reach test: Godel object package (G1 through G9 plus paper engine)

Full coverage for the Godel modules: every public declaration, including
each structure, its constructor, and each of its projections, is checked
and its axiom closure is printed.

`represents_trivial_iff` and `trivial_represents_id_not_delta` use
function extensionality on the degenerate instance. Every other
declaration is expected on the baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.Godel

/-! ## Paper engine and schematic object -/

#check @selfap
#check @represents
#check @fixed_point_from_represented_diagonal
#check @fixed_point_free_not_represented
#check @successor_obstruction
#check @self_exclusion
#check @SchematicCode
#check @SchematicCode.proj
#check @SchematicCode.const
#check @SchematicCode.compose
#check @eval
#check @quote
#check @unquote
#check @diag
#check @eval_proj
#check @eval_const
#check @eval_compose
#check @unquote_quote
#check @quote_injective
#check @quote_ne_of_ne
#check @carrier_r5
#check @quote_separates_r5
#check @codeDepth
#check @quote_r5_depth_bound
#check @natEncode
#check @natEncode_zero
#check @natEncode_succ
#check @natEncode_injective
#check @eval_not_second_projection
#check @const_void_represents_constant_void
#check @constant_void_ne_identity
#check @eval_id_or_const
#check @eval_compose_of_const_left
#check @delta_not_identity
#check @delta_not_constant
#check @CodeRepresented
#check @Schematic
#check @Schematic.proj
#check @Schematic.const
#check @Schematic.compose
#check @eval_schematic
#check @schematic_codeRepresented
#check @representability
#check @successor_not_codeRepresented
#check @successor_not_schematic
#check @schematic_class_not_only_identity
#check @codeRepresented_collapses_to_id_or_const
#check @schematic_fails_sharp_kill
#check @update
#check @substitute
#check @subst_eval
#check @subst_eval_r5
#check @substitute_proj_freezes_live_argument
#check @live_proj
#check @freeze_and_live_disagree
#check @live_update_ne_freeze_update
#check @schematicSelfEvaluation
#check @const_quote_forces_identity_selfap
#check @diag_quote_eq_carrier
#check @quote_represented_are_constants
#check @schematic_takes_smaller_class_escape
#check @schematic_not_internal
#check @trivial_cannot_represent_constant_void
#check @toCodeObject
#check @lawvereEvaluate
#check @lawvereEvaluate_self
#check @selfApplicationCorrect_on_all_codes
#check @toEvalMap
#check @selfApplicationCode_is_identity
#check @toFixedPointFree
#check @toSchema
#check @GodelPackage
#check @GodelPackage.mk
#check @GodelPackage.diagonal
#check @GodelPackage.substitute
#check @GodelPackage.update
#check @GodelPackage.subst_eval
#check @schematicPackage
#check @PartialSelfEvaluation
#check @PartialSelfEvaluation.mk
#check @PartialSelfEvaluation.Code
#check @PartialSelfEvaluation.quote
#check @PartialSelfEvaluation.eval?
#check @PartialSelfEvaluation.diag?
#check @PartialSelfEvaluation.diag_law
#check @selfap?
#check @partial_fixed_point_when_defined
#check @toPartial
#check @total_selfap_is_defined_partial
#check @partial_specializes_to_total
#check @nowherePartial
#check @nowhere_selfap_undefined
#check @SeparateValueDiagonal
#check @SeparateValueDiagonal.mk
#check @SeparateValueDiagonal.Code
#check @SeparateValueDiagonal.quote
#check @SeparateValueDiagonal.eval
#check @valueSelfap
#check @unitValued
#check @unit_has_no_fixed_point_free_endomap
#check @unit_valued_has_no_retraction
#check @schematic_has_fixed_point

#print axioms selfap
#print axioms represents
#print axioms fixed_point_from_represented_diagonal
#print axioms fixed_point_free_not_represented
#print axioms successor_obstruction
#print axioms self_exclusion
#print axioms SchematicCode
#print axioms SchematicCode.proj
#print axioms SchematicCode.const
#print axioms SchematicCode.compose
#print axioms eval
#print axioms quote
#print axioms unquote
#print axioms diag
#print axioms eval_proj
#print axioms eval_const
#print axioms eval_compose
#print axioms unquote_quote
#print axioms quote_injective
#print axioms quote_ne_of_ne
#print axioms carrier_r5
#print axioms quote_separates_r5
#print axioms codeDepth
#print axioms quote_r5_depth_bound
#print axioms natEncode
#print axioms natEncode_zero
#print axioms natEncode_succ
#print axioms natEncode_injective
#print axioms eval_not_second_projection
#print axioms const_void_represents_constant_void
#print axioms constant_void_ne_identity
#print axioms eval_id_or_const
#print axioms eval_compose_of_const_left
#print axioms delta_not_identity
#print axioms delta_not_constant
#print axioms CodeRepresented
#print axioms Schematic
#print axioms Schematic.proj
#print axioms Schematic.const
#print axioms Schematic.compose
#print axioms eval_schematic
#print axioms schematic_codeRepresented
#print axioms representability
#print axioms successor_not_codeRepresented
#print axioms successor_not_schematic
#print axioms schematic_class_not_only_identity
#print axioms codeRepresented_collapses_to_id_or_const
#print axioms schematic_fails_sharp_kill
#print axioms update
#print axioms substitute
#print axioms subst_eval
#print axioms subst_eval_r5
#print axioms substitute_proj_freezes_live_argument
#print axioms live_proj
#print axioms freeze_and_live_disagree
#print axioms live_update_ne_freeze_update
#print axioms schematicSelfEvaluation
#print axioms const_quote_forces_identity_selfap
#print axioms diag_quote_eq_carrier
#print axioms quote_represented_are_constants
#print axioms schematic_takes_smaller_class_escape
#print axioms schematic_not_internal
#print axioms trivial_cannot_represent_constant_void
#print axioms toCodeObject
#print axioms lawvereEvaluate
#print axioms lawvereEvaluate_self
#print axioms selfApplicationCorrect_on_all_codes
#print axioms toEvalMap
#print axioms selfApplicationCode_is_identity
#print axioms toFixedPointFree
#print axioms toSchema
#print axioms GodelPackage
#print axioms GodelPackage.mk
#print axioms GodelPackage.diagonal
#print axioms GodelPackage.substitute
#print axioms GodelPackage.update
#print axioms GodelPackage.subst_eval
#print axioms schematicPackage
#print axioms PartialSelfEvaluation
#print axioms PartialSelfEvaluation.mk
#print axioms PartialSelfEvaluation.Code
#print axioms PartialSelfEvaluation.quote
#print axioms PartialSelfEvaluation.eval?
#print axioms PartialSelfEvaluation.diag?
#print axioms PartialSelfEvaluation.diag_law
#print axioms selfap?
#print axioms partial_fixed_point_when_defined
#print axioms toPartial
#print axioms total_selfap_is_defined_partial
#print axioms partial_specializes_to_total
#print axioms nowherePartial
#print axioms nowhere_selfap_undefined
#print axioms SeparateValueDiagonal
#print axioms SeparateValueDiagonal.mk
#print axioms SeparateValueDiagonal.Code
#print axioms SeparateValueDiagonal.quote
#print axioms SeparateValueDiagonal.eval
#print axioms valueSelfap
#print axioms unitValued
#print axioms unit_has_no_fixed_point_free_endomap
#print axioms unit_valued_has_no_retraction
#print axioms schematic_has_fixed_point
/-! ## G7 diagonal lemma -/


/-! ## G8 freeze coupling -/


/-! ## G9 reflection stage -/


end OperatorKO7.Meta.DistinctionBoundary.Godel

namespace OperatorKO7.Meta.DistinctionBoundary.GodelFixedPoint

/-! ## GodelFixedPoint paper engine -/

#check @selfApplication
#check @Represents
#check @represented_composite_has_fixed_point
#check @not_represents_composite_of_fixed_point_free
#check @not_represents_delta_composite
#check @ClosedUnderLeftDelta
#check @self_exclusion_of_class
#check @trivial_not_represents_delta_composite
#check @represents_trivial_iff
#check @trivial_represents_id_not_delta

#print axioms selfApplication
#print axioms Represents
#print axioms represented_composite_has_fixed_point
#print axioms not_represents_composite_of_fixed_point_free
#print axioms not_represents_delta_composite
#print axioms ClosedUnderLeftDelta
#print axioms self_exclusion_of_class
#print axioms trivial_not_represents_delta_composite
#print axioms represents_trivial_iff
#print axioms trivial_represents_id_not_delta

end OperatorKO7.Meta.DistinctionBoundary.GodelFixedPoint
