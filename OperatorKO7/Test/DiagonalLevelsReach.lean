import OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels

/-!
# Reach test: DiagonalLevels

Full coverage for `Meta/DistinctionBoundary/DiagonalLevels.lean`: every public
declaration, including each structure, its constructor, and each of its
projections, is checked and its axiom closure is printed.

`comparisonDiagonal_nonempty_of_classical` and the declarations that consume it
(`unconditional_copy_not_comparison_refuted`) depend on `Classical.choice` by
design: the refutation they carry is a statement about the ambient classical
logic. Every other declaration is expected on the baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels

/-! ## D0: the copy diagonal -/

#check @CopyDiagonal
#check @CopyDiagonal.mk
#check @CopyDiagonal.copy
#check @CopyDiagonal.copy_law
#check @CopyDiagonal.NaturalUnder
#check @traceCopyDiagonal
#check @traceCopyDiagonal_duplicates
#check @copyDiagonal_natural_under_every_map

#print axioms CopyDiagonal
#print axioms CopyDiagonal.mk
#print axioms CopyDiagonal.copy
#print axioms CopyDiagonal.copy_law
#print axioms CopyDiagonal.NaturalUnder
#print axioms traceCopyDiagonal
#print axioms traceCopyDiagonal_duplicates
#print axioms copyDiagonal_natural_under_every_map

/-! ## D1: the comparison diagonal -/

#check @ComparisonDiagonal
#check @ComparisonDiagonal.mk
#check @ComparisonDiagonal.test
#check @ComparisonDiagonal.sound
#check @ComparisonDiagonal.complete
#check @ComparisonDiagonal.NaturalUnder
#check @traceComparisonDiagonal
#check @traceComparisonDiagonal_separates
#check @no_natural_comparisonDiagonal_of_merge

#print axioms ComparisonDiagonal
#print axioms ComparisonDiagonal.mk
#print axioms ComparisonDiagonal.test
#print axioms ComparisonDiagonal.sound
#print axioms ComparisonDiagonal.complete
#print axioms ComparisonDiagonal.NaturalUnder
#print axioms traceComparisonDiagonal
#print axioms traceComparisonDiagonal_separates
#print axioms no_natural_comparisonDiagonal_of_merge

/-! ## The refuted unconditional form and the clone-relative separation -/

#check @comparisonDiagonal_nonempty_of_classical
#check @unconditional_copy_not_comparison_refuted
#check @copy_not_comparison_clone_relative

#print axioms comparisonDiagonal_nonempty_of_classical
#print axioms unconditional_copy_not_comparison_refuted
#print axioms copy_not_comparison_clone_relative

/-! ## Freeness of the kernel carrier -/

#check @TraceEndomorphism
#check @TraceEndomorphism.mk
#check @TraceEndomorphism.map
#check @TraceEndomorphism.map_void
#check @TraceEndomorphism.map_delta
#check @TraceEndomorphism.map_integrate
#check @TraceEndomorphism.map_merge
#check @TraceEndomorphism.map_app
#check @TraceEndomorphism.map_recΔ
#check @TraceEndomorphism.map_eqW
#check @identityTraceEndomorphism
#check @traceEndomorphism_is_identity
#check @traceEndomorphism_never_merges

#print axioms TraceEndomorphism
#print axioms TraceEndomorphism.mk
#print axioms TraceEndomorphism.map
#print axioms TraceEndomorphism.map_void
#print axioms TraceEndomorphism.map_delta
#print axioms TraceEndomorphism.map_integrate
#print axioms TraceEndomorphism.map_merge
#print axioms TraceEndomorphism.map_app
#print axioms TraceEndomorphism.map_recΔ
#print axioms TraceEndomorphism.map_eqW
#print axioms identityTraceEndomorphism
#print axioms traceEndomorphism_is_identity
#print axioms traceEndomorphism_never_merges

/-! ## Sigma-definability -/

#check @evalTrace
#check @SigmaDefinableUnary
#check @SigmaDefinableBinary
#check @sigmaDefinableUnary_nonvacuous
#check @sigmaDefinableBinary_nonvacuous
#check @substVarAByVarB
#check @evalTrace_substVarAByVarB
#check @sigmaDefinableBinary_of_unary
#check @delta_ne_self
#check @sigmaDefinableUnary_delta_diagonal
#check @no_sigmaDefinable_universal_evaluator

#print axioms evalTrace
#print axioms SigmaDefinableUnary
#print axioms SigmaDefinableBinary
#print axioms sigmaDefinableUnary_nonvacuous
#print axioms sigmaDefinableBinary_nonvacuous
#print axioms substVarAByVarB
#print axioms evalTrace_substVarAByVarB
#print axioms sigmaDefinableBinary_of_unary
#print axioms delta_ne_self
#print axioms sigmaDefinableUnary_delta_diagonal
#print axioms no_sigmaDefinable_universal_evaluator

/-! ## D2: self-evaluation and internality -/

#check @SelfEvaluationDiagonal
#check @SelfEvaluationDiagonal.mk
#check @SelfEvaluationDiagonal.Code
#check @SelfEvaluationDiagonal.quote
#check @SelfEvaluationDiagonal.eval
#check @SelfEvaluationDiagonal.diag
#check @SelfEvaluationDiagonal.diag_law
#check @InternalToSignature
#check @InternalToSignature.mk
#check @InternalToSignature.encode
#check @InternalToSignature.decode
#check @InternalToSignature.encode_decode
#check @InternalToSignature.evalDefinable
#check @InternalToSignature.evalUniversal
#check @no_internal_selfEvaluationDiagonal
#check @trivialSelfEvaluationDiagonal
#check @trivialSelfEvaluation_not_universal
#check @internalToSignature_fields_are_individually_satisfiable
#check @trivialSelfEvaluationDiagonal_not_internal
#check @comparison_not_selfEvaluation_definition_relative

#print axioms SelfEvaluationDiagonal
#print axioms SelfEvaluationDiagonal.mk
#print axioms SelfEvaluationDiagonal.Code
#print axioms SelfEvaluationDiagonal.quote
#print axioms SelfEvaluationDiagonal.eval
#print axioms SelfEvaluationDiagonal.diag
#print axioms SelfEvaluationDiagonal.diag_law
#print axioms InternalToSignature
#print axioms InternalToSignature.mk
#print axioms InternalToSignature.encode
#print axioms InternalToSignature.decode
#print axioms InternalToSignature.encode_decode
#print axioms InternalToSignature.evalDefinable
#print axioms InternalToSignature.evalUniversal
#print axioms no_internal_selfEvaluationDiagonal
#print axioms trivialSelfEvaluationDiagonal
#print axioms trivialSelfEvaluation_not_universal
#print axioms internalToSignature_fields_are_individually_satisfiable
#print axioms trivialSelfEvaluationDiagonal_not_internal
#print axioms comparison_not_selfEvaluation_definition_relative

/-! ## The ladder -/

#check @diagonal_levels_ladder
#print axioms diagonal_levels_ladder

end OperatorKO7.Meta.DistinctionBoundary.DiagonalLevels
