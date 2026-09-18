import OperatorKO7.Meta.RDRSAlgebraicInterpretationAtlas

/-!
# Reach test: RDRSAlgebraicInterpretationAtlas (T3, Supervisor C)

Resolves every public name in the algebraic-interpretation atlas.
-/

namespace RDRSAlgebraicInterpretationAtlasReach

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.RDRSAlgebraicInterpretationAtlas

#check @algebraicInterpretationRows
#check @algebraicInterpretationRows_length
#check @algebraicInterpretationRows_nodup
#check @algebraicInterpretationRows_complete
#check @algebraic_row_status_exact
#check @Mechanism
#check @mechanismOf
#check @mechanism_assignment_in_lane
#check @NegCoeffPolyBigOHyp
#check @NonlinearPumpHyp
#check @TupleStrictSHyp
#check @HOTupleStrictSHyp
#check @PolynomialKBOHyp
#check @RowHypothesis
#check @conditional_rows_have_named_hypothesis
#check @rdrs_algebraic_interpretation_layer_closed

/-- Sanity: 14 rows. -/
theorem reach_algebraic_row_count :
    algebraicInterpretationRows.length = 14 :=
  algebraicInterpretationRows_length

/-- Sanity: row status is `barrier` or `conditional_barrier` for every row. -/
theorem reach_algebraic_row_status_exact :
    ∀ f, f ∈ algebraicInterpretationRows →
    statusOf f = .barrier ∨ statusOf f = .conditional_barrier :=
  algebraic_row_status_exact

/-- Sanity: mechanism `bigOPolyBound` is the assigned mechanism for the
negative-coefficient polynomial row. -/
theorem reach_negative_coefficient_mechanism :
    mechanismOf .negativeCoefficientPolynomial = .bigOPolyBound := rfl

/-- Sanity: the polynomial-KBO row's hypothesis carrier type matches. -/
theorem reach_polynomial_kbo_hypothesis :
    RowHypothesis .polynomialKBO = PolynomialKBOHyp := rfl

end RDRSAlgebraicInterpretationAtlasReach
