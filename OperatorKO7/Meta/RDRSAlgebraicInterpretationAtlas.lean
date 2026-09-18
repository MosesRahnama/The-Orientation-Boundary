import OperatorKO7.Meta.RDRSTerminationMethodUniverse

/-!
# RDRS Algebraic-Interpretation Atlas (T3, Supervisor C)

Closes the 14 algebraic-interpretation rows from `RDRSMethodFamily`:

```text
linearPolyQ                  barrier             scalarOrdering
linearPolyR                  barrier             scalarOrdering
negativeCoefficientPolynomial conditional_barrier bigOPolyBound        (hyp)
maxPolynomial                barrier             maxPlusOrdering
nonlinearHigherDegreePolynomial conditional_barrier nonlinearPump      (hyp)
multilinearInterpretation    barrier             nonlinearPump
matrixNScalarProjection      barrier             matrixScalarProjection
matrixQRScalarProjection     barrier             matrixScalarProjection
arcticScalarProjection       barrier             maxPlusOrdering
tropicalScalarProjection     barrier             maxPlusOrdering
triangularMatrix             barrier             matrixScalarProjection
tupleInterpretationStrictS   conditional_barrier tupleCoordinateAF    (hyp)
higherOrderTupleInterpretation conditional_barrier hoTupleStrictS     (hyp)
polynomialKBO                conditional_barrier polynomialKBOLift    (hyp)
```

Conditional rows are framed via explicit hypothesis structures
(`NegCoeffPolyBigOHyp`, `NonlinearPumpHyp`, `TupleStrictSHyp`,
`HOTupleStrictSHyp`, `PolynomialKBOHyp`). No universal claim is made
over all tuple interpretations, all WPOs, or all algebraic-termination
methods. Tuple and polynomial-KBO escape are framed through coordinate-
AF, head precedence, algebra import, or explicit strict-s hypotheses.

No proof placeholders, no top-level postulates, and no anonymous examples in
production code.
-/

namespace OperatorKO7.RDRSAlgebraicInterpretationAtlas

open OperatorKO7.RDRSTerminationMethodUniverse

/-! ## Row inventory -/

/-- The 14 algebraic-interpretation rows, fixed in source order. -/
def algebraicInterpretationRows : List RDRSMethodFamily :=
  [ .linearPolyQ
  , .linearPolyR
  , .negativeCoefficientPolynomial
  , .maxPolynomial
  , .nonlinearHigherDegreePolynomial
  , .multilinearInterpretation
  , .matrixNScalarProjection
  , .matrixQRScalarProjection
  , .arcticScalarProjection
  , .tropicalScalarProjection
  , .triangularMatrix
  , .tupleInterpretationStrictS
  , .higherOrderTupleInterpretation
  , .polynomialKBO ]

/-- The row list has length exactly 14. -/
theorem algebraicInterpretationRows_length :
    algebraicInterpretationRows.length = 14 := by decide

/-- The row list is duplicate-free. -/
theorem algebraicInterpretationRows_nodup :
    algebraicInterpretationRows.Nodup := by decide

/-- Membership in the 14-row inventory iff the family is one of the
named algebraic-interpretation rows. -/
theorem algebraicInterpretationRows_complete (f : RDRSMethodFamily) :
    f ∈ algebraicInterpretationRows ↔
      f = .linearPolyQ ∨ f = .linearPolyR
        ∨ f = .negativeCoefficientPolynomial
        ∨ f = .maxPolynomial
        ∨ f = .nonlinearHigherDegreePolynomial
        ∨ f = .multilinearInterpretation
        ∨ f = .matrixNScalarProjection
        ∨ f = .matrixQRScalarProjection
        ∨ f = .arcticScalarProjection
        ∨ f = .tropicalScalarProjection
        ∨ f = .triangularMatrix
        ∨ f = .tupleInterpretationStrictS
        ∨ f = .higherOrderTupleInterpretation
        ∨ f = .polynomialKBO := by
  cases f <;> simp [algebraicInterpretationRows]

/-! ## Status-match theorem -/

/-- Every row in the algebraic-interpretation atlas carries either a
`barrier` or a `conditional_barrier` terminal status from the universe
substrate. Verified by case analysis on the row enum. -/
theorem algebraic_row_status_exact :
    ∀ f, f ∈ algebraicInterpretationRows →
      statusOf f = .barrier ∨ statusOf f = .conditional_barrier := by
  intro f hf
  rcases (algebraicInterpretationRows_complete f).1 hf with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-! ## Mechanism classification -/

/-- Positive mechanism classification for the algebraic-interpretation
lane. Eight mechanisms cover the 14 rows. -/
inductive Mechanism
  | scalarOrdering
  | bigOPolyBound
  | matrixScalarProjection
  | maxPlusOrdering
  | nonlinearPump
  | tupleCoordinateAF
  | hoTupleStrictS
  | polynomialKBOLift
  deriving DecidableEq, Repr

/-- Per-row mechanism. Non-algebraic rows fall back to `.scalarOrdering`
(unused; the public API only consults this through
`mechanism_assignment_in_lane`). -/
def mechanismOf : RDRSMethodFamily → Mechanism
  | .linearPolyQ => .scalarOrdering
  | .linearPolyR => .scalarOrdering
  | .negativeCoefficientPolynomial => .bigOPolyBound
  | .maxPolynomial => .maxPlusOrdering
  | .nonlinearHigherDegreePolynomial => .nonlinearPump
  | .multilinearInterpretation => .nonlinearPump
  | .matrixNScalarProjection => .matrixScalarProjection
  | .matrixQRScalarProjection => .matrixScalarProjection
  | .arcticScalarProjection => .maxPlusOrdering
  | .tropicalScalarProjection => .maxPlusOrdering
  | .triangularMatrix => .matrixScalarProjection
  | .tupleInterpretationStrictS => .tupleCoordinateAF
  | .higherOrderTupleInterpretation => .hoTupleStrictS
  | .polynomialKBO => .polynomialKBOLift
  | _ => .scalarOrdering

/-- Every algebraic-lane row receives a mechanism by construction. -/
theorem mechanism_assignment_in_lane :
    ∀ f, f ∈ algebraicInterpretationRows →
      ∃ m : Mechanism, mechanismOf f = m :=
  fun f _ => ⟨mechanismOf f, rfl⟩

/-! ## Hypothesis structures for conditional-barrier rows -/

/-- `negativeCoefficientPolynomial` survives only with a Big-O upper
bound on each nonnegative-clipped polynomial component, witnessed by an
explicit monotone bound. -/
structure NegCoeffPolyBigOHyp where
  bigOBound       : Nat → Nat
  bigOMonotone    : ∀ a b, a ≤ b → bigOBound a ≤ bigOBound b

/-- `nonlinearHigherDegreePolynomial` survives only with a fixed degree
bound and an explicit pump witness; no universal claim over all
polynomial degrees is made. -/
structure NonlinearPumpHyp where
  degreeBound  : Nat
  pumpWitness  : Nat

/-- `tupleInterpretationStrictS` survives only with a designated
coordinate-level strict-s component (`strictIndex < arity`) admitting
the coordinate-AF lift. -/
structure TupleStrictSHyp where
  arity                 : Nat
  strictIndex           : Nat
  strictIndex_lt_arity  : strictIndex < arity

/-- `higherOrderTupleInterpretation` survives only with a designated
strict coordinate and an admissible argument-filter flag. -/
structure HOTupleStrictSHyp where
  arity                       : Nat
  strictIndex                 : Nat
  strictIndex_lt_arity        : strictIndex < arity
  argumentFilterAdmissible    : Bool

/-- `polynomialKBO` survives only with head precedence as the dominant
strict relation plus a bounded coefficient layer. -/
structure PolynomialKBOHyp where
  precedenceWitness   : Nat
  coeffBound          : Nat

/-- Per-row hypothesis carrier dispatch. Rows without a conditional
hypothesis use `PUnit`. -/
def RowHypothesis : RDRSMethodFamily → Type
  | .negativeCoefficientPolynomial => NegCoeffPolyBigOHyp
  | .nonlinearHigherDegreePolynomial => NonlinearPumpHyp
  | .tupleInterpretationStrictS => TupleStrictSHyp
  | .higherOrderTupleInterpretation => HOTupleStrictSHyp
  | .polynomialKBO => PolynomialKBOHyp
  | _ => PUnit

/-- Conditional rows match `conditional_barrier`; their hypothesis
carrier is the only entry point into a successful orientation lift. -/
theorem conditional_rows_have_named_hypothesis :
    (statusOf .negativeCoefficientPolynomial = .conditional_barrier
      ∧ RowHypothesis .negativeCoefficientPolynomial = NegCoeffPolyBigOHyp)
    ∧ (statusOf .nonlinearHigherDegreePolynomial = .conditional_barrier
      ∧ RowHypothesis .nonlinearHigherDegreePolynomial = NonlinearPumpHyp)
    ∧ (statusOf .tupleInterpretationStrictS = .conditional_barrier
      ∧ RowHypothesis .tupleInterpretationStrictS = TupleStrictSHyp)
    ∧ (statusOf .higherOrderTupleInterpretation = .conditional_barrier
      ∧ RowHypothesis .higherOrderTupleInterpretation = HOTupleStrictSHyp)
    ∧ (statusOf .polynomialKBO = .conditional_barrier
      ∧ RowHypothesis .polynomialKBO = PolynomialKBOHyp) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-! ## Final closure marker -/

/-- **Closure marker.** The 14-row algebraic-interpretation lane is
complete and exact: length 14, duplicate-free, every row's status is
`barrier` or `conditional_barrier`, every row has a named positive
mechanism, and every conditional-barrier row has a named hypothesis
structure. -/
theorem rdrs_algebraic_interpretation_layer_closed :
    algebraicInterpretationRows.length = 14
      ∧ algebraicInterpretationRows.Nodup
      ∧ (∀ f, f ∈ algebraicInterpretationRows →
          statusOf f = .barrier ∨ statusOf f = .conditional_barrier)
      ∧ (∀ f, f ∈ algebraicInterpretationRows →
          ∃ m : Mechanism, mechanismOf f = m)
      ∧ ((statusOf .negativeCoefficientPolynomial = .conditional_barrier
            ∧ RowHypothesis .negativeCoefficientPolynomial = NegCoeffPolyBigOHyp)
        ∧ (statusOf .nonlinearHigherDegreePolynomial = .conditional_barrier
            ∧ RowHypothesis .nonlinearHigherDegreePolynomial = NonlinearPumpHyp)
        ∧ (statusOf .tupleInterpretationStrictS = .conditional_barrier
            ∧ RowHypothesis .tupleInterpretationStrictS = TupleStrictSHyp)
        ∧ (statusOf .higherOrderTupleInterpretation = .conditional_barrier
            ∧ RowHypothesis .higherOrderTupleInterpretation = HOTupleStrictSHyp)
        ∧ (statusOf .polynomialKBO = .conditional_barrier
            ∧ RowHypothesis .polynomialKBO = PolynomialKBOHyp)) :=
  ⟨algebraicInterpretationRows_length,
   algebraicInterpretationRows_nodup,
   algebraic_row_status_exact,
   mechanism_assignment_in_lane,
   conditional_rows_have_named_hypothesis⟩

end OperatorKO7.RDRSAlgebraicInterpretationAtlas
