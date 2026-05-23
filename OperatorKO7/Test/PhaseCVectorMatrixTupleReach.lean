import OperatorKO7.Meta.TupleDecomposition

/-!
# Reach test: Phase C Vector / Matrix / Tuple lift

Confirms that every public name added by the Phase C modules
(`PayloadExposureMatrix`, `MatrixOverPolynomialReduction`,
`TupleDecomposition`) is reachable and type-checks. The reach test
imports only the topmost Phase C module and supplies one inline
concrete family witness so the canonical exposure matrix, its DWO lift,
the matrix-over-polynomial reduction, the tuple decomposition, and the
Phase C capstone all specialize on a concrete carrier without depending
on later phase modules.
-/

namespace OperatorKO7.StepDuplicating

/-! ## Public-name reach checks -/

#check @PayloadExposureMatrix
#check @PayloadExposureMatrix.mk
#check @PayloadExposureMatrix.entry
#check @PayloadExposureMatrix.projects_payloadCount
#check @payloadExposureMatrix
#check @payloadExposureMatrix_projects_payloadCount
#check @payloadExposureMatrix_to_DWO

#check @MatrixOverPolynomial
#check @MatrixOverPolynomial.mk
#check @MatrixOverPolynomial.matrix
#check @MatrixOverPolynomial.crossCoupled
#check @MatrixOverPolynomial.crossCoupled_witness
#check @matrixOverPolynomial_reduces_to_nonlinear_escape
#check @matrixOverPolynomial_correspondence_certificate

#check @TupleDispositionKind
#check @TupleDispositionKind.scalar
#check @TupleDispositionKind.matrix
#check @TupleDispositionKind.status
#check @TupleDecomposition
#check @TupleDecomposition.mk
#check @TupleDecomposition.rows
#check @TupleDecomposition.scalar_observer
#check @TupleDecomposition.matrix_observer
#check @tupleDecomposition_to_scalar_or_matrix
#check @phaseC_vector_matrix_tuple_closed

/-! ## Concrete reach example

The same trivial single-payload single-position family used by
`DirectWholeTermObserverReach`: `Step` is `fun a b => a = false ∧ b = true`
so the rule's lhs steps to its rhs and no other steps fire; the schema's
`payloadCount` is `if t then 2 else 1` so the strict count rise holds by
`decide`. The reach example exercises every Phase C public name on this
concrete carrier. -/

private def reachSchemaC : RightDuplicatingRecursorSchema where
  Term := Bool
  PayloadCoord := Unit
  Position := Unit
  lhs := false
  rhs := true
  payloadOccursAt := fun _ _ _ => True
  payloadCount := fun _ t => if t then 2 else 1
  distinguishedPayload := ()
  lhs_has_payload := rfl
  rhs_duplicates_payload := by decide
  firesOnClosedTerms := True

private def reachFamilyC : DuplicatingRecursiveFamily where
  schema := reachSchemaC
  Step := fun a b => a = false ∧ b = true
  duplicating_step := And.intro rfl rfl
  HasUnboundedPayloadPump := fun _ => True
  ExposesPayloadStrictly := fun _ => True
  distinguished_exposed := True.intro
  exposure_strict_count := by
    intro _ _
    show (1 : Nat) < 2
    decide

/-- Projection identity reach check on a concrete carrier. -/
example :
    ∀ (i : reachFamilyC.schema.PayloadCoord) (t : reachFamilyC.schema.Term),
      (payloadExposureMatrix reachFamilyC).entry i t
        = reachFamilyC.schema.payloadCount i t := by
  intros; rfl

/-- Canonical matrix-over-polynomial relation on the reach family. -/
private def reachMatrixOverPolynomialC :
    MatrixOverPolynomial reachFamilyC where
  matrix := payloadExposureMatrix reachFamilyC
  crossCoupled := True
  crossCoupled_witness := True.intro

/-- Phase C reduction: the canonical lift of the reach matrix-over-
polynomial cannot globally orient the reach family. -/
example :
    ¬ reachFamilyC.GloballyOrients
        (payloadExposureMatrix_to_DWO reachMatrixOverPolynomialC.matrix) :=
  matrixOverPolynomial_reduces_to_nonlinear_escape
    reachMatrixOverPolynomialC True.intro

/-- Phase C correspondence certificate on the reach family. -/
example :
    (¬ reachFamilyC.GloballyOrients
        (payloadExposureMatrix_to_DWO reachMatrixOverPolynomialC.matrix))
      ∧ (∀ (i : reachFamilyC.schema.PayloadCoord)
           (t : reachFamilyC.schema.Term),
          reachMatrixOverPolynomialC.matrix.entry i t
            = reachFamilyC.schema.payloadCount i t) :=
  matrixOverPolynomial_correspondence_certificate
    reachMatrixOverPolynomialC True.intro

/-- Canonical tuple decomposition on the reach family. -/
private def reachTupleDecompositionC : TupleDecomposition reachFamilyC where
  rows := [TupleDispositionKind.scalar, TupleDispositionKind.matrix,
           TupleDispositionKind.status]
  rows_nonempty := by decide
  scalar_observer := payloadCountObserver reachFamilyC
  matrix_observer := payloadExposureMatrix_to_DWO
    (payloadExposureMatrix reachFamilyC)
  status_witness := True
  status_witness_holds := True.intro
  scalar_observer_eq := rfl
  matrix_observer_eq := rfl

/-- Row resolution on the reach family. -/
example (k : TupleDispositionKind) :
    k = TupleDispositionKind.scalar
      ∨ k = TupleDispositionKind.matrix
      ∨ k = TupleDispositionKind.status :=
  tupleDecomposition_to_scalar_or_matrix reachTupleDecompositionC k

/-- Phase C capstone reach check on the concrete reach family. -/
example :
    (∀ (i : reachFamilyC.schema.PayloadCoord)
       (t : reachFamilyC.schema.Term),
        (payloadExposureMatrix reachFamilyC).entry i t
          = reachFamilyC.schema.payloadCount i t)
      ∧ (∀ P : MatrixOverPolynomial reachFamilyC,
          ¬ reachFamilyC.GloballyOrients
              (payloadExposureMatrix_to_DWO P.matrix))
      ∧ (∀ (_D : TupleDecomposition reachFamilyC) (k : TupleDispositionKind),
          k = TupleDispositionKind.scalar
            ∨ k = TupleDispositionKind.matrix
            ∨ k = TupleDispositionKind.status) :=
  phaseC_vector_matrix_tuple_closed reachFamilyC True.intro

end OperatorKO7.StepDuplicating
