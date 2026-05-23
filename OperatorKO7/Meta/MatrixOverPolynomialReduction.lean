import OperatorKO7.Meta.PayloadExposureMatrix

/-!
# Matrix-over-Polynomial Reduction to Nonlinear Escape (Phase C)

Phase C reduction layer. This module introduces the matrix-over-polynomial
relation surface and its correspondence to the nonlinear-escape surface of
the family barrier.

The module supplies:

- the `MatrixOverPolynomial` structure: a payload exposure matrix
  packaged with an abstract `crossCoupled` predicate witness recording
  that the matrix entries are derived from polynomial cross-coupling of
  payload counts;
- the reduction theorem `matrixOverPolynomial_reduces_to_nonlinear_escape`:
  given a payload pump witness on the family's distinguished coordinate,
  the canonical `DirectWholeTermObserver` induced by the matrix cannot
  globally orient the family. The reduction projects through
  `payloadExposureMatrix_to_DWO` and applies the Phase B barrier
  theorem `no_direct_orientation_of_payload_exposure` without any
  theorem-local bridge hypothesis;
- the correspondence certificate
  `matrixOverPolynomial_correspondence_certificate`: the certificate
  packages the non-orientation conclusion together with the projection
  identity that the matrix entries project to `schema.payloadCount`.

The reduction is constructive: every matrix-over-polynomial admits its
canonical exposure-matrix projection as the explicit nonlinear-escape
package, and the barrier holds verbatim through the projection.
-/

namespace OperatorKO7.StepDuplicating

/--
A matrix-over-polynomial relation over a `DuplicatingRecursiveFamily`.

The matrix layer is the underlying payload exposure matrix; the
`crossCoupled` predicate is an abstract carrier for the matrix-over-
polynomial cross-coupling commitment (concrete instances supply a
witness such as "entries are polynomial in payload counts across
multiple coordinates"); `crossCoupled_witness` discharges the predicate.
-/
structure MatrixOverPolynomial (F : DuplicatingRecursiveFamily) where
  /-- The underlying payload exposure matrix. -/
  matrix : PayloadExposureMatrix F
  /-- Abstract cross-coupling predicate carried by the relation. -/
  crossCoupled : Prop
  /-- Witness that the cross-coupling predicate holds. -/
  crossCoupled_witness : crossCoupled

/--
**Phase C reduction theorem.**

Every matrix-over-polynomial reduces to the nonlinear-escape surface:
its canonical `DirectWholeTermObserver` lift through
`payloadExposureMatrix_to_DWO` cannot globally orient the family. The
reduction consumes a payload-pump witness on the family's distinguished
coordinate and invokes the Phase B barrier theorem
`no_direct_orientation_of_payload_exposure` at the distinguished
coordinate; visibility and carrier sensitivity reduce to `rfl` for the
canonical lift, and `orient_forces_payload_drop` is discharged by the
matrix's projection identity inside the lift. -/
theorem matrixOverPolynomial_reduces_to_nonlinear_escape
    {F : DuplicatingRecursiveFamily} (P : MatrixOverPolynomial F)
    (hPump : F.HasUnboundedPayloadPump F.distinguishedPayload) :
    ¬ F.GloballyOrients (payloadExposureMatrix_to_DWO P.matrix) :=
  no_direct_orientation_of_payload_exposure
    (payloadExposureMatrix_to_DWO P.matrix)
    (i := F.distinguishedPayload)
    hPump
    F.distinguished_exposed
    (rfl)
    (rfl)

/--
**Phase C correspondence certificate.**

The packaged correspondence between a matrix-over-polynomial and the
nonlinear-escape surface: the canonical lift through
`payloadExposureMatrix_to_DWO` cannot globally orient the family
(reduction theorem), and the matrix's entries project to
`schema.payloadCount` on every coordinate and term (projection
identity). The certificate bundles both facts so downstream consumers
need not re-derive them. -/
theorem matrixOverPolynomial_correspondence_certificate
    {F : DuplicatingRecursiveFamily} (P : MatrixOverPolynomial F)
    (hPump : F.HasUnboundedPayloadPump F.distinguishedPayload) :
    (¬ F.GloballyOrients (payloadExposureMatrix_to_DWO P.matrix))
      ∧ (∀ (i : F.schema.PayloadCoord) (t : F.schema.Term),
          P.matrix.entry i t = F.schema.payloadCount i t) :=
  ⟨matrixOverPolynomial_reduces_to_nonlinear_escape P hPump,
   P.matrix.projects_payloadCount⟩

end OperatorKO7.StepDuplicating
