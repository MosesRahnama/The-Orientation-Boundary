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

## Exact closed carrier of this module

The carrier here is deliberately narrow, and the docstrings below are written
to say exactly what it is rather than what a reader might hope it is.

- `MatrixOverPolynomial F` is a `PayloadExposureMatrix F` together with an
  **abstract** `crossCoupled : Prop` field and a witness for it. The field is
  a `Prop` slot supplied by the caller. It is *not* a polynomial, *not* a
  monomial table, and *not* an algebraic cross-coupling condition: the module
  never inspects it, no theorem below consumes it, and it is compatible with
  `crossCoupled := True`. The name records an intended reading; the type
  records a caller-supplied proposition.
- Consequently `matrixOverPolynomial_reduces_to_nonlinear_escape` and
  `matrixOverPolynomial_correspondence_certificate` hold for *every*
  `MatrixOverPolynomial`, including one whose `crossCoupled` slot is trivial.
  Their real content comes from `PayloadExposureMatrix.projects_payloadCount`
  and the supplied payload-pump witness, not from cross coupling.
- The barrier invoked is the Phase B theorem
  `no_direct_orientation_of_payload_exposure`, stated for the family's single
  rule instance `schema.lhs → schema.rhs` at the distinguished payload
  coordinate. Nothing here is a contextual-closure, `StepStar`, or
  multi-coordinate claim.

`Meta/PolynomialPayloadObserver.lean` supplies the concrete counterpart that
this module's abstract slot does not: a finite monomial-table evaluator over
payload-count coordinates, a typed `CrossCoupledMonomial` witness, an algebraic
`PolynomialPayloadDominates` predicate defined from coefficients, exponents,
and positive monomial support, a dominance-conditioned non-orientation theorem
that consumes that predicate, and an explicit orienting escape control
(`escapeTable_not_dominates`, `escapeTable_orients_pair`) showing the dominance
hypothesis is load-bearing for non-orientation. Readers wanting a cross-coupling claim with formal
content should cite that module rather than the `crossCoupled` field here.
-/

namespace OperatorKO7.StepDuplicating

/--
A matrix-over-polynomial relation over a `DuplicatingRecursiveFamily`.

The matrix layer is the underlying payload exposure matrix. The
`crossCoupled` field is an **abstract caller-supplied `Prop` slot**, not an
algebraic condition: no declaration in this module inspects or consumes it,
and `crossCoupled := True` inhabits it. It records an intended reading of the
matrix entries; it proves nothing about them. For a cross-coupling condition
with formal content, see `CrossCoupledMonomial` and
`PolynomialPayloadDominates` in `Meta/PolynomialPayloadObserver.lean`.
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
