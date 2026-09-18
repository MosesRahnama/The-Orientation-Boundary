import OperatorKO7.Meta.DirectWholeTermObserver

/-!
# Payload Exposure Matrix (Phase C)

Phase C of the recursive-family expansion roadmap. This module introduces
the payload exposure matrix layer: a coordinate-indexed table of payload
counts together with a structural certificate that the table's rows
project to `schema.payloadCount` and a canonical lift of the matrix to a
`DirectWholeTermObserver`.

The module supplies:

- the `PayloadExposureMatrix` structure carrying one `Nat`-valued entry per
  payload coordinate and term, together with a `projects_payloadCount`
  certificate;
- the canonical exposure matrix `payloadExposureMatrix F` whose entries
  are exactly `F.schema.payloadCount`;
- the projection theorem `payloadExposureMatrix_projects_payloadCount`
  exposing the row identity;
- the canonical lift `payloadExposureMatrix_to_DWO` producing a
  `DirectWholeTermObserver` whose `eval` is the matrix entry at the
  family's distinguished payload coordinate, whose strict order is the
  natural number strict order, and whose `orient_forces_payload_drop`
  certificate is discharged via the matrix's projection identity.

The Phase B `DirectWholeTermObserver` barrier theorem applies to the
canonical lift without any additional theorem-local bridge hypothesis,
because the matrix projection identity rewrites the observer's strict
comparison to the schema's payload-count strict comparison verbatim.
-/

namespace OperatorKO7.StepDuplicating

/--
A payload exposure matrix over a `DuplicatingRecursiveFamily` records
one `Nat`-valued entry per pair of payload coordinate and term carrier.

The structural certificate `projects_payloadCount` certifies that this
table's row at coordinate `i` and term `t` equals `schema.payloadCount i t`.
Concrete matrices populated by per-class direct measures discharge this
certificate by exhibiting the row identity directly. -/
structure PayloadExposureMatrix (F : DuplicatingRecursiveFamily) where
  /-- The matrix entry at coordinate `i` and term `t`. -/
  entry : F.schema.PayloadCoord → F.schema.Term → Nat
  /-- Structural certificate: the matrix row at coordinate `i` and term
  `t` projects to the schema's payload count at coordinate `i` and term
  `t`. The canonical exposure matrix has `entry = schema.payloadCount`,
  in which case the certificate is `rfl`. -/
  projects_payloadCount :
    ∀ (i : F.schema.PayloadCoord) (t : F.schema.Term),
      entry i t = F.schema.payloadCount i t

/--
The canonical payload exposure matrix: every entry is exactly the
schema's payload count function. The projection certificate is `rfl`. -/
def payloadExposureMatrix (F : DuplicatingRecursiveFamily) :
    PayloadExposureMatrix F where
  entry := fun i t => F.schema.payloadCount i t
  projects_payloadCount := fun _ _ => rfl

/--
The projection identity: the matrix entry at coordinate `i` and term
`t` equals the schema's payload count at coordinate `i` of term `t`.
Direct restatement of the structural certificate carried by every
`PayloadExposureMatrix`. -/
theorem payloadExposureMatrix_projects_payloadCount
    {F : DuplicatingRecursiveFamily}
    (M : PayloadExposureMatrix F)
    (i : F.schema.PayloadCoord) (t : F.schema.Term) :
    M.entry i t = F.schema.payloadCount i t :=
  M.projects_payloadCount i t

/--
Canonical lift of a payload exposure matrix to a direct whole-term
observer.

The observer's carrier is `Nat`; the evaluator is the matrix entry at
the family's distinguished payload coordinate; the strict order is the
natural-number strict order; visibility and carrier sensitivity fire
exactly on the distinguished coordinate; `constructorLocal` and
`pumpMonotone` are set to `True`.

The structural certificate `orient_forces_payload_drop` is discharged
by case-analyzing the visibility witness (a propositional equality `i =
F.distinguishedPayload`) and rewriting the observer's strict comparison
to the schema's payload-count strict comparison via the matrix's
projection identity. -/
def payloadExposureMatrix_to_DWO {F : DuplicatingRecursiveFamily}
    (M : PayloadExposureMatrix F) :
    DirectWholeTermObserver F where
  Carrier := Nat
  eval := fun t => M.entry F.distinguishedPayload t
  lt := fun m n => m < n
  visiblePayloadCoordinate := fun p => p = F.distinguishedPayload
  carrierSensitive := fun p => p = F.distinguishedPayload
  constructorLocal := True
  pumpMonotone := fun _ => True
  orient_forces_payload_drop := by
    intro i hVisible _hSensitive hOriented
    -- `hVisible : i = F.distinguishedPayload`; rewrite `i` to the
    -- distinguished coordinate.
    cases hVisible
    -- Now `hOriented : M.entry F.distinguishedPayload F.schema.rhs <
    -- M.entry F.distinguishedPayload F.schema.lhs`. Rewrite both sides
    -- via the matrix's projection identity to reduce to the schema's
    -- payload-count strict comparison.
    have hL :
        M.entry F.distinguishedPayload F.schema.lhs
          = F.schema.payloadCount F.distinguishedPayload F.schema.lhs :=
      M.projects_payloadCount _ _
    have hR :
        M.entry F.distinguishedPayload F.schema.rhs
          = F.schema.payloadCount F.distinguishedPayload F.schema.rhs :=
      M.projects_payloadCount _ _
    rw [hL, hR] at hOriented
    exact hOriented

end OperatorKO7.StepDuplicating
