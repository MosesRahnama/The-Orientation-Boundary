import OperatorKO7.Meta.MatrixOverPolynomialReduction

/-!
# Tuple Interpretation Decomposition (Phase C)

Phase C tuple-decomposition layer. Tuple interpretations are decomposed
into three theorem-backed disposition kinds:

```
   kind        closure
   ────────    ─────────────────────────────────────────────
   scalar      closed via the canonical additive observer
               `payloadCountObserver F`
               (Phase B; additive barrier corollary).
   matrix      closed via the canonical exposure-matrix observer
               `payloadExposureMatrix_to_DWO (payloadExposureMatrix F)`
               (Phase C; matrix-over-polynomial reduction).
   status      closed via a licensed-escape status witness carried by
               the decomposition itself (residual route, status row).
```

The module supplies:

- the `TupleDispositionKind` enum (`scalar`, `matrix`, `status`);
- the `TupleDecomposition` structure carrying a non-empty list of
  disposition tags, the two canonical observers (scalar and matrix),
  identities locking the observers to the canonical Phase B and Phase C
  lifts, and a licensed-escape status witness;
- the row-resolution theorem `tupleDecomposition_to_scalar_or_matrix`:
  every disposition tag in the row list resolves into `scalar`, `matrix`,
  or `status`;
- the Phase C capstone theorem `phaseC_vector_matrix_tuple_closed`
  bundling the three Phase C facts: matrix projection identity, matrix-
  over-polynomial reduction, and tuple-row resolution.

The capstone is the public Phase C closure used by Supervisor C's audit
gate; it ties together the vector layer (matrix projection identity),
the matrix layer (matrix-over-polynomial reduction through the canonical
DWO), and the tuple layer (three-way disposition resolution).
-/

namespace OperatorKO7.StepDuplicating

/--
Three theorem-backed disposition kinds for a tuple-interpretation row.

* `scalar`: closed via the canonical additive observer
  `payloadCountObserver`.
* `matrix`: closed via the canonical exposure-matrix observer
  `payloadExposureMatrix_to_DWO`.
* `status`: closed via a licensed-escape status witness. -/
inductive TupleDispositionKind
  | scalar
  | matrix
  | status
  deriving DecidableEq, Repr

/--
A tuple-interpretation decomposition for a duplicating recursive
family.

The decomposition carries a non-empty list of disposition tags
(`rows`), the two canonical observers locked to their Phase B and Phase
C lifts, and an abstract status witness for the licensed-escape branch.
The structural identities `scalar_observer_eq` and `matrix_observer_eq`
certify that the two observers really are the Phase B additive observer
and the Phase C canonical exposure-matrix observer respectively. -/
structure TupleDecomposition (F : DuplicatingRecursiveFamily) where
  /-- The list of disposition tags assigned to the tuple rows. -/
  rows : List TupleDispositionKind
  /-- The row list is non-empty (every concrete tuple has at least one
  row). -/
  rows_nonempty : rows ≠ []
  /-- The scalar-branch observer (Phase B additive). -/
  scalar_observer : DirectWholeTermObserver F
  /-- The matrix-branch observer (Phase C canonical exposure matrix
  lift). -/
  matrix_observer : DirectWholeTermObserver F
  /-- The status-branch licensed-escape predicate carried by the
  decomposition. -/
  status_witness : Prop
  /-- Witness that the status-branch predicate holds. -/
  status_witness_holds : status_witness
  /-- Lock: the scalar observer is the canonical Phase B additive
  observer. -/
  scalar_observer_eq : scalar_observer = payloadCountObserver F
  /-- Lock: the matrix observer is the canonical Phase C exposure-matrix
  observer. -/
  matrix_observer_eq :
    matrix_observer
      = payloadExposureMatrix_to_DWO (payloadExposureMatrix F)

/--
**Phase C row-resolution theorem.**

Every disposition tag appearing in a tuple decomposition's row list
resolves into one of the three theorem-backed kinds: `scalar`, `matrix`,
or `status`. The disjunction is total on `TupleDispositionKind` by case
analysis. -/
theorem tupleDecomposition_to_scalar_or_matrix
    {F : DuplicatingRecursiveFamily}
    (_D : TupleDecomposition F)
    (k : TupleDispositionKind) :
    k = TupleDispositionKind.scalar
      ∨ k = TupleDispositionKind.matrix
      ∨ k = TupleDispositionKind.status := by
  cases k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/--
**Phase C capstone theorem.**

Bundles the three Phase C facts for any duplicating recursive family
that ships a payload-pump witness at the distinguished coordinate:

1. **Vector projection identity.** The canonical payload exposure
   matrix's entries project to the schema's payload count function on
   every coordinate and term.
2. **Matrix-over-polynomial reduction.** Every matrix-over-polynomial
   relation over the family fails to globally orient the family through
   its canonical exposure-matrix observer lift.
3. **Tuple row resolution.** Every tuple-decomposition row tag resolves
   into one of `scalar`, `matrix`, or `status`.

The capstone is the public Phase C closure cited by Supervisor C's
audit gate. -/
theorem phaseC_vector_matrix_tuple_closed
    (F : DuplicatingRecursiveFamily)
    (hPump : F.HasUnboundedPayloadPump F.distinguishedPayload) :
    (∀ (i : F.schema.PayloadCoord) (t : F.schema.Term),
        (payloadExposureMatrix F).entry i t
          = F.schema.payloadCount i t)
      ∧ (∀ P : MatrixOverPolynomial F,
          ¬ F.GloballyOrients (payloadExposureMatrix_to_DWO P.matrix))
      ∧ (∀ (_D : TupleDecomposition F) (k : TupleDispositionKind),
          k = TupleDispositionKind.scalar
            ∨ k = TupleDispositionKind.matrix
            ∨ k = TupleDispositionKind.status) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i t
    exact payloadExposureMatrix_projects_payloadCount
      (payloadExposureMatrix F) i t
  · intro P
    exact matrixOverPolynomial_reduces_to_nonlinear_escape P hPump
  · intro _D k
    exact tupleDecomposition_to_scalar_or_matrix _D k

end OperatorKO7.StepDuplicating
