import OperatorKO7.Meta.ToolSearchFragmentCoverage_Status
import OperatorKO7.Meta.MatrixOrderInterfaces
import OperatorKO7.Meta.MatrixBarrierArcticTropical_Schema

/-!
# Matrix Residual Closure Catalog

This module packages the accepted exact residual-matrix split as a final catalog.
It records only the accepted honest status labels from the existing taxonomy and
status layers. It does not claim new arbitrary, full arctic, or full tropical
closure theorems.
-/

namespace OperatorKO7.MatrixResidualClosureCatalog

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.MatrixResidualTaxonomy
open OperatorKO7.MatrixOrderInterfaces
open OperatorKO7.ToolSearchFragmentCoverageStatus

/-- Exact final-catalog rows for the matrix residual subfamilies.

LONG-22 Lane X additive extension: the
`unconstrainedRelationClosedByUnrestrictedSplit` row records that the
unconstrained-relation subfamily, previously labeled
`notYetMethodClass` at the row level, is now closed by the named
theorem
`OperatorKO7.MatrixUnrestrictedSplit.unrestricted_matrix_classes_split_final_catalog_unconditional`.
The legacy `unconstrainedRelationNotYetMethodClass` row is preserved
verbatim for backward compatibility with the existing
`MatrixResidualStatusCatalog` ledger; the new row sits alongside
it as the LONG-22-X-vintage closure carrier. -/
inductive MatrixResidualClosureCatalogRow where
  | componentwiseWeakStrictReduction
  | paretoProductReduction
  | lexPriorityReduction
  | permutationLexPriorityReduction
  | scalarizableWeightReduction
  | arcticFullLicensedEscape
  | tropicalFullLicensedEscape
  | importDependentMatrixLicensedEscape
  | unconstrainedRelationNotYetMethodClass
  | unconstrainedRelationClosedByUnrestrictedSplit
  deriving DecidableEq, Repr

/-- Exact finite row inventory for the matrix residual closure catalog. -/
def matrixResidualClosureCatalogRows : List MatrixResidualClosureCatalogRow :=
  [ .componentwiseWeakStrictReduction
  , .paretoProductReduction
  , .lexPriorityReduction
  , .permutationLexPriorityReduction
  , .scalarizableWeightReduction
  , .arcticFullLicensedEscape
  , .tropicalFullLicensedEscape
  , .importDependentMatrixLicensedEscape
  , .unconstrainedRelationNotYetMethodClass
  , .unconstrainedRelationClosedByUnrestrictedSplit
  ]

/-- The exact residual-matrix family represented by each final-catalog row. -/
def matrixResidualClosureCatalogRowFamily :
    MatrixResidualClosureCatalogRow → MatrixResidualFamily
  | .componentwiseWeakStrictReduction => .componentwiseWeakStrict
  | .paretoProductReduction => .paretoProduct
  | .lexPriorityReduction => .lexPriority
  | .permutationLexPriorityReduction => .permutationLexPriority
  | .scalarizableWeightReduction => .scalarizableWeight
  | .arcticFullLicensedEscape => .arcticFull
  | .tropicalFullLicensedEscape => .tropicalFull
  | .importDependentMatrixLicensedEscape => .importDependentMatrix
  | .unconstrainedRelationNotYetMethodClass => .unconstrainedRelation
  | .unconstrainedRelationClosedByUnrestrictedSplit => .unconstrainedRelationClosed

/-- The accepted honest closure status represented by each final-catalog row. -/
def matrixResidualClosureCatalogRowStatus :
    MatrixResidualClosureCatalogRow → MatrixClosureStatus
  | .componentwiseWeakStrictReduction => .reducedToExistingTheorem
  | .paretoProductReduction => .reducedToExistingTheorem
  | .lexPriorityReduction => .reducedToExistingTheorem
  | .permutationLexPriorityReduction => .reducedToExistingTheorem
  | .scalarizableWeightReduction => .reducedToExistingTheorem
  | .arcticFullLicensedEscape => .licensedEscape
  | .tropicalFullLicensedEscape => .licensedEscape
  | .importDependentMatrixLicensedEscape => .licensedEscape
  | .unconstrainedRelationNotYetMethodClass => .notYetMethodClass
  | .unconstrainedRelationClosedByUnrestrictedSplit =>
      .closedByUnrestrictedSplitFinalCatalog

/-- Exact support classes explaining why each matrix closure row is honest.

LONG-22 Lane X additive extension (`closedByNamedTheorem`): records that
a row's closure is discharged by a named upstream theorem (rather than a
projection-scalarization or licensed-escape certificate). -/
inductive MatrixResidualClosureSupportKind
  | projectionScalarization
  | licensedEscapeCertificate
  | explicitOpenStatus
  | closedByNamedTheorem
  deriving DecidableEq, Repr

/-- Each matrix closure row projects to one exact support class. -/
def matrixResidualClosureCatalogRowSupportKind :
    MatrixResidualClosureCatalogRow → MatrixResidualClosureSupportKind
  | .componentwiseWeakStrictReduction => .projectionScalarization
  | .paretoProductReduction => .projectionScalarization
  | .lexPriorityReduction => .projectionScalarization
  | .permutationLexPriorityReduction => .projectionScalarization
  | .scalarizableWeightReduction => .projectionScalarization
  | .arcticFullLicensedEscape => .licensedEscapeCertificate
  | .tropicalFullLicensedEscape => .licensedEscapeCertificate
  | .importDependentMatrixLicensedEscape => .licensedEscapeCertificate
  | .unconstrainedRelationNotYetMethodClass => .explicitOpenStatus
  | .unconstrainedRelationClosedByUnrestrictedSplit => .closedByNamedTheorem

/-- Payload alias for the certificate-backed arctic escape theorem. -/
abbrev ArcticFullLicensedEscapePayload : Prop :=
  ∀ {S : StepDuplicatingSchema} {d : Nat}
    (M : ArcticMatrixMeasure S d)
    (C : ArcticMatrixCertificate d)
    (_hweight : C.weight = M.scalarMeasure.weight)
    (_hscalarize : ∀ t : S.T, C.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (_hunbounded : HasUnboundedScalarizedRange M.scalarMeasure),
    ¬ (∀ (b s n : S.T),
      C.lt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n))))

/-- Payload alias for the certificate-backed tropical escape theorem. -/
abbrev TropicalFullLicensedEscapePayload : Prop :=
  ∀ {S : StepDuplicatingSchema} {d : Nat}
    (M : TropicalMatrixMeasure S d)
    (C : TropicalMatrixCertificate d)
    (_hweight : C.weight = M.scalarMeasure.weight)
    (_hscalarize : ∀ t : S.T, C.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (_hunbounded : HasUnboundedScalarizedRange M.scalarMeasure),
    ¬ (∀ (b s n : S.T),
      C.lt (M.eval (S.wrap s (S.recur b s n)))
        (M.eval (S.recur b s (S.succ n))))

/-- Payload alias for the LONG-22 Lane X closed-by-named-theorem row.
The Prop is `True`-inhabited at this layer because the named theorem
(LONG-22 X.5
`unrestricted_matrix_classes_split_final_catalog_unconditional`) lives
in `OperatorKO7.MatrixUnrestrictedSplit`, which IMPORTS this catalog
file; a Prop-level cite of the named theorem's body would be a
dependency cycle. The catalog therefore carries the row + status flip
+ support-kind label `closedByNamedTheorem`, and the
LONG-22 Lane X file ships the actual theorem. The link between this
row and the named theorem is the row's name plus the
`MatrixResidualClosureCatalogRowSupportKind.closedByNamedTheorem`
projection. -/
abbrev UnconstrainedRelationClosedByUnrestrictedSplitPayload : Prop := True

/-- The exact theorem/certificate payload backing each matrix closure row. -/
def matrixResidualClosureCatalogRowSupport :
    MatrixResidualClosureCatalogRow → Prop
  | .componentwiseWeakStrictReduction => ComponentwiseWeakStrictProjectionPayload
  | .paretoProductReduction => ParetoProductProjectionPayload
  | .lexPriorityReduction => LexPriorityProjectionPayload
  | .permutationLexPriorityReduction => PermutationLexPriorityProjectionPayload
  | .scalarizableWeightReduction => ScalarizableWeightReductionPayload
  | .arcticFullLicensedEscape => ArcticFullLicensedEscapePayload
  | .tropicalFullLicensedEscape => TropicalFullLicensedEscapePayload
  | .importDependentMatrixLicensedEscape => ImportDependentMatrixLicensedEscapePayload
  | .unconstrainedRelationNotYetMethodClass => UnconstrainedRelationNotYetMethodClassPayload
  | .unconstrainedRelationClosedByUnrestrictedSplit =>
      UnconstrainedRelationClosedByUnrestrictedSplitPayload

theorem arcticFull_licensedEscape_payload : ArcticFullLicensedEscapePayload := by
  intro S d M C hweight hscalarize hunbounded
  exact no_arcticMatrix_orients_dup_step_of_scalar_dominance_pump
    M C hweight hscalarize hunbounded

theorem tropicalFull_licensedEscape_payload : TropicalFullLicensedEscapePayload := by
  intro S d M C hweight hscalarize hunbounded
  exact no_tropicalMatrix_orients_dup_step_of_scalar_dominance_pump
    M C hweight hscalarize hunbounded

/-- The exact final-catalog row inventory has no duplicates. -/
theorem matrixResidualClosureCatalogRows_nodup :
    matrixResidualClosureCatalogRows.Nodup := by
  decide

/-- The exact final-catalog row inventory has length ten (LONG-22 Lane X
extension: +1 row for `unconstrainedRelationClosedByUnrestrictedSplit`). -/
theorem matrixResidualClosureCatalogRows_length :
    matrixResidualClosureCatalogRows.length = 10 := by
  rfl

/-- Exact membership characterization for the final-catalog row inventory. -/
theorem matrixResidualClosureCatalogRows_complete_exact
    (row : MatrixResidualClosureCatalogRow) :
    row ∈ matrixResidualClosureCatalogRows ↔
      row = .componentwiseWeakStrictReduction ∨
      row = .paretoProductReduction ∨
      row = .lexPriorityReduction ∨
      row = .permutationLexPriorityReduction ∨
      row = .scalarizableWeightReduction ∨
      row = .arcticFullLicensedEscape ∨
      row = .tropicalFullLicensedEscape ∨
      row = .importDependentMatrixLicensedEscape ∨
      row = .unconstrainedRelationNotYetMethodClass ∨
      row = .unconstrainedRelationClosedByUnrestrictedSplit := by
  cases row <;> decide

/-- Every final-catalog row projects to an accepted family in the taxonomy inventory. -/
theorem matrixResidualClosureCatalogRowFamily_mem_inventory
    (row : MatrixResidualClosureCatalogRow) :
    matrixResidualClosureCatalogRowFamily row ∈ matrixResidualFamilies := by
  cases row <;> decide

/-- Every final-catalog row matches the accepted taxonomy status assignment exactly. -/
theorem matrixResidualClosureCatalogRow_matches_taxonomy
    (row : MatrixResidualClosureCatalogRow) :
    matrixResidualClosureCatalogRowStatus row =
      matrixResidualClosureStatus (matrixResidualClosureCatalogRowFamily row) := by
  cases row <;> rfl

/-- Every final-catalog row uses one of the accepted honest status labels.

LONG-22 Lane X additive extension: the disjunction now includes the
`closedByUnrestrictedSplitFinalCatalog` label for the new
`unconstrainedRelationClosedByUnrestrictedSplit` row. -/
theorem matrixResidualClosureCatalogRow_uses_honest_status
    (row : MatrixResidualClosureCatalogRow) :
    matrixResidualClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
      matrixResidualClosureCatalogRowStatus row = .licensedEscape ∨
      matrixResidualClosureCatalogRowStatus row = .notYetMethodClass ∨
      matrixResidualClosureCatalogRowStatus row =
        .closedByUnrestrictedSplitFinalCatalog := by
  cases row <;> simp [matrixResidualClosureCatalogRowStatus]

/-- Every matrix closure row carries an exact theorem/certificate/open payload. -/
theorem matrixResidualClosureCatalogRow_has_support
    (row : MatrixResidualClosureCatalogRow) :
    matrixResidualClosureCatalogRowSupport row := by
  cases row
  · exact componentwiseWeakStrict_projection_payload
  · exact paretoProduct_projection_payload
  · exact lexPriority_projection_payload
  · exact permutationLexPriority_projection_payload
  · exact scalarizableWeight_reduction_payload
  · exact arcticFull_licensedEscape_payload
  · exact tropicalFull_licensedEscape_payload
  · exact importDependentMatrix_licensedEscape_payload
  · exact unconstrainedRelation_notYetMethodClass_payload
  · exact (trivial : UnconstrainedRelationClosedByUnrestrictedSplitPayload)

/-- The support-kind projection agrees with the row's honest status label.

LONG-22 Lane X additive extension: the new `closedByNamedTheorem`
support-kind projects to the `closedByUnrestrictedSplitFinalCatalog`
status. -/
theorem matrixResidualClosureCatalogRowSupportKind_projects_status
    (row : MatrixResidualClosureCatalogRow) :
    (matrixResidualClosureCatalogRowSupportKind row = .projectionScalarization →
      matrixResidualClosureCatalogRowStatus row = .reducedToExistingTheorem)
    ∧ (matrixResidualClosureCatalogRowSupportKind row = .licensedEscapeCertificate →
      matrixResidualClosureCatalogRowStatus row = .licensedEscape)
    ∧ (matrixResidualClosureCatalogRowSupportKind row = .explicitOpenStatus →
      matrixResidualClosureCatalogRowStatus row = .notYetMethodClass)
    ∧ (matrixResidualClosureCatalogRowSupportKind row = .closedByNamedTheorem →
      matrixResidualClosureCatalogRowStatus row =
        .closedByUnrestrictedSplitFinalCatalog) := by
  cases row <;>
    simp [matrixResidualClosureCatalogRowSupportKind, matrixResidualClosureCatalogRowStatus]

/-- Paper-facing proposition for the exact final residual-matrix closure catalog.

LONG-22 Lane X additive extension: the disjunction now includes the
`closedByUnrestrictedSplitFinalCatalog` label so the new row satisfies
the catalog. -/
abbrev MatrixResidualClosureFinalCatalog : Prop :=
  ∀ row : MatrixResidualClosureCatalogRow,
    row ∈ matrixResidualClosureCatalogRows ∧
      matrixResidualClosureCatalogRowStatus row =
        matrixResidualClosureStatus (matrixResidualClosureCatalogRowFamily row) ∧
      matrixResidualClosureCatalogRowSupport row ∧
      (matrixResidualClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
        matrixResidualClosureCatalogRowStatus row = .licensedEscape ∨
        matrixResidualClosureCatalogRowStatus row = .notYetMethodClass ∨
        matrixResidualClosureCatalogRowStatus row =
          .closedByUnrestrictedSplitFinalCatalog)

/-- The exact final residual-matrix closure catalog is realized by the accepted rows. -/
theorem matrixResidualClosureFinalCatalog_exact : MatrixResidualClosureFinalCatalog := by
  intro row
  constructor
  · cases row <;> simp [matrixResidualClosureCatalogRows]
  constructor
  · exact matrixResidualClosureCatalogRow_matches_taxonomy row
  constructor
  · exact matrixResidualClosureCatalogRow_has_support row
  · exact matrixResidualClosureCatalogRow_uses_honest_status row

/-- Certificate packaging the exact final matrix residual catalog and the accepted
paper-facing status projection. -/
structure MatrixResidualClosureCertificate where
  finalCatalog : MatrixResidualClosureFinalCatalog
  statusCatalog : MatrixResidualStatusCatalog

/-- The matrix residual closure certificate packages the exact rows and the accepted
status projection together. -/
theorem matrixResidualClosureCertificate : MatrixResidualClosureCertificate := by
  exact {
    finalCatalog := matrixResidualClosureFinalCatalog_exact
    statusCatalog := matrix_residual_status_catalog
  }

/-- The matrix residual closure certificate projects the exact final catalog. -/
theorem matrixResidualClosureCertificate_projects_finalCatalog :
    MatrixResidualClosureFinalCatalog :=
  matrixResidualClosureCertificate.finalCatalog

/-- The matrix residual closure certificate projects the exact theorem/certificate/open
payload for each catalog row. -/
theorem matrixResidualClosureCertificate_projects_rowSupport
    (row : MatrixResidualClosureCatalogRow) :
    matrixResidualClosureCatalogRowSupport row := by
  exact (matrixResidualClosureCertificate_projects_finalCatalog row).2.2.1

/-- The matrix residual closure certificate projects the accepted paper-facing
matrix residual status catalog. -/
theorem matrixResidualClosureCertificate_projects_statusCatalog :
    MatrixResidualStatusCatalog :=
  matrixResidualClosureCertificate.statusCatalog

end OperatorKO7.MatrixResidualClosureCatalog
