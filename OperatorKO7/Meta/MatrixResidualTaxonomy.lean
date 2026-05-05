namespace OperatorKO7.MatrixResidualTaxonomy

/-- Exact residual matrix subfamilies replacing the old opaque residual label.

LONG-22 Lane X additive extension (`unconstrainedRelationClosed`):
records that the unconstrained relation has a separate closed-by-
named-theorem family of its own under the LONG-22 X.5 unrestricted-
split final catalog. The legacy `unconstrainedRelation` constructor is
preserved verbatim (downstream `MatrixResidualStatusCatalog` continues
to assert the legacy `notYetMethodClass` status against it). -/
inductive MatrixResidualFamily
  | componentwiseWeakStrict
  | paretoProduct
  | lexPriority
  | permutationLexPriority
  | scalarizableWeight
  | arcticFull
  | tropicalFull
  | importDependentMatrix
  | unconstrainedRelation
  | unconstrainedRelationClosed
  deriving DecidableEq, Repr

/-- Procedure-grade closure labels for exact residual matrix subfamilies.

LONG-22 Lane X additive extension (`closedByUnrestrictedSplitFinalCatalog`):
records that a residual family previously labeled `notYetMethodClass`
has been promoted to a closed-by-named-theorem state by Lane X's
`unrestricted_matrix_classes_split_final_catalog_unconditional`. The
existing five constructors are preserved verbatim; the family-level
status function `matrixResidualClosureStatus` is unchanged for backward
compatibility (downstream consumers in
`ToolSearchFragmentCoverage_Status.MatrixResidualStatusCatalog` continue
to assert `unconstrainedRelation = .notYetMethodClass`). The new
constructor surfaces only at the catalog-row layer, where Lane X adds a
sibling row for the unrestricted-split closure. -/
inductive MatrixClosureStatus
  | blocked
  | reducedToExistingTheorem
  | certifiedSuccess
  | licensedEscape
  | notYetMethodClass
  | closedByUnrestrictedSplitFinalCatalog
  deriving DecidableEq, Repr

/-- Exact finite inventory of residual matrix subfamilies. -/
def matrixResidualFamilies : List MatrixResidualFamily :=
  [ .componentwiseWeakStrict
  , .paretoProduct
  , .lexPriority
  , .permutationLexPriority
  , .scalarizableWeight
  , .arcticFull
  , .tropicalFull
  , .importDependentMatrix
  , .unconstrainedRelation
  , .unconstrainedRelationClosed
  ]

/-- Current closure-status catalog for the exact residual matrix split. -/
def matrixResidualClosureStatus : MatrixResidualFamily → MatrixClosureStatus
  | .componentwiseWeakStrict => .reducedToExistingTheorem
  | .paretoProduct => .reducedToExistingTheorem
  | .lexPriority => .reducedToExistingTheorem
  | .permutationLexPriority => .reducedToExistingTheorem
  | .scalarizableWeight => .reducedToExistingTheorem
  | .arcticFull => .licensedEscape
  | .tropicalFull => .licensedEscape
  | .importDependentMatrix => .licensedEscape
  | .unconstrainedRelation => .notYetMethodClass
  | .unconstrainedRelationClosed => .closedByUnrestrictedSplitFinalCatalog

theorem matrixResidualFamilies_nodup : matrixResidualFamilies.Nodup := by
  decide

theorem matrixResidualFamilies_length : matrixResidualFamilies.length = 10 := by
  decide

theorem matrixResidualFamilies_complete_exact
    (family : MatrixResidualFamily) :
    family ∈ matrixResidualFamilies ↔
      family = .componentwiseWeakStrict ∨
      family = .paretoProduct ∨
      family = .lexPriority ∨
      family = .permutationLexPriority ∨
      family = .scalarizableWeight ∨
      family = .arcticFull ∨
      family = .tropicalFull ∨
      family = .importDependentMatrix ∨
      family = .unconstrainedRelation ∨
      family = .unconstrainedRelationClosed := by
  cases family <;> decide

theorem matrixResidualClosureStatus_catalog :
    matrixResidualClosureStatus .componentwiseWeakStrict = .reducedToExistingTheorem ∧
    matrixResidualClosureStatus .paretoProduct = .reducedToExistingTheorem ∧
    matrixResidualClosureStatus .lexPriority = .reducedToExistingTheorem ∧
    matrixResidualClosureStatus .permutationLexPriority = .reducedToExistingTheorem ∧
    matrixResidualClosureStatus .scalarizableWeight = .reducedToExistingTheorem ∧
    matrixResidualClosureStatus .arcticFull = .licensedEscape ∧
    matrixResidualClosureStatus .tropicalFull = .licensedEscape ∧
    matrixResidualClosureStatus .importDependentMatrix = .licensedEscape ∧
    matrixResidualClosureStatus .unconstrainedRelation = .notYetMethodClass := by
  decide

theorem matrixResidualClosureStatus_unconstrainedRelationClosed :
    matrixResidualClosureStatus .unconstrainedRelationClosed =
      .closedByUnrestrictedSplitFinalCatalog := by
  rfl

end OperatorKO7.MatrixResidualTaxonomy
