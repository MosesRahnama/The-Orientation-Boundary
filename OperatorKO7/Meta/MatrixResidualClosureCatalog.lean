import OperatorKO7.Meta.ToolSearchFragmentCoverage_Status
import OperatorKO7.Meta.MatrixOrderInterfaces
import OperatorKO7.Meta.MatrixBarrierArcticTropical_Schema
import OperatorKO7.Meta.MatrixUnrestrictedSplitCore

/-!
# Matrix residual closure catalog

This ten-row catalog is theorem-backed throughout.  The two compatibility rows
for the formerly unconstrained relation both carry the unconditional six-kind
split proved in `MatrixUnrestrictedSplitCore`; no row is supported by `True` and
no live row has an open or not-yet-method-class status.
-/

namespace OperatorKO7.MatrixResidualClosureCatalog

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.MatrixResidualTaxonomy
open OperatorKO7.MatrixOrderInterfaces
open OperatorKO7.ToolSearchFragmentCoverageStatus
open OperatorKO7.MatrixUnrestrictedSplit

/-- Rows of the finite residual-matrix status catalog.

The two compatibility rows both point to the theorem-backed
`unconstrainedRelationClosed` family.  One preserves the location of the former
legacy row; the other preserves the explicitly named closed row. -/
inductive MatrixResidualClosureCatalogRow where
  | componentwiseWeakStrictReduction
  | paretoProductReduction
  | lexPriorityReduction
  | permutationLexPriorityReduction
  | scalarizableWeightReduction
  | arcticFullLicensedEscape
  | tropicalFullLicensedEscape
  | importDependentMatrixLicensedEscape
  | unconstrainedRelationLegacyScopeBoundary
  | unconstrainedRelationClosedByUnrestrictedSplit
  deriving DecidableEq, Repr

/-- Ten-row inventory for the matrix residual status catalog. -/
def matrixResidualClosureCatalogRows : List MatrixResidualClosureCatalogRow :=
  [ .componentwiseWeakStrictReduction
  , .paretoProductReduction
  , .lexPriorityReduction
  , .permutationLexPriorityReduction
  , .scalarizableWeightReduction
  , .arcticFullLicensedEscape
  , .tropicalFullLicensedEscape
  , .importDependentMatrixLicensedEscape
  , .unconstrainedRelationLegacyScopeBoundary
  , .unconstrainedRelationClosedByUnrestrictedSplit
  ]

/-- Family label assigned to each row. -/
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
  | .unconstrainedRelationLegacyScopeBoundary => .unconstrainedRelationClosed
  | .unconstrainedRelationClosedByUnrestrictedSplit => .unconstrainedRelationClosed

/-- Status label assigned to each row. -/
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
  | .unconstrainedRelationLegacyScopeBoundary =>
      .closedByUnrestrictedSplitFinalCatalog
  | .unconstrainedRelationClosedByUnrestrictedSplit =>
      .closedByUnrestrictedSplitFinalCatalog

/-- Three support-kind labels; the proof itself is carried by `matrixResidualClosureCatalogRowSupport`. -/
inductive MatrixResidualClosureSupportKind
  | projectionScalarization
  | licensedEscapeCertificate
  | closedByNamedTheorem
  deriving DecidableEq, Repr

/-- Support-kind label assigned to each row. -/
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
  | .unconstrainedRelationLegacyScopeBoundary => .closedByNamedTheorem
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

/-- Exact payload of the unconditional six-kind matrix split. -/
abbrev UnconstrainedRelationClosedByUnrestrictedSplitPayload : Prop :=
  matrixCertificateKinds.length = 6
    ∧ matrixCertificateKinds.Nodup
    ∧ MatrixUnrestrictedSplitFinalCatalog
    ∧ (∀ M : MatrixRelation, ∃! kind : MatrixCertificateKind,
        matrixRelationKind M = kind)

/-- Proposition assigned as support for each row. Both final branches carry the six-kind split theorem. -/
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
  | .unconstrainedRelationLegacyScopeBoundary =>
      UnconstrainedRelationClosedByUnrestrictedSplitPayload
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

/-- The ten-row inventory has no duplicates. -/
theorem matrixResidualClosureCatalogRows_nodup :
    matrixResidualClosureCatalogRows.Nodup := by
  decide

/-- The row inventory has length ten. -/
theorem matrixResidualClosureCatalogRows_length :
    matrixResidualClosureCatalogRows.length = 10 := by
  rfl

/-- Membership characterization for the row inventory. -/
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
      row = .unconstrainedRelationLegacyScopeBoundary ∨
      row = .unconstrainedRelationClosedByUnrestrictedSplit := by
  cases row <;> decide

/-- Every row's assigned family belongs to the imported family inventory. -/
theorem matrixResidualClosureCatalogRowFamily_mem_inventory
    (row : MatrixResidualClosureCatalogRow) :
    matrixResidualClosureCatalogRowFamily row ∈ matrixResidualFamilies := by
  cases row <;> decide

/-- Each row's status assignment agrees definitionally with the imported taxonomy function. -/
theorem matrixResidualClosureCatalogRow_matches_taxonomy
    (row : MatrixResidualClosureCatalogRow) :
    matrixResidualClosureCatalogRowStatus row =
      matrixResidualClosureStatus (matrixResidualClosureCatalogRowFamily row) := by
  cases row <;> rfl

/-- Every live row has a theorem-reduction, licensed-escape, or exact
unrestricted-split status. -/
theorem matrixResidualClosureCatalogRow_uses_honest_status
    (row : MatrixResidualClosureCatalogRow) :
    matrixResidualClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
      matrixResidualClosureCatalogRowStatus row = .licensedEscape ∨
      matrixResidualClosureCatalogRowStatus row =
        .closedByUnrestrictedSplitFinalCatalog := by
  cases row <;> simp [matrixResidualClosureCatalogRowStatus]

/-- Every row's assigned support proposition is inhabited by a theorem-backed payload. -/
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
  · exact unrestricted_matrix_classes_split_final_catalog_unconditional
  · exact unrestricted_matrix_classes_split_final_catalog_unconditional

/-- Support-kind labels project to their theorem-backed status classes. -/
theorem matrixResidualClosureCatalogRowSupportKind_projects_status
    (row : MatrixResidualClosureCatalogRow) :
    (matrixResidualClosureCatalogRowSupportKind row = .projectionScalarization →
      matrixResidualClosureCatalogRowStatus row = .reducedToExistingTheorem)
    ∧ (matrixResidualClosureCatalogRowSupportKind row = .licensedEscapeCertificate →
      matrixResidualClosureCatalogRowStatus row = .licensedEscape)
    ∧ (matrixResidualClosureCatalogRowSupportKind row = .closedByNamedTheorem →
      matrixResidualClosureCatalogRowStatus row =
        .closedByUnrestrictedSplitFinalCatalog) := by
  cases row <;>
    simp [matrixResidualClosureCatalogRowSupportKind,
      matrixResidualClosureCatalogRowStatus]

/-- Finite metadata predicate combining row membership, definitional status agreement, inhabited
support, and membership in the four-label status disjunction. -/
abbrev MatrixResidualClosureFinalCatalog : Prop :=
  ∀ row : MatrixResidualClosureCatalogRow,
    row ∈ matrixResidualClosureCatalogRows ∧
      matrixResidualClosureCatalogRowStatus row =
        matrixResidualClosureStatus (matrixResidualClosureCatalogRowFamily row) ∧
      matrixResidualClosureCatalogRowSupport row ∧
      (matrixResidualClosureCatalogRowStatus row = .reducedToExistingTheorem ∨
        matrixResidualClosureCatalogRowStatus row = .licensedEscape ∨
        matrixResidualClosureCatalogRowStatus row =
          .closedByUnrestrictedSplitFinalCatalog)

/-- The finite metadata predicate holds for every row by enumeration and the assigned support proofs. -/
theorem matrixResidualClosureFinalCatalog_exact : MatrixResidualClosureFinalCatalog := by
  intro row
  constructor
  · cases row <;> simp [matrixResidualClosureCatalogRows]
  constructor
  · exact matrixResidualClosureCatalogRow_matches_taxonomy row
  constructor
  · exact matrixResidualClosureCatalogRow_has_support row
  · exact matrixResidualClosureCatalogRow_uses_honest_status row

/-- Pair of the finite metadata catalog proof and the imported status catalog. -/
structure MatrixResidualClosureCertificate where
  finalCatalog : MatrixResidualClosureFinalCatalog
  statusCatalog : MatrixResidualStatusCatalog

/-- Construct the pair from the two catalog proofs. -/
theorem matrixResidualClosureCertificate : MatrixResidualClosureCertificate := by
  exact {
    finalCatalog := matrixResidualClosureFinalCatalog_exact
    statusCatalog := matrix_residual_status_catalog
  }

/-- Project the finite metadata catalog proof. -/
theorem matrixResidualClosureCertificate_projects_finalCatalog :
    MatrixResidualClosureFinalCatalog :=
  matrixResidualClosureCertificate.finalCatalog

/-- Project the assigned support proposition for a row. -/
theorem matrixResidualClosureCertificate_projects_rowSupport
    (row : MatrixResidualClosureCatalogRow) :
    matrixResidualClosureCatalogRowSupport row := by
  exact (matrixResidualClosureCertificate_projects_finalCatalog row).2.2.1

/-- Project the imported matrix residual status catalog. -/
theorem matrixResidualClosureCertificate_projects_statusCatalog :
    MatrixResidualStatusCatalog :=
  matrixResidualClosureCertificate.statusCatalog

end OperatorKO7.MatrixResidualClosureCatalog
