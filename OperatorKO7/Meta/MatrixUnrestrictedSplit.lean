import OperatorKO7.Meta.MatrixUnrestrictedSplitCore
import OperatorKO7.Meta.MatrixResidualClosureCatalog

/-!
# Matrix Unrestricted Split -- Catalog Connection

The universal six-kind split is proved in the acyclic core module.  This file
connects that theorem to the residual catalog without introducing a circular
import.
-/

namespace OperatorKO7.MatrixUnrestrictedSplit

open OperatorKO7.MatrixResidualTaxonomy
open OperatorKO7.MatrixResidualClosureCatalog

/-- Both compatibility rows in the residual catalog are backed by the same
unconditional six-kind split theorem. -/
theorem unconstrainedRelation_rows_closed_by_unrestricted_split :
    matrixResidualClosureCatalogRowStatus
        MatrixResidualClosureCatalogRow.unconstrainedRelationLegacyScopeBoundary =
        MatrixClosureStatus.closedByUnrestrictedSplitFinalCatalog
    ∧ matrixResidualClosureCatalogRowStatus
        MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit =
        MatrixClosureStatus.closedByUnrestrictedSplitFinalCatalog
    ∧ matrixResidualClosureCatalogRowSupportKind
        MatrixResidualClosureCatalogRow.unconstrainedRelationLegacyScopeBoundary =
        MatrixResidualClosureSupportKind.closedByNamedTheorem
    ∧ matrixResidualClosureCatalogRowSupportKind
        MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit =
        MatrixResidualClosureSupportKind.closedByNamedTheorem
    ∧ (matrixCertificateKinds.length = 6
        ∧ MatrixUnrestrictedSplitFinalCatalog) := by
  exact ⟨rfl, rfl, rfl, rfl,
    matrixCertificateKinds_length,
    unrestricted_matrix_classes_split_final_catalog⟩

/-- Compatibility projection for the historically named closed row. -/
theorem unconstrainedRelation_row_closed_by_unrestricted_split :
    matrixResidualClosureCatalogRowStatus
      MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit
      = MatrixClosureStatus.closedByUnrestrictedSplitFinalCatalog
    ∧ matrixResidualClosureCatalogRowSupportKind
        MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit
      = MatrixResidualClosureSupportKind.closedByNamedTheorem
    ∧ matrixResidualClosureCatalogRowFamily
        MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit
      = MatrixResidualFamily.unconstrainedRelationClosed
    ∧ (matrixCertificateKinds.length = 6
        ∧ MatrixUnrestrictedSplitFinalCatalog) := by
  exact ⟨rfl, rfl, rfl,
    matrixCertificateKinds_length,
    unrestricted_matrix_classes_split_final_catalog⟩

/-- Engine audit anchor for the unconditional split theorem. -/
def matrix_unrestricted_classes_split_final_catalog_unconditional_anchor : String :=
  "OperatorKO7.MatrixUnrestrictedSplit." ++
    "unrestricted_matrix_classes_split_final_catalog_unconditional"

end OperatorKO7.MatrixUnrestrictedSplit
