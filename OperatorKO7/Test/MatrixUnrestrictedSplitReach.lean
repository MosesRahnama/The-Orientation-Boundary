import OperatorKO7.Meta.MatrixUnrestrictedSplit

/-!
# Reach test for `Meta/MatrixUnrestrictedSplit.lean`

Per `.agent-control/COMPLETION_PROTOCOL.md` the reach test serves as the
live-demo gate for theorem-side lanes. Asserts the headline theorem
X.5 and the per-kind theorem X.3 by name; checks the
`MatrixCertificateKind` enum has all six expected constructors; checks
the audit anchor string equality.
-/

namespace MatrixUnrestrictedSplitReach

open OperatorKO7.MatrixResidualTaxonomy
open OperatorKO7.MatrixResidualClosureCatalog
open OperatorKO7.MatrixUnrestrictedSplit

#check @MatrixCertificateKind
#check matrixCertificateKinds
#check matrixCertificateKinds_nodup
#check matrixCertificateKinds_length
#check @matrixCertificateKinds_complete_exact
#check @RowColumnDominanceOrder
#check @ConePositiveOrder
#check @SpectralNormOrder
#check @NonScalarizableOrder
#check @RowColumnDominancePayload
#check @ConePositivePayload
#check @SpectralNormPayload
#check @NonScalarizablePayload
#check @ArcticTropicalLicensedEscapePayload
#check @matrixCertificateKindUnconditionallyClosed
#check @matrix_unrestricted_class_blocked_unconditional_for_kind
#check @MatrixRelation
#check @matrixRelationKind
#check @matrix_certificate_classification
#check @MatrixUnrestrictedSplitFinalCatalog
#check @unrestricted_matrix_classes_split_final_catalog
#check @unrestricted_matrix_classes_split_final_catalog_unconditional
#check @unconstrainedRelation_row_closed_by_unrestricted_split
#check matrix_unrestricted_classes_split_final_catalog_unconditional_anchor

example : matrixCertificateKinds.length = 6 :=
  matrixCertificateKinds_length

example : matrixCertificateKinds.Nodup :=
  matrixCertificateKinds_nodup

example : MatrixCertificateKind.scalarizable ∈ matrixCertificateKinds := by
  decide

example : MatrixCertificateKind.arcticTropical ∈ matrixCertificateKinds := by
  decide

example : MatrixCertificateKind.nonScalarizable ∈ matrixCertificateKinds := by
  decide

example (kind : MatrixCertificateKind) :
    matrixCertificateKindUnconditionallyClosed kind :=
  matrix_unrestricted_class_blocked_unconditional_for_kind kind

example :
    matrixCertificateKinds.length = 6
    ∧ matrixCertificateKinds.Nodup
    ∧ MatrixUnrestrictedSplitFinalCatalog
    ∧ (∀ M : MatrixRelation, ∃! kind : MatrixCertificateKind,
        matrixRelationKind M = kind) :=
  unrestricted_matrix_classes_split_final_catalog_unconditional

example : matrixResidualClosureCatalogRowStatus
    MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit
    = MatrixClosureStatus.closedByUnrestrictedSplitFinalCatalog :=
  rfl

example : matrixResidualClosureCatalogRowSupportKind
    MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit
    = MatrixResidualClosureSupportKind.closedByNamedTheorem :=
  rfl

example : matrixResidualClosureCatalogRowFamily
    MatrixResidualClosureCatalogRow.unconstrainedRelationClosedByUnrestrictedSplit
    = MatrixResidualFamily.unconstrainedRelationClosed :=
  rfl

example : matrixResidualClosureStatus
    MatrixResidualFamily.unconstrainedRelationClosed
    = MatrixClosureStatus.closedByUnrestrictedSplitFinalCatalog :=
  rfl

example : matrix_unrestricted_classes_split_final_catalog_unconditional_anchor =
    "OperatorKO7.MatrixUnrestrictedSplit." ++
      "unrestricted_matrix_classes_split_final_catalog_unconditional" :=
  rfl

end MatrixUnrestrictedSplitReach
