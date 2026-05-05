import OperatorKO7.Meta.LCELP4CCloseout

/-!
# LCEL P4C Final Status Catalog

This module records the final theorem-facing P4C closeout surface after the
unconditional raw theorem is derived from the two now-closed universal
constructor obligations.

The catalog distinguishes three closed canonical paper-facing pairs, the
accepted exact certified boundary, the two proved universal obligations, and
the proved raw bare P4C target.
-/

namespace OperatorKO7.LCELP4CFinalStatus

open OperatorKO7.LCELP4CResidualObligation
open OperatorKO7.LCELP4CCanonicalInstances
open OperatorKO7.LCELP4CCloseout

inductive LCELP4CFinalStatusKind where
  | closedCanonicalPair
  | acceptedExactCertifiedBoundary
  | provedUniversalCertification
  | provedUniversalCertifiedRouteLiftBlueprint
  | provedRawBareP4C
  deriving DecidableEq, Repr

inductive LCELP4CFinalStatusRowId where
  | godelDpCanonicalPair
  | godelBenchmarkCanonicalPair
  | benchmarkDpCanonicalPair
  | exactCertifiedBoundary
  | universalCertification
  | universalCertifiedRouteLiftBlueprint
  | rawBareP4C
  deriving DecidableEq, Repr

def lcel_p4c_final_status_kind : LCELP4CFinalStatusRowId → LCELP4CFinalStatusKind
  | .godelDpCanonicalPair => .closedCanonicalPair
  | .godelBenchmarkCanonicalPair => .closedCanonicalPair
  | .benchmarkDpCanonicalPair => .closedCanonicalPair
  | .exactCertifiedBoundary => .acceptedExactCertifiedBoundary
  | .universalCertification => .provedUniversalCertification
  | .universalCertifiedRouteLiftBlueprint => .provedUniversalCertifiedRouteLiftBlueprint
  | .rawBareP4C => .provedRawBareP4C

def lcel_p4c_final_status_label : LCELP4CFinalStatusRowId → String
  | .godelDpCanonicalPair => "Canonical Godel-DP pair"
  | .godelBenchmarkCanonicalPair => "Canonical Godel-benchmark pair"
  | .benchmarkDpCanonicalPair => "Canonical benchmark-DP pair"
  | .exactCertifiedBoundary => "Exact certified boundary"
  | .universalCertification => "Universal certification proved"
  | .universalCertifiedRouteLiftBlueprint => "Universal certified route-lift blueprint proved"
  | .rawBareP4C => "Raw bare P4C proved"

structure LCELP4CFinalStatusRow where
  id : LCELP4CFinalStatusRowId
  label : String
  kind : LCELP4CFinalStatusKind
  deriving DecidableEq, Repr

def lcel_p4c_final_status_row
    (rowId : LCELP4CFinalStatusRowId) : LCELP4CFinalStatusRow :=
  {
    id := rowId
    label := lcel_p4c_final_status_label rowId
    kind := lcel_p4c_final_status_kind rowId
  }

def lcel_p4c_final_status_rows : List LCELP4CFinalStatusRow :=
  [lcel_p4c_final_status_row .godelDpCanonicalPair,
    lcel_p4c_final_status_row .godelBenchmarkCanonicalPair,
    lcel_p4c_final_status_row .benchmarkDpCanonicalPair,
    lcel_p4c_final_status_row .exactCertifiedBoundary,
    lcel_p4c_final_status_row .universalCertification,
    lcel_p4c_final_status_row .universalCertifiedRouteLiftBlueprint,
    lcel_p4c_final_status_row .rawBareP4C]

structure LCELP4CFinalStatusCatalog : Type 1 where
  rows : List LCELP4CFinalStatusRow
  canonicalBoundary : LCELP4CCanonicalBoundaryCatalog
  rows_exact : rows = lcel_p4c_final_status_rows

def lcel_p4c_final_status_catalog : LCELP4CFinalStatusCatalog where
  rows := lcel_p4c_final_status_rows
  canonicalBoundary := lcel_p4c_canonicalBoundaryCatalog
  rows_exact := rfl

def LCELP4CFinalStatusCatalog.HasRow
    (catalog : LCELP4CFinalStatusCatalog)
    (rowId : LCELP4CFinalStatusRowId)
    (kind : LCELP4CFinalStatusKind) : Prop :=
  ∃ row ∈ catalog.rows, row.id = rowId ∧ row.kind = kind

theorem lcel_p4c_final_status_catalog_rows_exact :
    lcel_p4c_final_status_catalog.rows = lcel_p4c_final_status_rows :=
  lcel_p4c_final_status_catalog.rows_exact

private theorem lcel_p4c_final_status_catalog_covers_row
    (rowId : LCELP4CFinalStatusRowId) :
    LCELP4CFinalStatusCatalog.HasRow
      lcel_p4c_final_status_catalog
      rowId
      (lcel_p4c_final_status_kind rowId) := by
  refine ⟨lcel_p4c_final_status_row rowId, ?_, rfl, rfl⟩
  cases rowId <;>
    simp [lcel_p4c_final_status_catalog, lcel_p4c_final_status_rows,
      lcel_p4c_final_status_row,
      lcel_p4c_final_status_label, lcel_p4c_final_status_kind]

theorem lcel_p4c_final_status_catalog_covers_godel_dp :
    LCELP4CFinalStatusCatalog.HasRow
      lcel_p4c_final_status_catalog
      .godelDpCanonicalPair
      .closedCanonicalPair :=
  lcel_p4c_final_status_catalog_covers_row .godelDpCanonicalPair

theorem lcel_p4c_final_status_catalog_covers_godel_benchmark :
    LCELP4CFinalStatusCatalog.HasRow
      lcel_p4c_final_status_catalog
      .godelBenchmarkCanonicalPair
      .closedCanonicalPair :=
  lcel_p4c_final_status_catalog_covers_row .godelBenchmarkCanonicalPair

theorem lcel_p4c_final_status_catalog_covers_benchmark_dp :
    LCELP4CFinalStatusCatalog.HasRow
      lcel_p4c_final_status_catalog
      .benchmarkDpCanonicalPair
      .closedCanonicalPair :=
  lcel_p4c_final_status_catalog_covers_row .benchmarkDpCanonicalPair

theorem lcel_p4c_final_status_catalog_accepts_exactCertifiedBoundary :
    LCELP4CFinalStatusCatalog.HasRow
      lcel_p4c_final_status_catalog
      .exactCertifiedBoundary
      .acceptedExactCertifiedBoundary :=
  lcel_p4c_final_status_catalog_covers_row .exactCertifiedBoundary

theorem lcel_p4c_final_status_catalog_marks_universalCertification_proved :
    LCELP4CFinalStatusCatalog.HasRow
      lcel_p4c_final_status_catalog
      .universalCertification
      .provedUniversalCertification :=
  lcel_p4c_final_status_catalog_covers_row .universalCertification

theorem lcel_p4c_final_status_catalog_marks_universalCertifiedRouteLiftBlueprint_proved :
    LCELP4CFinalStatusCatalog.HasRow
      lcel_p4c_final_status_catalog
      .universalCertifiedRouteLiftBlueprint
      .provedUniversalCertifiedRouteLiftBlueprint :=
  lcel_p4c_final_status_catalog_covers_row .universalCertifiedRouteLiftBlueprint

theorem lcel_p4c_final_status_catalog_marks_rawBareP4C_proved :
    LCELP4CFinalStatusCatalog.HasRow
      lcel_p4c_final_status_catalog
      .rawBareP4C
      .provedRawBareP4C :=
  lcel_p4c_final_status_catalog_covers_row .rawBareP4C

/-- The final status catalog now certifies the exact certified boundary
without extra hypotheses. -/
theorem lcel_p4c_final_status_catalog_proves_exactCertifiedBoundary :
    LCELP4CExactCertifiedBoundary :=
  lcel_p4c_exactCertifiedBoundary_closed

/-- The final status catalog records universal certification as proved. -/
theorem lcel_p4c_final_status_catalog_proves_universalCertification :
    CertifiedFormalLCELInstance.UniversalCertification :=
  lcel_p4c_final_status_catalog_proves_exactCertifiedBoundary.1

/-- The final status catalog records the universal certified route-lift
blueprint as proved. -/
theorem lcel_p4c_final_status_catalog_proves_universalCertifiedRouteLiftBlueprint :
    CertifiedFormalLCELInstance.UniversalCertifiedRouteLiftBlueprint :=
  lcel_p4c_final_status_catalog_proves_exactCertifiedBoundary.2

/-- The final status catalog records the unconditional raw bare P4C target. -/
theorem lcel_p4c_final_status_catalog_proves_rawBareP4CTarget :
    LCELP4CRawTarget :=
  lcel_p4c_unconditional_rawTarget

theorem lcel_p4c_final_status_catalog_projects_residualDataCatalog
    (h : LCELP4CExactCertifiedBoundary) :
    LCELP4CResidualDataCatalog :=
  lcel_p4c_residualDataCatalog_of_exactCertifiedBoundary h

theorem lcel_p4c_final_status_catalog_projects_certifiedBoundaryCatalog
    (h : LCELP4CExactCertifiedBoundary) :
    LCELP4CCertifiedBoundaryCatalog :=
  lcel_p4c_certifiedBoundaryCatalog_of_exactCertifiedBoundary h

theorem lcel_p4c_final_status_catalog_projects_universalResidualPackage
    (h : LCELP4CExactCertifiedBoundary) :
    UniversalLCELRouteLiftResidualPackage :=
  universal_residualPackage_of_exactCertifiedBoundary h

theorem lcel_p4c_final_status_catalog_projects_rawBareP4CTarget
    (h : LCELP4CExactCertifiedBoundary) :
    LCELP4CRawTarget :=
  universal_lcel_witness_free_structural_identity_of_exactCertifiedBoundary h

end OperatorKO7.LCELP4CFinalStatus
