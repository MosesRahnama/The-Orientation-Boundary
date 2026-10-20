import OperatorKO7.Meta.TheoryExpansionCloseoutSurface

/-!
# Theory Expansion Completion Record

Public completion record. This module consumes the
completion surface and records the completion marker without weakening or
restating the repaired substrate.
-/

namespace OperatorKO7

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.RecursiveFamilyBoundaryCloseoutCatalog

/-- Public completion package for the theory-expansion development. The record
projects the completion surface, records the exact row count,
and records that every row is theorem-backed. -/
structure TheoryExpansionReleaseAudit where
  closeoutSurface : TheoryExpansionCloseoutSurface
  closeoutSurfaceExact : closeoutSurface = theoryExpansionCloseoutSurface
  publicCloseoutReady :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row)
  rowCount : recursiveFamily_boundary_closeout_catalog.length = 11
  allRowsTheoremBacked :
    ∀ row ∈ recursiveFamily_boundary_closeout_catalog,
      RecursiveFamilyBoundaryCloseoutRow.status row =
        RecursiveFamilyBoundaryCloseoutRow.Status.theoremBacked

/-- Canonical public completion record for the theory-expansion development. -/
def theoryExpansionReleaseAudit : TheoryExpansionReleaseAudit where
  closeoutSurface := theoryExpansionCloseoutSurface
  closeoutSurfaceExact := rfl
  publicCloseoutReady := theoryExpansion_public_closeout_ready
  rowCount := theoryExpansion_public_closeout_ready.1.1
  allRowsTheoremBacked := by
    intro row _hRow
    cases row <;> rfl

/-- The record projects the public summary marker. -/
theorem theoryExpansionReleaseAudit_projects_closeout :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  theoryExpansionReleaseAudit.publicCloseoutReady

/-- The record preserves the repaired row count. -/
theorem theoryExpansionReleaseAudit_row_count :
    recursiveFamily_boundary_closeout_catalog.length = 11 :=
  theoryExpansionReleaseAudit.rowCount

/-- Every repaired row surfaced by the record is theorem-backed. -/
theorem theoryExpansionReleaseAudit_all_rows_theoremBacked :
    ∀ row ∈ recursiveFamily_boundary_closeout_catalog,
      RecursiveFamilyBoundaryCloseoutRow.status row =
        RecursiveFamilyBoundaryCloseoutRow.Status.theoremBacked :=
  theoryExpansionReleaseAudit.allRowsTheoremBacked

/-- Public completion theorem, backed by the completion
surface and the repaired catalog. -/
theorem theoryExpansion_release_ready :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  theoryExpansionReleaseAudit_projects_closeout

end OperatorKO7
