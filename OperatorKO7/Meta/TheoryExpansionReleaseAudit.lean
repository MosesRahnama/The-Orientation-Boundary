import OperatorKO7.Meta.TheoryExpansionCloseoutSurface

/-!
# Theory Expansion Release Audit

Public release-audit surface for Sprint 15. This module consumes the Sprint 14
closeout surface and records the release-level marker without weakening or
restating the repaired Phase G substrate.
-/

namespace OperatorKO7

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.RecursiveFamilyBoundaryCloseoutCatalog

/-- Public release-audit package for the theory-expansion lane. The record
projects the Sprint 14 closeout surface, records the exact Phase G row count,
and records that every Phase G row is theorem-backed. -/
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

/-- Canonical public release audit for the theory-expansion lane. -/
def theoryExpansionReleaseAudit : TheoryExpansionReleaseAudit where
  closeoutSurface := theoryExpansionCloseoutSurface
  closeoutSurfaceExact := rfl
  publicCloseoutReady := theoryExpansion_public_closeout_ready
  rowCount := theoryExpansion_public_closeout_ready.1.1
  allRowsTheoremBacked := by
    intro row _hRow
    cases row <;> rfl

/-- The release audit projects the Sprint 14 public closeout marker. -/
theorem theoryExpansionReleaseAudit_projects_closeout :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  theoryExpansionReleaseAudit.publicCloseoutReady

/-- The release audit preserves the repaired Phase G row count. -/
theorem theoryExpansionReleaseAudit_row_count :
    recursiveFamily_boundary_closeout_catalog.length = 11 :=
  theoryExpansionReleaseAudit.rowCount

/-- Every repaired Phase G row surfaced by the release audit is theorem-backed. -/
theorem theoryExpansionReleaseAudit_all_rows_theoremBacked :
    ∀ row ∈ recursiveFamily_boundary_closeout_catalog,
      RecursiveFamilyBoundaryCloseoutRow.status row =
        RecursiveFamilyBoundaryCloseoutRow.Status.theoremBacked :=
  theoryExpansionReleaseAudit.allRowsTheoremBacked

/-- Release-level public readiness marker, backed by the Sprint 14 closeout
surface and the repaired Phase G catalog. -/
theorem theoryExpansion_release_ready :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  theoryExpansionReleaseAudit_projects_closeout

end OperatorKO7
