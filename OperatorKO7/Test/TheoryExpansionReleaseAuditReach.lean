import OperatorKO7.Meta.TheoryExpansionReleaseAudit

/-!
# Reachability check: TheoryExpansionReleaseAudit

Asserts that the release-audit names resolve and project through the public surface.
-/

namespace TheoryExpansionReleaseAuditReach

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.RecursiveFamilyBoundaryCloseoutCatalog

#check @OperatorKO7.TheoryExpansionReleaseAudit
#check OperatorKO7.theoryExpansionReleaseAudit
#check OperatorKO7.theoryExpansionReleaseAudit_projects_closeout
#check OperatorKO7.theoryExpansionReleaseAudit_row_count
#check OperatorKO7.theoryExpansionReleaseAudit_all_rows_theoremBacked
#check OperatorKO7.theoryExpansion_release_ready

/-- Sanity: the public release-audit object is reachable. -/
example : OperatorKO7.TheoryExpansionReleaseAudit :=
  OperatorKO7.theoryExpansionReleaseAudit

/-- Sanity: the release audit preserves the closeout marker. -/
example :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  OperatorKO7.theoryExpansionReleaseAudit_projects_closeout

/-- Sanity: the release-level marker is reachable. -/
example :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  OperatorKO7.theoryExpansion_release_ready

/-- Sanity: the release audit preserves the exact row count. -/
example : recursiveFamily_boundary_closeout_catalog.length = 11 :=
  OperatorKO7.theoryExpansionReleaseAudit_row_count

/-- Sanity: all release-audit rows are theorem-backed. -/
example :
    ∀ row ∈ recursiveFamily_boundary_closeout_catalog,
      RecursiveFamilyBoundaryCloseoutRow.status row =
        RecursiveFamilyBoundaryCloseoutRow.Status.theoremBacked :=
  OperatorKO7.theoryExpansionReleaseAudit_all_rows_theoremBacked

/-- Sanity: the audit record uses the canonical closeout surface. -/
example :
    OperatorKO7.theoryExpansionReleaseAudit.closeoutSurface =
      OperatorKO7.theoryExpansionCloseoutSurface :=
  OperatorKO7.theoryExpansionReleaseAudit.closeoutSurfaceExact

end TheoryExpansionReleaseAuditReach
