import OperatorKO7.Meta.RecursiveFamilyBoundaryCloseoutCatalog

/-!
# Theory Expansion Summary Surface

Final public summary surface for the theory-expansion development. This module
consumes the repaired recursive-family boundary surface and exposes a
single record plus accessible theorem names for completion.
-/

namespace OperatorKO7

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.RecursiveFamilyBoundaryCloseoutCatalog

/-- Public completion package for the theory-expansion development. The catalog field is
the repaired catalog, and the proof field is the repaired 
theorem surface. This file does not rebuild the catalog or restate any
substrate proof. -/
structure TheoryExpansionCloseoutSurface where
  phaseGCatalog : List RecursiveFamilyBoundaryCloseoutRow
  phaseGClosed :
    (phaseGCatalog.length = 11 ∧
        phaseGCatalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ phaseGCatalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row)

/-- Canonical public summary surface for the theory-expansion development. -/
def theoryExpansionCloseoutSurface : TheoryExpansionCloseoutSurface where
  phaseGCatalog := recursiveFamily_boundary_closeout_catalog
  phaseGClosed := phaseG_recursiveFamily_boundary_closeout_closed

/-- The public summary surface projects the repaired theorem. -/
theorem theoryExpansionCloseoutSurface_projects_phaseG :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  by
    simpa [theoryExpansionCloseoutSurface] using
      theoryExpansionCloseoutSurface.phaseGClosed

/-- The canonical surface is exactly the record built from the completion
theorem. -/
theorem theoryExpansionCloseoutSurface_exact :
    theoryExpansionCloseoutSurface =
      { phaseGCatalog := recursiveFamily_boundary_closeout_catalog
        phaseGClosed := phaseG_recursiveFamily_boundary_closeout_closed } := by
  rfl

/-- Public completion theorem for the theory-expansion development. -/
theorem theoryExpansion_public_closeout_ready :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  theoryExpansionCloseoutSurface_projects_phaseG

end OperatorKO7
