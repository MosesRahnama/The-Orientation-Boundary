import OperatorKO7.Meta.RecursiveFamilyBoundaryCloseoutCatalog

/-!
# Theory Expansion Closeout Surface

Final public closeout surface for the theory-expansion lane. This module
consumes the repaired Phase G recursive-family boundary surface and exposes a
single record plus reach-friendly theorem names for Sprint 14 closeout.
-/

namespace OperatorKO7

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.RecursiveFamilyBoundaryCloseoutCatalog

/-- Public closeout package for the theory-expansion lane. The catalog field is
the repaired Phase G catalog, and the proof field is the repaired Phase G
theorem surface. This file does not rebuild the Phase G catalog or restate any
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

/-- Canonical public closeout surface for the theory-expansion lane. -/
def theoryExpansionCloseoutSurface : TheoryExpansionCloseoutSurface where
  phaseGCatalog := recursiveFamily_boundary_closeout_catalog
  phaseGClosed := phaseG_recursiveFamily_boundary_closeout_closed

/-- The public closeout surface projects the repaired Phase G theorem. -/
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

/-- The canonical surface is exactly the record built from the Phase G closeout
theorem. -/
theorem theoryExpansionCloseoutSurface_exact :
    theoryExpansionCloseoutSurface =
      { phaseGCatalog := recursiveFamily_boundary_closeout_catalog
        phaseGClosed := phaseG_recursiveFamily_boundary_closeout_closed } := by
  rfl

/-- Public Sprint 14 readiness marker for the theory-expansion lane. -/
theorem theoryExpansion_public_closeout_ready :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  theoryExpansionCloseoutSurface_projects_phaseG

end OperatorKO7
