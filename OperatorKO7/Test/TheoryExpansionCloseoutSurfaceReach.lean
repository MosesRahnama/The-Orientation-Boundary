import OperatorKO7.Meta.TheoryExpansionCloseoutSurface

/-!
# Reach test: TheoryExpansionCloseoutSurface

Asserts that the final public theory-expansion closeout names resolve and route
through the repaired Phase G surface.
-/

namespace TheoryExpansionCloseoutSurfaceReach

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.RecursiveFamilyBoundaryCloseoutCatalog

#check @OperatorKO7.TheoryExpansionCloseoutSurface
#check OperatorKO7.theoryExpansionCloseoutSurface
#check OperatorKO7.theoryExpansionCloseoutSurface_projects_phaseG
#check OperatorKO7.theoryExpansionCloseoutSurface_exact
#check OperatorKO7.theoryExpansion_public_closeout_ready

/-- Sanity: the public surface object is reachable. -/
example : OperatorKO7.TheoryExpansionCloseoutSurface :=
  OperatorKO7.theoryExpansionCloseoutSurface

/-- Sanity: the public readiness theorem exposes the Phase G closeout theorem. -/
example :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  OperatorKO7.theoryExpansion_public_closeout_ready

/-- Sanity: the canonical surface is exactly the Phase G-backed record. -/
example :
    OperatorKO7.theoryExpansionCloseoutSurface =
      { phaseGCatalog := recursiveFamily_boundary_closeout_catalog
        phaseGClosed := phaseG_recursiveFamily_boundary_closeout_closed } :=
  OperatorKO7.theoryExpansionCloseoutSurface_exact

/-- Sanity: the public surface retains the exact Phase G catalog. -/
example :
    OperatorKO7.theoryExpansionCloseoutSurface.phaseGCatalog =
      recursiveFamily_boundary_closeout_catalog :=
  rfl

/-- Sanity: the readiness theorem preserves the exact Phase G row count. -/
example : recursiveFamily_boundary_closeout_catalog.length = 11 :=
  OperatorKO7.theoryExpansion_public_closeout_ready.1.1

end TheoryExpansionCloseoutSurfaceReach
