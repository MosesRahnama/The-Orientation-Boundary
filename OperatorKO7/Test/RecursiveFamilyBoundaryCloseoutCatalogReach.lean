import OperatorKO7.Meta.RecursiveFamilyBoundaryCloseoutCatalog

/-!
# Reach test: RecursiveFamilyBoundaryCloseoutCatalog (Phase G)

Asserts that every required public name from the Phase G closeout catalog
resolves verbatim, and that the catalog's 11 rows each project to a
theorem-backed substrate identifier.
-/

namespace RecursiveFamilyBoundaryCloseoutCatalogReach

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.RecursiveFamilyBoundaryCloseoutCatalog

#check @RecursiveFamilyBoundaryCloseoutRow
#check @recursiveFamily_boundary_closeout_catalog
#check @recursiveFamily_boundary_closeout_catalog_complete_exact
#check @recursiveFamily_boundary_closeout_row_projects_existing_surface
#check @recursiveFamily_boundary_closeout_row_projects_existing_surface_holds
#check @phaseG_recursiveFamily_boundary_closeout_closed

/-- Sanity: the catalog has the expected length. -/
example : recursiveFamily_boundary_closeout_catalog.length = 11 :=
  recursiveFamily_boundary_closeout_catalog_complete_exact.1

/-- Sanity: every catalog row projects onto a theorem-backed substrate
surface. -/
example : ∀ row : RecursiveFamilyBoundaryCloseoutRow,
    recursiveFamily_boundary_closeout_row_projects_existing_surface row :=
  recursiveFamily_boundary_closeout_row_projects_existing_surface_holds

/-- Sanity: the closeout marker bundles the catalog completeness and the
per-row projection. -/
example :
    (recursiveFamily_boundary_closeout_catalog.length = 11 ∧
        recursiveFamily_boundary_closeout_catalog.Nodup ∧
        (∀ row : RecursiveFamilyBoundaryCloseoutRow,
          row ∈ recursiveFamily_boundary_closeout_catalog)) ∧
      (∀ row : RecursiveFamilyBoundaryCloseoutRow,
        recursiveFamily_boundary_closeout_row_projects_existing_surface row) :=
  phaseG_recursiveFamily_boundary_closeout_closed

/-- Sanity: every constructor of `RecursiveFamilyBoundaryCloseoutRow` appears
in the finite catalog. -/
example (row : RecursiveFamilyBoundaryCloseoutRow) :
    row ∈ recursiveFamily_boundary_closeout_catalog :=
  recursiveFamily_boundary_closeout_catalog_complete_exact.2.2 row

/-- Sanity: per-row projection is provable on a concrete row. -/
example :
    recursiveFamily_boundary_closeout_row_projects_existing_surface
      .phaseA3_CanonicalWitnessUniversality :=
  recursiveFamily_boundary_closeout_row_projects_existing_surface_holds
    .phaseA3_CanonicalWitnessUniversality

end RecursiveFamilyBoundaryCloseoutCatalogReach
