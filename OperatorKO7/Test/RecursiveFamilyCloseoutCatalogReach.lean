import OperatorKO7.Meta.RecursiveFamilyCloseoutCatalog

/-!
# Reach tests for `Meta/RecursiveFamilyCloseoutCatalog.lean`

Smoke-tests the recursive-family closeout certificate and its public marker
theorem.
-/

namespace OperatorKO7.StepDuplicating
namespace RecursiveFamilyCloseoutCatalog

open OperatorKO7.Meta.RDRSRecursiveFamilyBoundary

#check @RecursiveFamilySurfaceClosed
#check @recursive_family_surface_closed
#check @audit_theory_expansion_recursive_family_closeout_catalog_module_anchor

#print axioms recursive_family_surface_closed

example : recursiveFamilyEscapeCatalogRows.length = 3 :=
  recursive_family_surface_closed.escapeCatalogRowCount

example (fs : List RecursiveFamily) :
    (recursiveFamilyBoundaryCatalogOfList fs).size = fs.length :=
  recursive_family_surface_closed.boundaryCatalogSize fs

example (C : RecursiveFamilyBoundaryCatalog) :
    (recursiveFamilyEscapeCatalogOfBoundary C).routes =
      recursiveFamilyEscapeCatalogRows :=
  recursive_family_surface_closed.boundaryLiftRoutes C

end RecursiveFamilyCloseoutCatalog
end OperatorKO7.StepDuplicating
