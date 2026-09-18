import OperatorKO7.Meta.RecursiveFamilyEscapeCatalog

/-!
# Reach tests for `Meta/RecursiveFamilyEscapeCatalog.lean`

Smoke-tests the exact recursive-family escape catalog surface, its boundary lift,
and the exhaustive theorem derived from the existing KO7 escape trichotomy.
-/

namespace OperatorKO7.StepDuplicating
namespace RecursiveFamilyEscapeCatalogReach

open OperatorKO7.Meta.RDRSRecursiveFamilyBoundary
open OperatorKO7.EscapeTrichotomy

#check @RecursiveFamilyEscapeRoute
#check @recursiveFamilyEscapeCatalogRows
#check @recursiveFamilyEscapeCatalogRows_length
#check @recursiveFamilyEscapeCatalogRows_nodup
#check @recursiveFamilyEscapeCatalogRows_complete_exact
#check @recursiveFamilyEscapeCatalogRows_complete

#check @RecursiveFamilyEscapeCatalog
#check @recursiveFamilyEscapeCatalogOfBoundary
#check @recursiveFamilyEscapeCatalogOfBoundary_routes

#check @recursiveFamily_escape_characterization_available
#check @RecursiveFamilyEscapeWitness
#check @recursiveFamily_escape_catalog_exhaustive
#check @audit_theory_expansion_recursive_family_escape_catalog_module_anchor

#print axioms recursiveFamily_escape_catalog_exhaustive

example : RecursiveFamilyEscapeRoute.projectionOrDP ∈ recursiveFamilyEscapeCatalogRows :=
  recursiveFamilyEscapeCatalogRows_complete _

example (boundaryCatalog : RecursiveFamilyBoundaryCatalog) :
    (recursiveFamilyEscapeCatalogOfBoundary boundaryCatalog).routes =
      recursiveFamilyEscapeCatalogRows :=
  recursiveFamilyEscapeCatalogOfBoundary_routes boundaryCatalog

end RecursiveFamilyEscapeCatalogReach
end OperatorKO7.StepDuplicating
