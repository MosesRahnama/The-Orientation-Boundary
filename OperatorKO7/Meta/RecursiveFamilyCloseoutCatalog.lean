import OperatorKO7.Meta.RDRSRecursiveFamilyBoundary
import OperatorKO7.Meta.RecursiveFamilyEscapeCatalog

/-!
# Recursive Family Closeout Catalog

Final closeout marker for the recursive-family escape surface.

This file adds no new mathematics. It packages the already-landed recursive-
family boundary theorem, the exact three-route escape catalog, the boundary-to-
catalog lift, the schema-generic one-way characterization, and the explicit
KO7-side exhaustive route theorem into one review-facing certificate.
-/

set_option autoImplicit false

namespace OperatorKO7.StepDuplicating

open OperatorKO7.Meta.RDRSRecursiveFamilyBoundary
open OperatorKO7.EscapeTrichotomy
open RecursiveFamilyEscapeCharacterization

/-- Packed closeout certificate for the recursive-family surface. -/
structure RecursiveFamilySurfaceClosed : Prop where
  /-- Every recursive family lies outside the uniform-cost direct-measure
  boundary. -/
  boundaryUnconditional :
    ∀ F : RecursiveFamily, IsOutsideDirectMeasureBoundary F
  /-- Any finite boundary catalog built from a family list preserves the exact
  input cardinality. -/
  boundaryCatalogSize :
    ∀ fs : List RecursiveFamily,
      (recursiveFamilyBoundaryCatalogOfList fs).size = fs.length
  /-- Every member of a boundary catalog inherits the boundary witness through
  the catalog API. -/
  boundaryCatalogMemberWitness :
    ∀ (C : RecursiveFamilyBoundaryCatalog) (F : RecursiveFamily),
      F ∈ C.families → IsOutsideDirectMeasureBoundary F
  /-- The recursive-family escape catalog has the exact three-row inventory. -/
  escapeCatalogRowCount :
    recursiveFamilyEscapeCatalogRows.length = 3
  /-- The exact route inventory has no duplicates. -/
  escapeCatalogNodup :
    recursiveFamilyEscapeCatalogRows.Nodup
  /-- Every exact route tag appears in the route inventory. -/
  escapeCatalogComplete :
    ∀ route : RecursiveFamilyEscapeRoute,
      route ∈ recursiveFamilyEscapeCatalogRows
  /-- Any boundary catalog lifts definitionally to the exact route ledger. -/
  boundaryLiftRoutes :
    ∀ C : RecursiveFamilyBoundaryCatalog,
      (recursiveFamilyEscapeCatalogOfBoundary C).routes =
        recursiveFamilyEscapeCatalogRows
  /-- Every duplicating recursive family carries the landed schema-generic
  one-way escape characterization. -/
  genericCharacterization :
    ∀ F : DuplicatingRecursiveFamily,
      RecursiveFamilyEscapeCharacterization F
  /-- Every orienting observer in the explicit KO7 direct universe lands in one
  of the three exact route classes. -/
  explicitEscapeExhaustive :
    ∀ {O : KO7DirectOrienter},
      O.Orients → RecursiveFamilyEscapeWitness O

/-- Final closeout marker for the recursive-family surface.

The theorem closes the recursive-family slice by aggregation only: no field in
the packed certificate below proves anything beyond the already-landed boundary,
catalog, or characterization modules. -/
theorem recursive_family_surface_closed : RecursiveFamilySurfaceClosed where
  boundaryUnconditional := rdrs_recursive_family_boundary_unconditional
  boundaryCatalogSize := recursiveFamilyBoundaryCatalogOfList_size
  boundaryCatalogMemberWitness := fun C F hF =>
    C.member_isOutsideBoundary F hF
  escapeCatalogRowCount := recursiveFamilyEscapeCatalogRows_length
  escapeCatalogNodup := recursiveFamilyEscapeCatalogRows_nodup
  escapeCatalogComplete := recursiveFamilyEscapeCatalogRows_complete
  boundaryLiftRoutes := recursiveFamilyEscapeCatalogOfBoundary_routes
  genericCharacterization := recursiveFamily_escape_characterization_available
  explicitEscapeExhaustive := fun horient =>
    recursiveFamily_escape_catalog_exhaustive horient

/-- Audit anchor for the recursive-family closeout catalog module. -/
def audit_theory_expansion_recursive_family_closeout_catalog_module_anchor : String :=
  "recursive_family_surface_closed"

end OperatorKO7.StepDuplicating
