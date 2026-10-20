import OperatorKO7.Meta.RDRSRecursiveFamilyBoundary
import OperatorKO7.Meta.RecursiveFamilyEscapeCharacterization
import OperatorKO7.Meta.EscapeTrichotomy

/-!
# Recursive Family Escape Catalog

This module turns the already-landed recursive-family escape surfaces into one
finite catalog layer.

The catalog is intentionally exact and narrow:

- `projectionOrDP`: projection-style or dependency-pair style escape routes,
- `nonlinearOutOfClass`: escapes that leave the current formalized direct
  barrier universe,
- `ablation`: escapes that break the base-level transparency the direct
  barrier lane requires.

The exhaustive theorem in this file does not claim a converse. It states only
that every orienting observer in the explicit KO7 direct universe lands in one
of these three route classes, via the existing
`ko7_direct_escape_trichotomy_extended` theorem.

The catalog itself is packaged on top of the already-landed
`RecursiveFamilyBoundaryCatalog` carrier so later closeout modules can import a
single route ledger together with whatever boundary-family list they need.
-/

set_option autoImplicit false

namespace OperatorKO7.StepDuplicating

open OperatorKO7
open OperatorKO7.Meta.RDRSRecursiveFamilyBoundary
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.EscapeTrichotomy
open RecursiveFamilyEscapeCharacterization

/-- Exact route tags for the currently formalized recursive-family escape
catalog. -/
inductive RecursiveFamilyEscapeRoute where
  | projectionOrDP
  | nonlinearOutOfClass
  | ablation
  deriving DecidableEq, Repr

/-- Exact finite inventory of the recursive-family escape routes currently
formalized. -/
def recursiveFamilyEscapeCatalogRows : List RecursiveFamilyEscapeRoute :=
  [ .projectionOrDP
  , .nonlinearOutOfClass
  , .ablation
  ]

/-- The recursive-family escape catalog has exactly three route rows. -/
theorem recursiveFamilyEscapeCatalogRows_length :
    recursiveFamilyEscapeCatalogRows.length = 3 := by
  rfl

/-- The recursive-family escape catalog has no duplicate route rows. -/
theorem recursiveFamilyEscapeCatalogRows_nodup :
    recursiveFamilyEscapeCatalogRows.Nodup := by
  decide

/-- Exact membership characterization for the recursive-family escape catalog. -/
theorem recursiveFamilyEscapeCatalogRows_complete_exact
    (route : RecursiveFamilyEscapeRoute) :
    route ∈ recursiveFamilyEscapeCatalogRows ↔
      route = .projectionOrDP ∨
      route = .nonlinearOutOfClass ∨
      route = .ablation := by
  cases route <;> decide

/-- Every recursive-family escape route is represented in the exact catalog. -/
theorem recursiveFamilyEscapeCatalogRows_complete
    (route : RecursiveFamilyEscapeRoute) :
    route ∈ recursiveFamilyEscapeCatalogRows := by
  cases route <;> decide

/-- Boundary-lifted carrier for the recursive-family escape catalog.

The boundary catalog records which recursive families are being tracked; this
structure adds the finite route ledger those families can close through. -/
structure RecursiveFamilyEscapeCatalog where
  boundaryCatalog : RecursiveFamilyBoundaryCatalog
  routes : List RecursiveFamilyEscapeRoute
  routes_nodup : routes.Nodup
  routes_complete : ∀ route : RecursiveFamilyEscapeRoute, route ∈ routes

/-- Lift any recursive-family boundary catalog to the exact escape-route
catalog used by the current recursive-family closeout lane. -/
def recursiveFamilyEscapeCatalogOfBoundary
    (boundaryCatalog : RecursiveFamilyBoundaryCatalog) :
    RecursiveFamilyEscapeCatalog where
  boundaryCatalog := boundaryCatalog
  routes := recursiveFamilyEscapeCatalogRows
  routes_nodup := recursiveFamilyEscapeCatalogRows_nodup
  routes_complete := recursiveFamilyEscapeCatalogRows_complete

/-- The boundary lift preserves the exact route ledger definitionally. -/
theorem recursiveFamilyEscapeCatalogOfBoundary_routes
    (boundaryCatalog : RecursiveFamilyBoundaryCatalog) :
    (recursiveFamilyEscapeCatalogOfBoundary boundaryCatalog).routes =
      recursiveFamilyEscapeCatalogRows := by
  rfl

/-- Generic side bridge: every duplicating recursive family already carries the
landed one-way escape characterization certificate. This keeps the catalog file
connected to the schema-generic escape layer used later by the closeout
catalog. -/
theorem recursiveFamily_escape_characterization_available
    (F : DuplicatingRecursiveFamily) :
    RecursiveFamilyEscapeCharacterization F := by
  exact recursiveFamily_escape_characterization_certificate F

/-- Concrete recursive-family escape witnesses for the explicit KO7 direct
orienter universe. The three constructors intentionally match the exact route
catalog above. -/
inductive RecursiveFamilyEscapeWitness (O : KO7DirectOrienter) : Prop
  | projectionOrDP :
      ¬ StepDuplicatingSchema.WrapSubtermSensitive ko7Schema O.primaryScalar →
        RecursiveFamilyEscapeWitness O
  | nonlinearOutOfClass :
      ¬ KO7DirectBarrierRepresentable O →
        RecursiveFamilyEscapeWitness O
  | ablation :
      ¬ StepDuplicatingSchema.TransparentAtBase ko7Schema O.primaryScalar →
        RecursiveFamilyEscapeWitness O

/-- Closed catalog theorem: every orienting observer in the explicit KO7 direct
universe lands in one of the three exact recursive-family escape routes.

This is the exhaustive theorem for the currently formalized class. It is
derived directly from the existing `ko7_direct_escape_trichotomy_extended`
surface and therefore makes no stronger converse claim. -/
theorem recursiveFamily_escape_catalog_exhaustive
    {O : KO7DirectOrienter}
    (horient : O.Orients) :
    RecursiveFamilyEscapeWitness O := by
  have htri := ko7_direct_escape_trichotomy_extended (O := O) horient
  rcases htri with hprojection | hablation | hnonlinear
  · exact RecursiveFamilyEscapeWitness.projectionOrDP hprojection
  · exact RecursiveFamilyEscapeWitness.ablation hablation
  · exact RecursiveFamilyEscapeWitness.nonlinearOutOfClass hnonlinear

/-- Audit anchor for the recursive-family escape-catalog expansion module. -/
def audit_theory_expansion_recursive_family_escape_catalog_module_anchor : String :=
  "recursiveFamily_escape_catalog_exhaustive"

end OperatorKO7.StepDuplicating
