import OperatorKO7.Meta.ConstructionRouteCatalog_Certificate
import OperatorKO7.Meta.SemanticMethodBoundary
import OperatorKO7.Meta.GenericDPMethodBoundary
import OperatorKO7.Meta.FBI_Classification

/-!
# W1 Method Carrier

This module packages the theorem-backed W1 import layer as a finite carrier.
It records canonical W1 witnesses and the currently connected W1-facing rows
from the semantic, generic-DP, and FBI boundary surfaces.
-/

namespace OperatorKO7.W1MethodCarrier

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogCertificate
open OperatorKO7.SemanticMethodBoundary
open OperatorKO7.GenericDPMethodBoundary
open OperatorKO7.FBIClassification
open OperatorKO7.BenchmarkedPRCFamily

/-- Finite carrier of theorem-backed W1 method rows. -/
inductive W1MethodRow where
  | canonicalPrecedence
  | canonicalGlobalPolynomial
  | canonicalImportedWhole
  | canonicalTransparency
  | semanticImportedModelLogicalRelation
  | genericDPImportedOrdering
  | fbiImportedWholeLicensedEscape
  deriving DecidableEq, Repr

/-- Finite inventory of the W1 method-carrier rows. -/
def w1MethodRows : List W1MethodRow :=
  [ .canonicalPrecedence
  , .canonicalGlobalPolynomial
  , .canonicalImportedWhole
  , .canonicalTransparency
  , .semanticImportedModelLogicalRelation
  , .genericDPImportedOrdering
  , .fbiImportedWholeLicensedEscape
  ]

/-- Status vocabulary for the finite W1 carrier. -/
inductive W1MethodStatus where
  | licensedEscape (route : ConstructionRoute)
  deriving DecidableEq, Repr

/-- Source surface from which a W1 carrier row is projected. -/
inductive W1MethodSource where
  | canonicalSuccess (success : W1ConstructionSuccess)
  | semanticBoundary (cls : SemanticMethodClass)
  | genericDPBoundary (cls : GenericDPMethodClass)
  | fbiFinalCatalog (row : FBIFinalCatalogRow)

/-- Route projection carried by each W1 method row. -/
def w1MethodRowRoute : W1MethodRow → ConstructionRoute
  | .canonicalPrecedence => .W1
  | .canonicalGlobalPolynomial => .W1
  | .canonicalImportedWhole => .W1
  | .canonicalTransparency => .W1
  | .semanticImportedModelLogicalRelation => .W1
  | .genericDPImportedOrdering => .W1
  | .fbiImportedWholeLicensedEscape => .W1

/-- Import-class projection carried by each W1 method row. -/
def w1MethodRowImportClass : W1MethodRow → W1ImportClass
  | .canonicalPrecedence => .precedence
  | .canonicalGlobalPolynomial => .globalPolynomial
  | .canonicalImportedWhole => .importedWholeWitness
  | .canonicalTransparency => .transparencyEssentiality
  | .semanticImportedModelLogicalRelation => .importedWholeWitness
  | .genericDPImportedOrdering => .precedence
  | .fbiImportedWholeLicensedEscape => .importedWholeWitness

/-- Source witness or certificate projection carried by each W1 row. -/
def w1MethodRowSource : W1MethodRow → W1MethodSource
  | .canonicalPrecedence => .canonicalSuccess mpo_w1_success
  | .canonicalGlobalPolynomial => .canonicalSuccess poly_w1_success
  | .canonicalImportedWhole => .canonicalSuccess importedWhole_w1_success
  | .canonicalTransparency => .canonicalSuccess transparency_w1_success
  | .semanticImportedModelLogicalRelation =>
      .semanticBoundary .importedModelLogicalRelation
  | .genericDPImportedOrdering =>
      .genericDPBoundary .importedOrdering
  | .fbiImportedWholeLicensedEscape =>
      .fbiFinalCatalog .constructionW1LicensedEscape

/-- Status projection carried by each W1 row. -/
def w1MethodRowStatus : W1MethodRow → W1MethodStatus
  | .canonicalPrecedence => .licensedEscape .W1
  | .canonicalGlobalPolynomial => .licensedEscape .W1
  | .canonicalImportedWhole => .licensedEscape .W1
  | .canonicalTransparency => .licensedEscape .W1
  | .semanticImportedModelLogicalRelation => .licensedEscape .W1
  | .genericDPImportedOrdering => .licensedEscape .W1
  | .fbiImportedWholeLicensedEscape => .licensedEscape .W1

/-- Theorem-backed support payload for each W1 carrier row. -/
def W1MethodRowSupported : W1MethodRow → Prop
  | .canonicalPrecedence =>
      PermittedW1Import .precedence
  | .canonicalGlobalPolynomial =>
      PermittedW1Import .globalPolynomial
  | .canonicalImportedWhole =>
      PermittedW1Import .importedWholeWitness ∧
        importedWhole_w1_success.route ≠ .W0 ∧
        HasImportedWholeWitness fullDuplicating ∧
        ¬ HasDirectWitness fullDuplicating
  | .canonicalTransparency =>
      PermittedW1Import .transparencyEssentiality
  | .semanticImportedModelLogicalRelation =>
      SemanticMethodSupported .importedModelLogicalRelation ∧
        semanticMethodBoundaryRoute? .importedModelLogicalRelation = some .W1 ∧
        semanticMethodBoundaryStatus .importedModelLogicalRelation = .licensedEscape .W1
  | .genericDPImportedOrdering =>
      GenericDPMethodSupported .importedOrdering ∧
        genericDPBoundaryRoute? .importedOrdering = some .W1 ∧
        genericDPBoundaryStatus .importedOrdering = .licensedEscape .W1
  | .fbiImportedWholeLicensedEscape =>
      FBIFinalCatalogRowSupported .constructionW1LicensedEscape ∧
        fbiFinalCatalogRoute? .constructionW1LicensedEscape = some .W1 ∧
        fbiFinalCatalogStatus .constructionW1LicensedEscape = .licensedEscape .W1

/-- Every W1 method row in the finite carrier has theorem-backed support. -/
theorem w1MethodRowSupported_holds (row : W1MethodRow) :
    W1MethodRowSupported row := by
  cases row with
  | canonicalPrecedence =>
      exact mpo_w1_success_requires_precedence_import
  | canonicalGlobalPolynomial =>
      exact poly_w1_success_requires_global_polynomial_import
  | canonicalImportedWhole =>
      exact ⟨importedWhole_w1_success_requires_imported_whole,
        importedWhole_w1_success_separates_from_w0.1,
        importedWhole_w1_success_separates_from_w0.2.1,
        importedWhole_w1_success_separates_from_w0.2.2⟩
  | canonicalTransparency =>
      exact transparency_w1_success_requires_transparency_import
  | semanticImportedModelLogicalRelation =>
      exact ⟨semanticMethodSupported_holds .importedModelLogicalRelation,
        semanticMethodBoundaryRoute_exact .importedModelLogicalRelation,
        semanticMethodBoundaryStatus_exact .importedModelLogicalRelation⟩
  | genericDPImportedOrdering =>
      exact ⟨genericDPMethodSupported_holds .importedOrdering,
        genericDPBoundaryRoute_exact .importedOrdering,
        genericDPBoundaryStatus_exact .importedOrdering⟩
  | fbiImportedWholeLicensedEscape =>
      exact ⟨fbi_final_catalog_row_supported .constructionW1LicensedEscape,
        (fbi_final_catalog_row_route_status_exact .constructionW1LicensedEscape).1,
        (fbi_final_catalog_row_route_status_exact .constructionW1LicensedEscape).2⟩

/-- The W1 carrier inventory has no duplicates. -/
theorem w1MethodRows_nodup :
    w1MethodRows.Nodup := by
  decide

/-- The W1 carrier inventory has exact size seven. -/
theorem w1MethodRows_length :
    w1MethodRows.length = 7 := by
  rfl

/-- Exact membership characterization for the W1 carrier inventory. -/
theorem w1MethodRows_complete_exact (row : W1MethodRow) :
    row ∈ w1MethodRows ↔
      row = .canonicalPrecedence ∨
      row = .canonicalGlobalPolynomial ∨
      row = .canonicalImportedWhole ∨
      row = .canonicalTransparency ∨
      row = .semanticImportedModelLogicalRelation ∨
      row = .genericDPImportedOrdering ∨
      row = .fbiImportedWholeLicensedEscape := by
  cases row <;> simp [w1MethodRows]

/-- Exact route projection for each W1 carrier row. -/
theorem w1MethodRowRoute_exact (row : W1MethodRow) :
    w1MethodRowRoute row = .W1 := by
  cases row <;> rfl

/-- Exact status projection for each W1 carrier row. -/
theorem w1MethodRowStatus_exact (row : W1MethodRow) :
    w1MethodRowStatus row = .licensedEscape .W1 := by
  cases row <;> rfl

/-- Exact import-class projection for each W1 carrier row. -/
theorem w1MethodRowImportClass_exact (row : W1MethodRow) :
    w1MethodRowImportClass row =
      match row with
      | .canonicalPrecedence => .precedence
      | .canonicalGlobalPolynomial => .globalPolynomial
      | .canonicalImportedWhole => .importedWholeWitness
      | .canonicalTransparency => .transparencyEssentiality
      | .semanticImportedModelLogicalRelation => .importedWholeWitness
      | .genericDPImportedOrdering => .precedence
      | .fbiImportedWholeLicensedEscape => .importedWholeWitness := by
  cases row <;> rfl

/-- Exact source projection for each W1 carrier row. -/
theorem w1MethodRowSource_exact (row : W1MethodRow) :
    w1MethodRowSource row =
      match row with
      | .canonicalPrecedence => .canonicalSuccess mpo_w1_success
      | .canonicalGlobalPolynomial => .canonicalSuccess poly_w1_success
      | .canonicalImportedWhole => .canonicalSuccess importedWhole_w1_success
      | .canonicalTransparency => .canonicalSuccess transparency_w1_success
      | .semanticImportedModelLogicalRelation =>
          .semanticBoundary .importedModelLogicalRelation
      | .genericDPImportedOrdering => .genericDPBoundary .importedOrdering
      | .fbiImportedWholeLicensedEscape =>
          .fbiFinalCatalog .constructionW1LicensedEscape := by
  cases row <;> rfl

/-- Paper-facing proposition for the finite W1 carrier catalog. -/
abbrev W1MethodCarrierCatalog : Prop :=
  ∀ row : W1MethodRow,
    row ∈ w1MethodRows ∧
      W1MethodRowSupported row ∧
      w1MethodRowRoute row = .W1 ∧
      w1MethodRowStatus row = .licensedEscape .W1

/-- The finite W1 carrier catalog is fully realized by the current theorem-backed rows. -/
theorem w1MethodCarrierCatalog_exact : W1MethodCarrierCatalog := by
  intro row
  refine ⟨?_, w1MethodRowSupported_holds row, w1MethodRowRoute_exact row, w1MethodRowStatus_exact row⟩
  exact (w1MethodRows_complete_exact row).2 <| by
    cases row <;> simp

/-- The catalog projects theorem-backed support for each W1 row. -/
theorem w1MethodCarrierCatalog_projects_support
    (h : W1MethodCarrierCatalog) (row : W1MethodRow) :
    W1MethodRowSupported row :=
  (h row).2.1

/-- The catalog projects the exact route for each W1 row. -/
theorem w1MethodCarrierCatalog_projects_route
    (h : W1MethodCarrierCatalog) (row : W1MethodRow) :
    w1MethodRowRoute row = .W1 :=
  (h row).2.2.1

/-- The catalog projects the exact status for each W1 row. -/
theorem w1MethodCarrierCatalog_projects_status
    (h : W1MethodCarrierCatalog) (row : W1MethodRow) :
    w1MethodRowStatus row = .licensedEscape .W1 :=
  (h row).2.2.2

/-- Carrier-level necessity: every supported W1 row exposes a permitted W1 import. -/
theorem w1MethodRowSupported_implies_permitted_import
    {row : W1MethodRow} (h : W1MethodRowSupported row) :
    PermittedW1Import (w1MethodRowImportClass row) := by
  cases row with
  | canonicalPrecedence =>
      exact h
  | canonicalGlobalPolynomial =>
      exact h
  | canonicalImportedWhole =>
      exact h.1
  | canonicalTransparency =>
      exact h
  | semanticImportedModelLogicalRelation =>
      exact h.1.1
  | genericDPImportedOrdering =>
      exact h.1.1
  | fbiImportedWholeLicensedEscape =>
      exact importedWhole_w1_success_requires_imported_whole

/-- Every W1 carrier row is separated from W0. -/
theorem w1MethodRowRoute_ne_w0 (row : W1MethodRow) :
    w1MethodRowRoute row ≠ .W0 := by
  cases row <;> decide

/-- Every W1 carrier row is separated from W2. -/
theorem w1MethodRowRoute_ne_w2 (row : W1MethodRow) :
    w1MethodRowRoute row ≠ .W2 := by
  cases row <;> decide

/-- Carrier-level route separation from W0 and W2. -/
theorem w1MethodRow_separates_from_w0_and_w2 (row : W1MethodRow) :
    w1MethodRowRoute row ≠ .W0 ∧ w1MethodRowRoute row ≠ .W2 := by
  exact ⟨w1MethodRowRoute_ne_w0 row, w1MethodRowRoute_ne_w2 row⟩

/-- The semantic imported-model row connects to the existing semantic boundary surface. -/
theorem semanticImportedModelLogicalRelation_projects_semantic_boundary :
    SemanticMethodSupported .importedModelLogicalRelation ∧
      semanticMethodBoundaryRoute? .importedModelLogicalRelation = some .W1 ∧
      semanticMethodBoundaryStatus .importedModelLogicalRelation = .licensedEscape .W1 := by
  exact w1MethodRowSupported_holds .semanticImportedModelLogicalRelation

/-- The generic-DP imported-ordering row connects to the existing generic-DP boundary surface. -/
theorem genericDPImportedOrdering_projects_genericDP_boundary :
    GenericDPMethodSupported .importedOrdering ∧
      genericDPBoundaryRoute? .importedOrdering = some .W1 ∧
      genericDPBoundaryStatus .importedOrdering = .licensedEscape .W1 := by
  exact w1MethodRowSupported_holds .genericDPImportedOrdering

/-- The FBI imported-whole row connects to the existing FBI final-catalog surface. -/
theorem fbiImportedWhole_projects_fbi_final_catalog :
    FBIFinalCatalogRowSupported .constructionW1LicensedEscape ∧
      fbiFinalCatalogRoute? .constructionW1LicensedEscape = some .W1 ∧
      fbiFinalCatalogStatus .constructionW1LicensedEscape = .licensedEscape .W1 := by
  exact w1MethodRowSupported_holds .fbiImportedWholeLicensedEscape

/-- Certificate packaging the exact W1 carrier catalog, necessity, and route separation. -/
structure W1MethodCarrierCertificate where
  catalog : W1MethodCarrierCatalog
  necessity : ∀ {row : W1MethodRow}, W1MethodRowSupported row → PermittedW1Import (w1MethodRowImportClass row)
  separation : ∀ row : W1MethodRow, w1MethodRowRoute row ≠ .W0 ∧ w1MethodRowRoute row ≠ .W2

/-- The W1 carrier certificate is realized by the finite catalog, necessity, and separation theorems. -/
theorem w1MethodCarrierCertificate_exact : W1MethodCarrierCertificate := by
  exact {
    catalog := w1MethodCarrierCatalog_exact
    necessity := fun {row} h => w1MethodRowSupported_implies_permitted_import h
    separation := w1MethodRow_separates_from_w0_and_w2
  }

/-- The certificate projects the exact W1 carrier catalog. -/
theorem w1MethodCarrierCertificate_projects_catalog :
    W1MethodCarrierCatalog :=
  w1MethodCarrierCertificate_exact.catalog

/-- The certificate projects carrier-level necessity. -/
theorem w1MethodCarrierCertificate_projects_necessity
    {row : W1MethodRow} (h : W1MethodRowSupported row) :
    PermittedW1Import (w1MethodRowImportClass row) :=
  w1MethodCarrierCertificate_exact.necessity h

/-- The certificate projects carrier-level route separation. -/
theorem w1MethodCarrierCertificate_projects_separation
    (row : W1MethodRow) :
    w1MethodRowRoute row ≠ .W0 ∧ w1MethodRowRoute row ≠ .W2 :=
  w1MethodCarrierCertificate_exact.separation row

end OperatorKO7.W1MethodCarrier
