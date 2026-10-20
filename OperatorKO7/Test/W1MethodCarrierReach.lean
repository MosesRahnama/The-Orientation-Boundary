import OperatorKO7.Meta.W1MethodCarrier

namespace W1MethodCarrierReach

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.W1MethodCarrier
open OperatorKO7.SemanticMethodBoundary
open OperatorKO7.GenericDPMethodBoundary
open OperatorKO7.FBIClassification
open OperatorKO7.BenchmarkedPRCFamily

#check W1MethodRow
#check w1MethodRows
#check W1MethodStatus
#check W1MethodSource
#check w1MethodRowRoute
#check w1MethodRowImportClass
#check w1MethodRowSource
#check w1MethodRowStatus
#check W1MethodRowSupported
#check w1MethodRows_nodup
#check w1MethodRows_length
#check w1MethodRows_complete_exact
#check w1MethodRowRoute_exact
#check w1MethodRowStatus_exact
#check w1MethodRowImportClass_exact
#check w1MethodRowSource_exact
#check W1MethodCarrierCatalog
#check w1MethodCarrierCatalog_exact
#check w1MethodCarrierCatalog_projects_support
#check w1MethodCarrierCatalog_projects_route
#check w1MethodCarrierCatalog_projects_status
#check w1MethodRowSupported_implies_permitted_import
#check w1MethodRowRoute_ne_w0
#check w1MethodRowRoute_ne_w2
#check w1MethodRow_separates_from_w0_and_w2
#check semanticImportedModelLogicalRelation_projects_semantic_boundary
#check genericDPImportedOrdering_projects_genericDP_boundary
#check fbiImportedWhole_projects_fbi_final_catalog
#check W1MethodCarrierCertificate
#check w1MethodCarrierCertificate_exact
#check w1MethodCarrierCertificate_projects_catalog
#check w1MethodCarrierCertificate_projects_necessity
#check w1MethodCarrierCertificate_projects_separation

example : W1MethodCarrierCatalog :=
  w1MethodCarrierCertificate_projects_catalog

example : W1MethodRowSupported .canonicalImportedWhole := by
  exact w1MethodCarrierCatalog_projects_support w1MethodCarrierCatalog_exact _

example : PermittedW1Import (w1MethodRowImportClass .genericDPImportedOrdering) := by
  exact w1MethodCarrierCertificate_projects_necessity
    (w1MethodCarrierCatalog_projects_support w1MethodCarrierCatalog_exact _)

example : w1MethodRowRoute .fbiImportedWholeLicensedEscape = .W1 := by
  exact w1MethodCarrierCatalog_projects_route w1MethodCarrierCatalog_exact _

example : w1MethodRowStatus .semanticImportedModelLogicalRelation = .licensedEscape .W1 := by
  exact w1MethodCarrierCatalog_projects_status w1MethodCarrierCatalog_exact _

example : SemanticMethodSupported .importedModelLogicalRelation := by
  exact semanticImportedModelLogicalRelation_projects_semantic_boundary.1

example : GenericDPMethodSupported .importedOrdering := by
  exact genericDPImportedOrdering_projects_genericDP_boundary.1

example : FBIFinalCatalogRowSupported .constructionW1LicensedEscape := by
  exact fbiImportedWhole_projects_fbi_final_catalog.1

example : w1MethodRowImportClass .semanticImportedModelLogicalRelation = .importedWholeWitness := by
  exact w1MethodRowImportClass_exact _

example : w1MethodRowRoute .canonicalPrecedence ≠ .W0 ∧ w1MethodRowRoute .canonicalPrecedence ≠ .W2 := by
  exact w1MethodCarrierCertificate_projects_separation _

end W1MethodCarrierReach
