import OperatorKO7.Meta.GenericDPMethodBoundary
import OperatorKO7.Meta.SemanticMethodBoundary

namespace GenericDPSemanticBoundaryReach

open OperatorKO7.GenericDPMethodBoundary
open OperatorKO7.SemanticMethodBoundary
open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.BenchmarkedPRCFamily

#check GenericDPMethodClass
#check genericDPMethodClasses
#check genericDPBoundaryRoute?
#check GenericDPBoundaryStatus
#check genericDPBoundaryStatus
#check GenericDPMethodSupported
#check GenericDPBoundaryCatalog
#check genericDPBoundaryCatalog_exact
#check genericDPBoundaryCatalog_projects_support
#check genericDPBoundaryCatalog_projects_status
#check GenericDPExplicitDirectCertificate
#check genericDP_w0_claim_requires_explicit_direct_certificate
#check GenericDPBoundaryCertificate
#check genericDPBoundaryCertificate_projects_catalog
#check genericDPBoundaryCertificate_projects_nonW0

#check SemanticMethodClass
#check semanticMethodClasses
#check semanticMethodBoundaryRoute?
#check SemanticMethodBoundaryStatus
#check semanticMethodBoundaryStatus
#check SemanticMethodSupported
#check SemanticMethodBoundaryCatalog
#check semanticMethodBoundaryCatalog_exact
#check semanticMethodBoundaryCatalog_projects_support
#check semanticMethodBoundaryCatalog_projects_status
#check importedSemanticMethod_is_licensed_escape
#check importedSemanticMethod_not_direct_w0
#check SemanticMethodBoundaryCertificate
#check semanticMethodBoundaryCertificate_projects_catalog
#check semanticMethodBoundaryCertificate_projects_importedNotW0

example : GenericDPBoundaryCatalog :=
  genericDPBoundaryCertificate_projects_catalog

example : GenericDPMethodSupported .transformedCallRoute := by
  exact genericDPBoundaryCatalog_projects_support
    genericDPBoundaryCatalog_exact .transformedCallRoute

example :
    genericDPBoundaryStatus .importedOrdering = .licensedEscape .W1 := by
  exact genericDPBoundaryCatalog_projects_status
    genericDPBoundaryCatalog_exact .importedOrdering

example : genericDPBoundaryRoute? .certifiedEngine ≠ some .W0 := by
  exact genericDPBoundaryCertificate_projects_nonW0 .certifiedEngine

example : SemanticMethodBoundaryCatalog :=
  semanticMethodBoundaryCertificate_projects_catalog

example : SemanticMethodSupported .transparentWholeTermMeasure := by
  exact semanticMethodBoundaryCatalog_projects_support
    semanticMethodBoundaryCatalog_exact .transparentWholeTermMeasure

example :
    semanticMethodBoundaryStatus .importedModelLogicalRelation = .licensedEscape .W1 := by
  exact importedSemanticMethod_is_licensed_escape

example : semanticMethodBoundaryRoute? .importedModelLogicalRelation ≠ some .W0 := by
  exact semanticMethodBoundaryCertificate_projects_importedNotW0

example : HasDirectWitness fullLinear := by
  exact semanticMethodBoundaryCatalog_projects_support
    semanticMethodBoundaryCatalog_exact .transparentWholeTermMeasure

end GenericDPSemanticBoundaryReach
