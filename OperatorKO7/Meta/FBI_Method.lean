import OperatorKO7.Meta.ConstructionRouteCatalog_Certificate

namespace OperatorKO7

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogCertificate
open OperatorKO7.TransformedCallClassification

/-- FBI directions tracked by the carrier. -/
inductive FBIDirection where
  | forward
  | backward
deriving DecidableEq, Repr

/-- FBI instantiation modes tracked by the carrier. -/
inductive FBIInstantiation where
  | forwardOnly
  | backwardOnly
  | bidirectional
deriving DecidableEq, Repr

/-- The explicit directions used by an FBI instantiation mode. -/
def FBIInstantiation.directions : FBIInstantiation → List FBIDirection
  | .forwardOnly => [.forward]
  | .backwardOnly => [.backward]
  | .bidirectional => [.forward, .backward]

/-- An FBI instantiation matches a direction exactly when that direction occurs
in its explicit direction list. -/
def FBIInstantiation.matchesDirection
    (instantiation : FBIInstantiation) (direction : FBIDirection) : Prop :=
  direction ∈ instantiation.directions

/-- Comparison witnesses available to the FBI method carrier. -/
inductive FBIComparisonWitness where
  | directWholeTermComparison
  | transformedCallEvidence
      (witness : CanonicalConstructionWitness)
      (transformClass : W2TransformClass)
      (route_is_w2 : canonicalWitnessRoute witness = .W2)
      (transform_matches : canonicalWitnessW2TransformClass? witness = some transformClass)
  | constructionImportEvidence
      (witness : CanonicalConstructionWitness)
      (importClass : W1ImportClass)
      (route_is_w1 : canonicalWitnessRoute witness = .W1)
      (import_matches : canonicalWitnessW1ImportClass? witness = some importClass)
  | concreteCertificateEvidence
      (certificate : CanonicalConstructionCertificate)

/-- Formal FBI method objects pair an instantiation mode with explicit comparison evidence. -/
structure FBIMethod where
  instantiation : FBIInstantiation
  comparisonWitness : FBIComparisonWitness

/-- A formal FBI method matches a direction exactly when its instantiation does. -/
def FBIMethod.matchesDirection (method : FBIMethod) (direction : FBIDirection) : Prop :=
  method.instantiation.matchesDirection direction

/-- FBI closure statuses currently supported by the formal carrier. -/
inductive FBIClosureStatus where
  | reducedToExistingTheorem (route : ConstructionRoute)
  | licensedEscape (route : ConstructionRoute)
  | certifiedSuccess
deriving DecidableEq, Repr

/-- Success semantics for a formal FBI method. -/
structure FBISuccessSemantics where
  route? : Option ConstructionRoute
  closureStatus : FBIClosureStatus

/-- The route extracted from explicit FBI comparison evidence. -/
def FBIComparisonWitness.route? : FBIComparisonWitness → Option ConstructionRoute
  | .directWholeTermComparison => some .W0
  | .transformedCallEvidence _ _ _ _ => some .W2
  | .constructionImportEvidence _ _ _ _ => some .W1
  | .concreteCertificateEvidence _ => none

/-- The closure status extracted from explicit FBI comparison evidence. -/
def FBIComparisonWitness.closureStatus : FBIComparisonWitness → FBIClosureStatus
  | .directWholeTermComparison => .reducedToExistingTheorem .W0
  | .transformedCallEvidence _ _ _ _ => .licensedEscape .W2
  | .constructionImportEvidence _ _ _ _ => .licensedEscape .W1
  | .concreteCertificateEvidence _ => .certifiedSuccess

/-- The formal FBI success semantics induced by the method carrier. -/
def FBIMethod.successSemantics (method : FBIMethod) : FBISuccessSemantics where
  route? := method.comparisonWitness.route?
  closureStatus := method.comparisonWitness.closureStatus

/-- Canonical direct-evidence FBI method. -/
def directForwardFBIMethod : FBIMethod where
  instantiation := .forwardOnly
  comparisonWitness := .directWholeTermComparison

/-- Canonical W1-import FBI method routed through the existing construction catalog. -/
def importedWholeFBIMethod : FBIMethod where
  instantiation := .backwardOnly
  comparisonWitness := .constructionImportEvidence
    .w1ImportedWhole
    .importedWholeWitness
    rfl
    rfl

/-- Canonical W2 FBI method routed through the existing transformed-call catalog. -/
def transformedCallFBIMethod : FBIMethod where
  instantiation := .bidirectional
  comparisonWitness := .transformedCallEvidence
    .w2FullDuplicating
    .ko7DPProjection
    rfl
    rfl

/-- Canonical FBI method carrying concrete certificate evidence. -/
def certifiedFBIMethod : FBIMethod where
  instantiation := .bidirectional
  comparisonWitness := .concreteCertificateEvidence canonical_construction_certificate

end OperatorKO7
