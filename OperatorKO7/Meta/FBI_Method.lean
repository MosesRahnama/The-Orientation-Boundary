import OperatorKO7.Meta.ConstructionRouteCatalog_Certificate

namespace OperatorKO7

open OperatorKO7.ConstructionMethodClassification
open OperatorKO7.ConstructionRouteCatalog
open OperatorKO7.ConstructionRouteCatalogCertificate
open OperatorKO7.TransformedCallClassification

/-!
# FBI method carrier and constructor tags

`FBIMethod` pairs an instantiation-mode tag with a comparison-witness
constructor. The route and closure-status functions below classify the witness
constructor by pattern matching. The type permits every pairing of instantiation
mode and witness constructor. The `certifiedSuccess` tag is assigned when the
witness constructor already carries a certificate. Semantic orientation,
direction-witness consistency, and adequacy require additional predicates.
-/

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

/-- Membership of a direction in the instantiation's explicit direction list. -/
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

/-- Apply `FBIInstantiation.matchesDirection` to the method's instantiation field. -/
def FBIMethod.matchesDirection (method : FBIMethod) (direction : FBIDirection) : Prop :=
  method.instantiation.matchesDirection direction

/-- Closure-status constructors represented by `FBIClosureStatus`. -/
inductive FBIClosureStatus where
  | reducedToExistingTheorem (route : ConstructionRoute)
  | licensedEscape (route : ConstructionRoute)
  | certifiedSuccess
deriving DecidableEq, Repr

/-- Route and closure-status tags associated with a method. -/
structure FBISuccessSemantics where
  route? : Option ConstructionRoute
  closureStatus : FBIClosureStatus

/-- The route extracted from explicit FBI comparison evidence. -/
def FBIComparisonWitness.route? : FBIComparisonWitness → Option ConstructionRoute
  | .directWholeTermComparison => some .W0
  | .transformedCallEvidence _ _ _ _ => some .W2
  | .constructionImportEvidence _ _ _ _ => some .W1
  | .concreteCertificateEvidence _ => none

/-- Constructor-to-status mapping for FBI comparison witnesses. -/
def FBIComparisonWitness.closureStatus : FBIComparisonWitness → FBIClosureStatus
  | .directWholeTermComparison => .reducedToExistingTheorem .W0
  | .transformedCallEvidence _ _ _ _ => .licensedEscape .W2
  | .constructionImportEvidence _ _ _ _ => .licensedEscape .W1
  | .concreteCertificateEvidence _ => .certifiedSuccess

/-- Apply the witness's route and status mappings independently of the instantiation field. -/
def FBIMethod.successSemantics (method : FBIMethod) : FBISuccessSemantics where
  route? := method.comparisonWitness.route?
  closureStatus := method.comparisonWitness.closureStatus

/-- Direct-comparison fixture with the `forwardOnly` instantiation tag. -/
def directForwardFBIMethod : FBIMethod where
  instantiation := .forwardOnly
  comparisonWitness := .directWholeTermComparison

/-- Construction-import fixture with the `backwardOnly` instantiation tag. -/
def importedWholeFBIMethod : FBIMethod where
  instantiation := .backwardOnly
  comparisonWitness := .constructionImportEvidence
    .w1ImportedWhole
    .importedWholeWitness
    rfl
    rfl

/-- Transformed-call fixture with the `bidirectional` instantiation tag. -/
def transformedCallFBIMethod : FBIMethod where
  instantiation := .bidirectional
  comparisonWitness := .transformedCallEvidence
    .w2FullDuplicating
    .ko7DPProjection
    rfl
    rfl

/-- Fixture whose witness constructor carries `canonical_construction_certificate`. -/
def certifiedFBIMethod : FBIMethod where
  instantiation := .bidirectional
  comparisonWitness := .concreteCertificateEvidence canonical_construction_certificate

end OperatorKO7
