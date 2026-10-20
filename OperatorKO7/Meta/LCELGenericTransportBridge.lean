import OperatorKO7.Meta.LCELUnrestrictedClassification

/-!
This module constructs transport records from caller-supplied source correspondence,
admissibility, target facts, and coherence equalities. Every result is conditional on those
fields.












-/

namespace OperatorKO7.LCELGenericTransportBridge

open OperatorKO7.LCELSchema
open OperatorKO7.LCELSemanticCorrespondence
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELMathematical
open OperatorKO7.LCELAdmissibility
open OperatorKO7.LCELUnrestrictedClassification
open OperatorKO7.ReflectionSchema

/-- Data record whose requirements are the fields displayed below.

-/
structure LCELSourceSensitiveRouteSemantics
    (L₁ L₂ : FormalLCELInstance) : Type 1 where
  strongSlot : LCELStrongSemanticSlotCorrespondence L₁ L₂
  stagewise :
    OperatorKO7.ReflectionSchema.StagewiseEquivalent
      L₁.comparison.profile.shape L₂.comparison.profile.shape
  targetLicensedAdmission :
    L₂.comparison.reflectionContent.licensedAdmission
      L₂.comparison.reflectionContent.blockedSentence
  targetObstructionBlockedEqReflectionBlocked :
    L₂.comparison.obstructionContent.blockedBy
        L₂.comparison.obstructionContent.witness
      = L₂.comparison.reflectionContent.blockedSentence
  targetReflectionBlockedEqImported :
    L₂.comparison.reflectionContent.blockedSentence
      = L₂.comparison.reimportContent.importedSentence
  targetBoundaryRealized : L₂.boundaryObject.realized

namespace LCELSourceSensitiveRouteSemantics

/-- Definition with formal content given by the displayed type and body. -/
def transportBase
    {L₁ L₂ : FormalLCELInstance}
  (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂) :
    BaseReversibilityTheorem L₁ → BaseReversibilityTheorem L₂ :=
  fun T => baseReversibilityTheorem_transport_viaStrongSlot R.strongSlot T

/-- Definition with formal content given by the displayed type and body. -/
def transportLicense
    {L₁ L₂ : FormalLCELInstance}
    (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂) :
    LicenseIrreversibilityTheorem L₁ → LicenseIrreversibilityTheorem L₂ :=
  fun T =>
    licenseIrreversibilityTheorem_transport_viaStrongSlot
      R.strongSlot R.targetLicensedAdmission T

/-- Definition with formal content given by the displayed type and body. -/
def transportReimport
    {L₁ L₂ : FormalLCELInstance}
  (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂) :
    ReimportReversibilityTheorem L₁ → ReimportReversibilityTheorem L₂ :=
  fun T => reimportReversibilityTheorem_transport_viaStrongSlot R.strongSlot T

/-- Definition with formal content given by the displayed type and body. -/
def transportBoundary
    {L₁ L₂ : FormalLCELInstance}
    (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂) :
    BoundaryFactorizationTheorem L₁ → BoundaryFactorizationTheorem L₂ :=
  fun T =>
    boundaryFactorizationTheorem_transport
      (R.transportReimport)
      (R.transportLicense)
      R.targetObstructionBlockedEqReflectionBlocked
      R.targetReflectionBlockedEqImported
      R.targetBoundaryRealized
      T

/-- Definition with formal content given by the displayed type and body.



-/
def toTransportBridgeData
    {L₁ L₂ : FormalLCELInstance}
  (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂)
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (hBase :
      R.transportBase (baseReversibilityTheorem_of_support A₁.baseSupport)
        = baseReversibilityTheorem_of_support A₂.baseSupport)
    (hLicense :
      R.transportLicense (licenseIrreversibilityTheorem_of_support A₁.licenseSupport)
        = licenseIrreversibilityTheorem_of_support A₂.licenseSupport)
    (hReimport :
      R.transportReimport (reimportReversibilityTheorem_of_support A₁.reimportSupport)
        = reimportReversibilityTheorem_of_support A₂.reimportSupport)
    (hBoundary :
      R.transportBoundary (boundaryFactorizationTheorem_of_support A₁.boundarySupport)
        = boundaryFactorizationTheorem_of_support A₂.boundarySupport) :
    LCELTransportBridgeData A₁ A₂ where
  strongSlot := R.strongSlot
  stagewise := R.stagewise
  transportBase := R.transportBase
  transportLicense := R.transportLicense
  transportReimport := R.transportReimport
  transportBoundary := R.transportBoundary
  transportBase_canonical := hBase
  transportLicense_canonical := hLicense
  transportReimport_canonical := hReimport
  transportBoundary_canonical := hBoundary

/-- Definition with formal content given by the displayed type and body.
-/
def toMathematicalSupportWitness
    {L₁ L₂ : FormalLCELInstance}
  (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂)
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (hBase :
      R.transportBase (baseReversibilityTheorem_of_support A₁.baseSupport)
        = baseReversibilityTheorem_of_support A₂.baseSupport)
    (hLicense :
      R.transportLicense (licenseIrreversibilityTheorem_of_support A₁.licenseSupport)
        = licenseIrreversibilityTheorem_of_support A₂.licenseSupport)
    (hReimport :
      R.transportReimport (reimportReversibilityTheorem_of_support A₁.reimportSupport)
        = reimportReversibilityTheorem_of_support A₂.reimportSupport)
    (hBoundary :
      R.transportBoundary (boundaryFactorizationTheorem_of_support A₁.boundarySupport)
        = boundaryFactorizationTheorem_of_support A₂.boundarySupport) :
    LCELMathematicalSupportWitness L₁ L₂ :=
  LCELMathematicalSupportWitness.ofTransportBridgeData
    A₁ A₂
    (R.toTransportBridgeData A₁ A₂ hBase hLicense hReimport hBoundary)

theorem toMathematicalSupportWitness_transportBase_fromRoute
    {L₁ L₂ : FormalLCELInstance}
  (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂)
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (hBase :
      R.transportBase (baseReversibilityTheorem_of_support A₁.baseSupport)
        = baseReversibilityTheorem_of_support A₂.baseSupport)
    (hLicense :
      R.transportLicense (licenseIrreversibilityTheorem_of_support A₁.licenseSupport)
        = licenseIrreversibilityTheorem_of_support A₂.licenseSupport)
    (hReimport :
      R.transportReimport (reimportReversibilityTheorem_of_support A₁.reimportSupport)
        = reimportReversibilityTheorem_of_support A₂.reimportSupport)
    (hBoundary :
      R.transportBoundary (boundaryFactorizationTheorem_of_support A₁.boundarySupport)
        = boundaryFactorizationTheorem_of_support A₂.boundarySupport)
    (T : BaseReversibilityTheorem L₁) :
    (R.toMathematicalSupportWitness A₁ A₂ hBase hLicense hReimport hBoundary).transportBase T
      = R.transportBase T :=
  ofTransportBridgeData_transportBase_fromBridge
    A₁ A₂ (R.toTransportBridgeData A₁ A₂ hBase hLicense hReimport hBoundary) T

theorem toMathematicalSupportWitness_transportLicense_fromRoute
    {L₁ L₂ : FormalLCELInstance}
  (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂)
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (hBase :
      R.transportBase (baseReversibilityTheorem_of_support A₁.baseSupport)
        = baseReversibilityTheorem_of_support A₂.baseSupport)
    (hLicense :
      R.transportLicense (licenseIrreversibilityTheorem_of_support A₁.licenseSupport)
        = licenseIrreversibilityTheorem_of_support A₂.licenseSupport)
    (hReimport :
      R.transportReimport (reimportReversibilityTheorem_of_support A₁.reimportSupport)
        = reimportReversibilityTheorem_of_support A₂.reimportSupport)
    (hBoundary :
      R.transportBoundary (boundaryFactorizationTheorem_of_support A₁.boundarySupport)
        = boundaryFactorizationTheorem_of_support A₂.boundarySupport)
    (T : LicenseIrreversibilityTheorem L₁) :
    (R.toMathematicalSupportWitness A₁ A₂ hBase hLicense hReimport hBoundary).transportLicense T
      = R.transportLicense T :=
  ofTransportBridgeData_transportLicense_fromBridge
    A₁ A₂ (R.toTransportBridgeData A₁ A₂ hBase hLicense hReimport hBoundary) T

theorem toMathematicalSupportWitness_transportReimport_fromRoute
    {L₁ L₂ : FormalLCELInstance}
  (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂)
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (hBase :
      R.transportBase (baseReversibilityTheorem_of_support A₁.baseSupport)
        = baseReversibilityTheorem_of_support A₂.baseSupport)
    (hLicense :
      R.transportLicense (licenseIrreversibilityTheorem_of_support A₁.licenseSupport)
        = licenseIrreversibilityTheorem_of_support A₂.licenseSupport)
    (hReimport :
      R.transportReimport (reimportReversibilityTheorem_of_support A₁.reimportSupport)
        = reimportReversibilityTheorem_of_support A₂.reimportSupport)
    (hBoundary :
      R.transportBoundary (boundaryFactorizationTheorem_of_support A₁.boundarySupport)
        = boundaryFactorizationTheorem_of_support A₂.boundarySupport)
    (T : ReimportReversibilityTheorem L₁) :
    (R.toMathematicalSupportWitness A₁ A₂ hBase hLicense hReimport hBoundary).transportReimport T
      = R.transportReimport T :=
  ofTransportBridgeData_transportReimport_fromBridge
    A₁ A₂ (R.toTransportBridgeData A₁ A₂ hBase hLicense hReimport hBoundary) T

theorem toMathematicalSupportWitness_transportBoundary_fromRoute
    {L₁ L₂ : FormalLCELInstance}
  (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂)
    (A₁ : LCELAdmissibilityData L₁)
    (A₂ : LCELAdmissibilityData L₂)
    (hBase :
      R.transportBase (baseReversibilityTheorem_of_support A₁.baseSupport)
        = baseReversibilityTheorem_of_support A₂.baseSupport)
    (hLicense :
      R.transportLicense (licenseIrreversibilityTheorem_of_support A₁.licenseSupport)
        = licenseIrreversibilityTheorem_of_support A₂.licenseSupport)
    (hReimport :
      R.transportReimport (reimportReversibilityTheorem_of_support A₁.reimportSupport)
        = reimportReversibilityTheorem_of_support A₂.reimportSupport)
    (hBoundary :
      R.transportBoundary (boundaryFactorizationTheorem_of_support A₁.boundarySupport)
        = boundaryFactorizationTheorem_of_support A₂.boundarySupport)
    (T : BoundaryFactorizationTheorem L₁) :
    (R.toMathematicalSupportWitness A₁ A₂ hBase hLicense hReimport hBoundary).transportBoundary T
      = R.transportBoundary T :=
  ofTransportBridgeData_transportBoundary_fromBridge
    A₁ A₂ (R.toTransportBridgeData A₁ A₂ hBase hLicense hReimport hBoundary) T

end LCELSourceSensitiveRouteSemantics

end OperatorKO7.LCELGenericTransportBridge
