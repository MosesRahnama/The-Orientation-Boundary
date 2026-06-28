import OperatorKO7.Meta.LCELUnrestrictedClassification

/-!
# LCEL Generic Transport Bridge

L4 pair-generic source-sensitive route semantics for the strong transport-bridge
stack.

The existing strong bridge layer (`LCELTransportBridgeData`) already packages
explicit theorem-object transport functions plus canonical coherence equations.
What it does not package separately is the **route semantics pattern** used by
the benchmark ↔ DP canonical case: a strong slot correspondence, stagewise
equivalence, and the target-side structural laws needed to build the four
source-sensitive theorem transports by the generic helper constructors.

This file isolates that pattern into a reusable record and supplies theorem-backed
builders from route semantics to `LCELTransportBridgeData` and then to
`LCELMathematicalSupportWitness`.
-/

namespace OperatorKO7.LCELGenericTransportBridge

open OperatorKO7.LCELSchema
open OperatorKO7.LCELSemanticCorrespondence
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELMathematical
open OperatorKO7.LCELAdmissibility
open OperatorKO7.LCELUnrestrictedClassification
open OperatorKO7.ReflectionSchema

/-- Pair-generic source-sensitive route semantics for the four theorem-object
transport helpers. This is the reusable data that the benchmark ↔ DP canonical
case was spelling out directly at the bridge-definition site. -/
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

/-- Source-sensitive base-theorem transport induced by the route semantics. -/
def transportBase
    {L₁ L₂ : FormalLCELInstance}
  (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂) :
    BaseReversibilityTheorem L₁ → BaseReversibilityTheorem L₂ :=
  fun T => baseReversibilityTheorem_transport_viaStrongSlot R.strongSlot T

/-- Source-sensitive license-theorem transport induced by the route semantics. -/
def transportLicense
    {L₁ L₂ : FormalLCELInstance}
    (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂) :
    LicenseIrreversibilityTheorem L₁ → LicenseIrreversibilityTheorem L₂ :=
  fun T =>
    licenseIrreversibilityTheorem_transport_viaStrongSlot
      R.strongSlot R.targetLicensedAdmission T

/-- Source-sensitive reimport-theorem transport induced by the route semantics. -/
def transportReimport
    {L₁ L₂ : FormalLCELInstance}
  (R : OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂) :
    ReimportReversibilityTheorem L₁ → ReimportReversibilityTheorem L₂ :=
  fun T => reimportReversibilityTheorem_transport_viaStrongSlot R.strongSlot T

/-- Source-sensitive boundary-theorem transport induced by the route semantics. -/
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

/-- Build a strong transport bridge from pair-generic source-sensitive route
semantics once the canonical coherence equations are supplied. This isolates the
remaining obligation exactly: route semantics alone does not fix the target's
canonical theorem objects, so admissibility data and coherence proofs are still
required. -/
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

/-- Build a mathematical support witness directly from route semantics, via the
strong transport-bridge builder. -/
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
