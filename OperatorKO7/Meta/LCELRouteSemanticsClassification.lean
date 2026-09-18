import OperatorKO7.Meta.LCELGenericTransportBridge
import OperatorKO7.Meta.LCELUnrestrictedExistence

/-!
# LCEL Route-Semantics Classification and Unrestricted Lift

This file extends the L4 route-semantics layer into a clean lift surface.
Given pair-generic source-sensitive route semantics, per-side admissibility
data, and the four canonical coherence equations, the route now lifts to:

- a strong transport bridge,
- an unrestricted mathematical witness,
- unrestricted-witness admission, and
- the existing unrestricted structural-identity corollary.

This remains conditional. The lift does not claim a raw-pair witness-free P4C
theorem: the admissibility packages and four coherence equations remain explicit
hypotheses.
-/

namespace OperatorKO7.LCELGenericTransportBridge

open OperatorKO7.LCELSchema
open OperatorKO7.LCELMathematical
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELUniversalTheorem
open OperatorKO7.LCELAdmissibility
open OperatorKO7.LCELUnrestrictedTheorem
open OperatorKO7.LCELUnrestrictedClassification
open OperatorKO7.LCELUnrestrictedExistence

/-- Packaged theorem object for the conditional route-semantics lift.

This records the exact seven hypotheses still needed at the L4 boundary:
route semantics, per-side admissibility data, and the four canonical coherence
equations. It does not weaken the boundary and does not claim P4C. -/
structure LCELRouteSemanticsLiftData
    (L₁ L₂ : FormalLCELInstance) : Type 1 where
  routeSemantics :
    OperatorKO7.LCELGenericTransportBridge.LCELSourceSensitiveRouteSemantics L₁ L₂
  sourceAdmissibilityData : LCELAdmissibilityData L₁
  targetAdmissibilityData : LCELAdmissibilityData L₂
  transportBase_canonical :
    routeSemantics.transportBase
        (baseReversibilityTheorem_of_support sourceAdmissibilityData.baseSupport)
      = baseReversibilityTheorem_of_support targetAdmissibilityData.baseSupport
  transportLicense_canonical :
    routeSemantics.transportLicense
        (licenseIrreversibilityTheorem_of_support sourceAdmissibilityData.licenseSupport)
      = licenseIrreversibilityTheorem_of_support targetAdmissibilityData.licenseSupport
  transportReimport_canonical :
    routeSemantics.transportReimport
        (reimportReversibilityTheorem_of_support sourceAdmissibilityData.reimportSupport)
      = reimportReversibilityTheorem_of_support targetAdmissibilityData.reimportSupport
  transportBoundary_canonical :
    routeSemantics.transportBoundary
        (boundaryFactorizationTheorem_of_support sourceAdmissibilityData.boundarySupport)
      = boundaryFactorizationTheorem_of_support targetAdmissibilityData.boundarySupport

namespace LCELRouteSemanticsLiftData

/-- Recover the strong transport bridge carried by the packaged route lift. -/
def toTransportBridgeData
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂) :
    LCELTransportBridgeData D.sourceAdmissibilityData D.targetAdmissibilityData :=
  D.routeSemantics.toTransportBridgeData
    D.sourceAdmissibilityData
    D.targetAdmissibilityData
    D.transportBase_canonical
    D.transportLicense_canonical
    D.transportReimport_canonical
    D.transportBoundary_canonical

/-- Recover the mathematical-support witness carried by the packaged route lift. -/
def toMathematicalSupportWitness
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂) :
    LCELMathematicalSupportWitness L₁ L₂ :=
  D.routeSemantics.toMathematicalSupportWitness
    D.sourceAdmissibilityData
    D.targetAdmissibilityData
    D.transportBase_canonical
    D.transportLicense_canonical
    D.transportReimport_canonical
    D.transportBoundary_canonical

/-- Recover the unrestricted witness carried by the packaged route lift. -/
def toUnrestrictedMathematicalWitness
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂) :
    LCELUnrestrictedMathematicalWitness L₁ L₂ :=
  LCELUnrestrictedMathematicalWitness.ofAdmissibilityDataAndTransportBridge
    D.sourceAdmissibilityData
    D.targetAdmissibilityData
    D.toTransportBridgeData

theorem toUnrestrictedMathematicalWitness_comparison_eq
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂) :
    D.toUnrestrictedMathematicalWitness.comparison = D.toMathematicalSupportWitness :=
  rfl

/-- Propositional admission surface carried by the packaged route lift. -/
theorem admitsUnrestrictedWitness
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂) :
    AdmitsLCELUnrestrictedWitness L₁ L₂ :=
  ⟨D.toUnrestrictedMathematicalWitness⟩

/-- Unrestricted structural identity on the internally built admissible instances. -/
theorem lcel_unrestricted_structural_identity
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂) :
    Nonempty
      (LCELUniversalQuasiFunctor
        D.toUnrestrictedMathematicalWitness.sourceAdmissibleInstance
        D.toUnrestrictedMathematicalWitness.targetAdmissibleInstance) :=
  lcel_unrestricted_structural_identity_of_mathematicalWitness
    D.toUnrestrictedMathematicalWitness

/-- Existence-form structural identity on the packaged route-lift surface. -/
theorem lcel_exists_structural_identity
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂) :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = L₁
        ∧ A₂.instance_ = L₂
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  lcel_unrestricted_structural_identity_of_existsWitness
    D.admitsUnrestrictedWitness

theorem toMathematicalSupportWitness_transportBase_fromRoute
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂)
    (T : BaseReversibilityTheorem L₁) :
    D.toMathematicalSupportWitness.transportBase T = D.routeSemantics.transportBase T :=
  ofTransportBridgeData_transportBase_fromBridge
    D.sourceAdmissibilityData D.targetAdmissibilityData D.toTransportBridgeData T

theorem toMathematicalSupportWitness_transportLicense_fromRoute
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂)
    (T : LicenseIrreversibilityTheorem L₁) :
    D.toMathematicalSupportWitness.transportLicense T = D.routeSemantics.transportLicense T :=
  ofTransportBridgeData_transportLicense_fromBridge
    D.sourceAdmissibilityData D.targetAdmissibilityData D.toTransportBridgeData T

theorem toMathematicalSupportWitness_transportReimport_fromRoute
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂)
    (T : ReimportReversibilityTheorem L₁) :
    D.toMathematicalSupportWitness.transportReimport T = D.routeSemantics.transportReimport T :=
  ofTransportBridgeData_transportReimport_fromBridge
    D.sourceAdmissibilityData D.targetAdmissibilityData D.toTransportBridgeData T

theorem toMathematicalSupportWitness_transportBoundary_fromRoute
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂)
    (T : BoundaryFactorizationTheorem L₁) :
    D.toMathematicalSupportWitness.transportBoundary T = D.routeSemantics.transportBoundary T :=
  ofTransportBridgeData_transportBoundary_fromBridge
    D.sourceAdmissibilityData D.targetAdmissibilityData D.toTransportBridgeData T

theorem toUnrestrictedMathematicalWitness_transportBase_fromRoute
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂)
    (T : BaseReversibilityTheorem L₁) :
    D.toUnrestrictedMathematicalWitness.comparison.transportBase T = D.routeSemantics.transportBase T :=
  D.toMathematicalSupportWitness_transportBase_fromRoute T

theorem toUnrestrictedMathematicalWitness_transportLicense_fromRoute
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂)
    (T : LicenseIrreversibilityTheorem L₁) :
    D.toUnrestrictedMathematicalWitness.comparison.transportLicense T = D.routeSemantics.transportLicense T :=
  D.toMathematicalSupportWitness_transportLicense_fromRoute T

theorem toUnrestrictedMathematicalWitness_transportReimport_fromRoute
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂)
    (T : ReimportReversibilityTheorem L₁) :
    D.toUnrestrictedMathematicalWitness.comparison.transportReimport T = D.routeSemantics.transportReimport T :=
  D.toMathematicalSupportWitness_transportReimport_fromRoute T

theorem toUnrestrictedMathematicalWitness_transportBoundary_fromRoute
    {L₁ L₂ : FormalLCELInstance}
    (D : LCELRouteSemanticsLiftData L₁ L₂)
    (T : BoundaryFactorizationTheorem L₁) :
    D.toUnrestrictedMathematicalWitness.comparison.transportBoundary T = D.routeSemantics.transportBoundary T :=
  D.toMathematicalSupportWitness_transportBoundary_fromRoute T

end LCELRouteSemanticsLiftData

namespace LCELSourceSensitiveRouteSemantics

/-- Lift route semantics and admissibility/coherence data to an unrestricted
mathematical witness through the strong transport-bridge route. -/
def toUnrestrictedMathematicalWitness
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
    LCELUnrestrictedMathematicalWitness L₁ L₂ :=
  LCELUnrestrictedMathematicalWitness.ofAdmissibilityDataAndTransportBridge
    A₁ A₂
    (R.toTransportBridgeData A₁ A₂ hBase hLicense hReimport hBoundary)

/-- The unrestricted witness built from route semantics carries exactly the
strong-route mathematical-support witness in its comparison field. -/
theorem toUnrestrictedMathematicalWitness_comparison_eq
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
    (R.toUnrestrictedMathematicalWitness A₁ A₂ hBase hLicense hReimport hBoundary).comparison
      = R.toMathematicalSupportWitness A₁ A₂ hBase hLicense hReimport hBoundary :=
  rfl

theorem toUnrestrictedMathematicalWitness_transportBase_fromRoute
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
    (R.toUnrestrictedMathematicalWitness A₁ A₂ hBase hLicense hReimport hBoundary).comparison.transportBase T
      = R.transportBase T := by
  show (R.toMathematicalSupportWitness A₁ A₂ hBase hLicense hReimport hBoundary).transportBase T
      = R.transportBase T
  exact
    R.toMathematicalSupportWitness_transportBase_fromRoute
      A₁ A₂ hBase hLicense hReimport hBoundary T

theorem toUnrestrictedMathematicalWitness_transportLicense_fromRoute
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
    (R.toUnrestrictedMathematicalWitness A₁ A₂ hBase hLicense hReimport hBoundary).comparison.transportLicense T
      = R.transportLicense T := by
  show (R.toMathematicalSupportWitness A₁ A₂ hBase hLicense hReimport hBoundary).transportLicense T
      = R.transportLicense T
  exact
    R.toMathematicalSupportWitness_transportLicense_fromRoute
      A₁ A₂ hBase hLicense hReimport hBoundary T

theorem toUnrestrictedMathematicalWitness_transportReimport_fromRoute
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
    (R.toUnrestrictedMathematicalWitness A₁ A₂ hBase hLicense hReimport hBoundary).comparison.transportReimport T
      = R.transportReimport T := by
  show (R.toMathematicalSupportWitness A₁ A₂ hBase hLicense hReimport hBoundary).transportReimport T
      = R.transportReimport T
  exact
    R.toMathematicalSupportWitness_transportReimport_fromRoute
      A₁ A₂ hBase hLicense hReimport hBoundary T

theorem toUnrestrictedMathematicalWitness_transportBoundary_fromRoute
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
    (R.toUnrestrictedMathematicalWitness A₁ A₂ hBase hLicense hReimport hBoundary).comparison.transportBoundary T
      = R.transportBoundary T := by
  show (R.toMathematicalSupportWitness A₁ A₂ hBase hLicense hReimport hBoundary).transportBoundary T
      = R.transportBoundary T
  exact
    R.toMathematicalSupportWitness_transportBoundary_fromRoute
      A₁ A₂ hBase hLicense hReimport hBoundary T

/-- Route semantics plus admissibility/coherence data yields unrestricted-witness
admission on the raw pair. -/
theorem admitsUnrestrictedWitness_ofRouteSemantics
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
    AdmitsLCELUnrestrictedWitness L₁ L₂ :=
  ⟨R.toUnrestrictedMathematicalWitness A₁ A₂ hBase hLicense hReimport hBoundary⟩

/-- Route semantics plus admissibility/coherence data yields the unrestricted
structural-identity corollary on the internally built admissible instances. -/
theorem lcel_unrestricted_structural_identity_of_routeSemantics
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
    Nonempty
      (LCELUniversalQuasiFunctor
        (R.toUnrestrictedMathematicalWitness A₁ A₂ hBase hLicense hReimport hBoundary).sourceAdmissibleInstance
        (R.toUnrestrictedMathematicalWitness A₁ A₂ hBase hLicense hReimport hBoundary).targetAdmissibleInstance) :=
  lcel_unrestricted_structural_identity_of_mathematicalWitness
    (R.toUnrestrictedMathematicalWitness A₁ A₂ hBase hLicense hReimport hBoundary)

/-- Existence-form structural identity corollary from the route-semantics lift.
This is still conditional on admissibility/coherence and does not claim P4C. -/
theorem lcel_exists_structural_identity_of_routeSemantics
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
    ∃ A₁' A₂' : AdmissibleLCELInstance,
      A₁'.instance_ = L₁
        ∧ A₂'.instance_ = L₂
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁' A₂') :=
  lcel_unrestricted_structural_identity_of_existsWitness
    (R.admitsUnrestrictedWitness_ofRouteSemantics
      A₁ A₂ hBase hLicense hReimport hBoundary)

end LCELSourceSensitiveRouteSemantics

end OperatorKO7.LCELGenericTransportBridge
