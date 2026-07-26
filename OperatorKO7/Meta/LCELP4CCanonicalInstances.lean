import OperatorKO7.Meta.LCELP4CResidualObligation
import OperatorKO7.Meta.LCELUnrestrictedTheorem

namespace OperatorKO7.LCELP4CCanonicalInstances

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELDpInstance
open OperatorKO7.LCELAdmissibility
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELSemanticCorrespondence
open OperatorKO7.LCELUniversalTheorem
open OperatorKO7.LCELUnrestrictedExistence
open OperatorKO7.LCELUnrestrictedClassification
open OperatorKO7.LCELGenericTransportBridge
open OperatorKO7.LCELBenchmarkDpUnrestrictedTheorem
open OperatorKO7.LCELP4CResidualObligation

/-- Canonical admissibility and support overlay on the Gödel 1931 LCEL
instance. -/
def godel1931CertifiedFormalLCELInstance : CertifiedFormalLCELInstance :=
  CertifiedFormalLCELInstance.ofAdmissibilityData
    godel1931LCELInstance
    godel1931LCELAdmissibilityData

/-- Canonical admissibility and support overlay on the benchmark-transport LCEL
instance. -/
def benchmarkTransportCertifiedFormalLCELInstance : CertifiedFormalLCELInstance :=
  CertifiedFormalLCELInstance.ofAdmissibilityData
    benchmarkTransportLCELInstance
    benchmarkTransportLCELAdmissibilityData

/-- Canonical admissibility and support overlay on the native DP / emitter LCEL
instance. -/
def dpEmitterCertifiedFormalLCELInstance : CertifiedFormalLCELInstance :=
  CertifiedFormalLCELInstance.ofAdmissibilityData
    dpEmitterLCELInstance
    dpEmitterLCELAdmissibilityData

theorem godel1931CertifiedFormalLCELInstance_toAdmissibilityData :
    godel1931CertifiedFormalLCELInstance.toAdmissibilityData
      = godel1931LCELAdmissibilityData :=
  rfl

theorem benchmarkTransportCertifiedFormalLCELInstance_toAdmissibilityData :
    benchmarkTransportCertifiedFormalLCELInstance.toAdmissibilityData
      = benchmarkTransportLCELAdmissibilityData :=
  rfl

theorem dpEmitterCertifiedFormalLCELInstance_toAdmissibilityData :
    dpEmitterCertifiedFormalLCELInstance.toAdmissibilityData
      = dpEmitterLCELAdmissibilityData :=
  rfl

/-- Pair-level route and coherence inputs used to build a route-lift blueprint
for a fixed LCEL pair. Every field is supplied by the package. -/
structure CertifiedRouteLiftInputPackage
    (C₁ C₂ : CertifiedFormalLCELInstance) : Type 1 where
  routeSemantics : LCELSourceSensitiveRouteSemantics C₁.instance_ C₂.instance_
  transportBase_canonical :
    routeSemantics.transportBase
        (baseReversibilityTheorem_of_support C₁.toAdmissibilityData.baseSupport)
      = baseReversibilityTheorem_of_support C₂.toAdmissibilityData.baseSupport
  transportLicense_canonical :
    routeSemantics.transportLicense
        (licenseIrreversibilityTheorem_of_support C₁.toAdmissibilityData.licenseSupport)
      = licenseIrreversibilityTheorem_of_support C₂.toAdmissibilityData.licenseSupport
  transportReimport_canonical :
    routeSemantics.transportReimport
        (reimportReversibilityTheorem_of_support C₁.toAdmissibilityData.reimportSupport)
      = reimportReversibilityTheorem_of_support C₂.toAdmissibilityData.reimportSupport
  transportBoundary_canonical :
    routeSemantics.transportBoundary
        (boundaryFactorizationTheorem_of_support C₁.toAdmissibilityData.boundarySupport)
      = boundaryFactorizationTheorem_of_support C₂.toAdmissibilityData.boundarySupport

namespace CertifiedRouteLiftInputPackage

/-- Recover the route-lift blueprint from the supplied inputs for a fixed
pair. -/
def toBlueprint
    {C₁ C₂ : CertifiedFormalLCELInstance}
    (P : CertifiedRouteLiftInputPackage C₁ C₂) :
    CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint C₁ C₂ where
  strongSlot := P.routeSemantics.strongSlot
  stagewise := P.routeSemantics.stagewise
  targetObstructionBlockedEqReflectionBlocked :=
    P.routeSemantics.targetObstructionBlockedEqReflectionBlocked
  targetReflectionBlockedEqImported :=
    P.routeSemantics.targetReflectionBlockedEqImported
  transportBase_canonical := P.transportBase_canonical
  transportLicense_canonical := P.transportLicense_canonical
  transportReimport_canonical := P.transportReimport_canonical
  transportBoundary_canonical := P.transportBoundary_canonical

/-- The packaged route-lift inputs also recover the named residual package on
the underlying raw pair. -/
def toResidualPackage
    {C₁ C₂ : CertifiedFormalLCELInstance}
    (P : CertifiedRouteLiftInputPackage C₁ C₂) :
    LCELRouteLiftResidualPackage C₁.instance_ C₂.instance_ :=
  P.toBlueprint.toResidualPackage

end CertifiedRouteLiftInputPackage

/-- Supplied route semantics on the benchmark ↔ DP pair in target-boundary
form. -/
def benchmark_dp_certifiedSourceSensitiveRouteSemantics :
    LCELSourceSensitiveRouteSemantics
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance where
  strongSlot := benchmark_dp_strongSemanticSlotCorrespondence
  stagewise := benchmark_dp_transportBridgeData.stagewise
  targetLicensedAdmission :=
    dpEmitterLicenseIrreversibilitySupport.blockedLicensedAdmission
  targetObstructionBlockedEqReflectionBlocked :=
    dpEmitterBoundaryFactorizationSupport.obstructionBlockedEqReflectionBlocked
  targetReflectionBlockedEqImported :=
    dpEmitterBoundaryFactorizationSupport.reflectionBlockedEqImported
  targetBoundaryRealized :=
    dpEmitterLCELInstance.boundaryObject.designated_realizes

theorem benchmark_dp_certified_transportBase_canonical :
    benchmark_dp_certifiedSourceSensitiveRouteSemantics.transportBase
      (baseReversibilityTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.baseSupport)
    = baseReversibilityTheorem_of_support
        dpEmitterLCELAdmissibilityData.baseSupport := by
  simpa [benchmark_dp_certifiedSourceSensitiveRouteSemantics,
    benchmark_dp_sourceSensitiveRouteSemantics]
    using benchmark_dp_route_transportBase_canonical

theorem benchmark_dp_certified_transportLicense_canonical :
    benchmark_dp_certifiedSourceSensitiveRouteSemantics.transportLicense
      (licenseIrreversibilityTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.licenseSupport)
    = licenseIrreversibilityTheorem_of_support
        dpEmitterLCELAdmissibilityData.licenseSupport := by
  simpa [benchmark_dp_certifiedSourceSensitiveRouteSemantics,
    benchmark_dp_sourceSensitiveRouteSemantics]
    using benchmark_dp_route_transportLicense_canonical

theorem benchmark_dp_certified_transportReimport_canonical :
    benchmark_dp_certifiedSourceSensitiveRouteSemantics.transportReimport
      (reimportReversibilityTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.reimportSupport)
    = reimportReversibilityTheorem_of_support
        dpEmitterLCELAdmissibilityData.reimportSupport := by
  simpa [benchmark_dp_certifiedSourceSensitiveRouteSemantics,
    benchmark_dp_sourceSensitiveRouteSemantics]
    using benchmark_dp_route_transportReimport_canonical

theorem benchmark_dp_certified_transportBoundary_canonical :
    benchmark_dp_certifiedSourceSensitiveRouteSemantics.transportBoundary
      (boundaryFactorizationTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.boundarySupport)
    = boundaryFactorizationTheorem_of_support
        dpEmitterLCELAdmissibilityData.boundarySupport := by
  simpa [benchmark_dp_certifiedSourceSensitiveRouteSemantics,
    benchmark_dp_sourceSensitiveRouteSemantics]
    using benchmark_dp_route_transportBoundary_canonical

/-- Supplied route semantics on the Gödel ↔ DP pair. -/
def godel_dp_certifiedSourceSensitiveRouteSemantics :
    LCELSourceSensitiveRouteSemantics
      godel1931LCELInstance
      dpEmitterLCELInstance where
  strongSlot := godel_dp_strongSemanticSlotCorrespondence
  stagewise := godel_dp_transportBridgeData.stagewise
  targetLicensedAdmission :=
    dpEmitterLicenseIrreversibilitySupport.blockedLicensedAdmission
  targetObstructionBlockedEqReflectionBlocked :=
    dpEmitterBoundaryFactorizationSupport.obstructionBlockedEqReflectionBlocked
  targetReflectionBlockedEqImported :=
    dpEmitterBoundaryFactorizationSupport.reflectionBlockedEqImported
  targetBoundaryRealized :=
    dpEmitterLCELInstance.boundaryObject.designated_realizes

theorem godel_dp_certified_transportBase_canonical :
    godel_dp_certifiedSourceSensitiveRouteSemantics.transportBase
      (baseReversibilityTheorem_of_support godel1931LCELAdmissibilityData.baseSupport)
    = baseReversibilityTheorem_of_support
        dpEmitterLCELAdmissibilityData.baseSupport :=
  rfl

theorem godel_dp_certified_transportLicense_canonical :
    godel_dp_certifiedSourceSensitiveRouteSemantics.transportLicense
      (licenseIrreversibilityTheorem_of_support
        godel1931LCELAdmissibilityData.licenseSupport)
    = licenseIrreversibilityTheorem_of_support
        dpEmitterLCELAdmissibilityData.licenseSupport :=
  rfl

theorem godel_dp_certified_transportReimport_canonical :
    godel_dp_certifiedSourceSensitiveRouteSemantics.transportReimport
      (reimportReversibilityTheorem_of_support
        godel1931LCELAdmissibilityData.reimportSupport)
    = reimportReversibilityTheorem_of_support
        dpEmitterLCELAdmissibilityData.reimportSupport :=
  rfl

theorem godel_dp_certified_transportBoundary_canonical :
    godel_dp_certifiedSourceSensitiveRouteSemantics.transportBoundary
      (boundaryFactorizationTheorem_of_support
        godel1931LCELAdmissibilityData.boundarySupport)
    = boundaryFactorizationTheorem_of_support
        dpEmitterLCELAdmissibilityData.boundarySupport :=
  rfl

/-- Supplied route semantics on the Gödel ↔ benchmark pair. -/
def godel_benchmark_certifiedSourceSensitiveRouteSemantics :
    LCELSourceSensitiveRouteSemantics
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  strongSlot := godel_benchmark_strongSemanticSlotCorrespondence
  stagewise := godel_benchmark_transportBridgeData.stagewise
  targetLicensedAdmission :=
    benchmarkTransportLicenseIrreversibilitySupport.blockedLicensedAdmission
  targetObstructionBlockedEqReflectionBlocked :=
    benchmarkTransportBoundaryFactorizationSupport.obstructionBlockedEqReflectionBlocked
  targetReflectionBlockedEqImported :=
    benchmarkTransportBoundaryFactorizationSupport.reflectionBlockedEqImported
  targetBoundaryRealized :=
    benchmarkTransportLCELInstance.boundaryObject.designated_realizes

theorem godel_benchmark_certified_transportBase_canonical :
    godel_benchmark_certifiedSourceSensitiveRouteSemantics.transportBase
      (baseReversibilityTheorem_of_support godel1931LCELAdmissibilityData.baseSupport)
    = baseReversibilityTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.baseSupport :=
  rfl

theorem godel_benchmark_certified_transportLicense_canonical :
    godel_benchmark_certifiedSourceSensitiveRouteSemantics.transportLicense
      (licenseIrreversibilityTheorem_of_support
        godel1931LCELAdmissibilityData.licenseSupport)
    = licenseIrreversibilityTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.licenseSupport :=
  rfl

theorem godel_benchmark_certified_transportReimport_canonical :
    godel_benchmark_certifiedSourceSensitiveRouteSemantics.transportReimport
      (reimportReversibilityTheorem_of_support
        godel1931LCELAdmissibilityData.reimportSupport)
    = reimportReversibilityTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.reimportSupport :=
  rfl

theorem godel_benchmark_certified_transportBoundary_canonical :
    godel_benchmark_certifiedSourceSensitiveRouteSemantics.transportBoundary
      (boundaryFactorizationTheorem_of_support
        godel1931LCELAdmissibilityData.boundarySupport)
    = boundaryFactorizationTheorem_of_support
        benchmarkTransportLCELAdmissibilityData.boundarySupport :=
  rfl

/-- Canonical packaged route-lift inputs on the benchmark ↔ DP pair. -/
def benchmark_dp_certifiedRouteLiftInputPackage :
    CertifiedRouteLiftInputPackage
      benchmarkTransportCertifiedFormalLCELInstance
      dpEmitterCertifiedFormalLCELInstance where
  routeSemantics := benchmark_dp_certifiedSourceSensitiveRouteSemantics
  transportBase_canonical := by
    simpa [benchmarkTransportCertifiedFormalLCELInstance,
      dpEmitterCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      benchmark_dp_certifiedSourceSensitiveRouteSemantics]
      using benchmark_dp_certified_transportBase_canonical
  transportLicense_canonical := by
    simpa [benchmarkTransportCertifiedFormalLCELInstance,
      dpEmitterCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      benchmark_dp_certifiedSourceSensitiveRouteSemantics]
      using benchmark_dp_certified_transportLicense_canonical
  transportReimport_canonical := by
    simpa [benchmarkTransportCertifiedFormalLCELInstance,
      dpEmitterCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      benchmark_dp_certifiedSourceSensitiveRouteSemantics]
      using benchmark_dp_certified_transportReimport_canonical
  transportBoundary_canonical := by
    simpa [benchmarkTransportCertifiedFormalLCELInstance,
      dpEmitterCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      benchmark_dp_certifiedSourceSensitiveRouteSemantics]
      using benchmark_dp_certified_transportBoundary_canonical

/-- Canonical packaged route-lift inputs on the Gödel ↔ DP pair. -/
def godel_dp_certifiedRouteLiftInputPackage :
    CertifiedRouteLiftInputPackage
      godel1931CertifiedFormalLCELInstance
      dpEmitterCertifiedFormalLCELInstance where
  routeSemantics := godel_dp_certifiedSourceSensitiveRouteSemantics
  transportBase_canonical := by
    simpa [godel1931CertifiedFormalLCELInstance,
      dpEmitterCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      godel_dp_certifiedSourceSensitiveRouteSemantics]
      using godel_dp_certified_transportBase_canonical
  transportLicense_canonical := by
    simpa [godel1931CertifiedFormalLCELInstance,
      dpEmitterCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      godel_dp_certifiedSourceSensitiveRouteSemantics]
      using godel_dp_certified_transportLicense_canonical
  transportReimport_canonical := by
    simpa [godel1931CertifiedFormalLCELInstance,
      dpEmitterCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      godel_dp_certifiedSourceSensitiveRouteSemantics]
      using godel_dp_certified_transportReimport_canonical
  transportBoundary_canonical := by
    simpa [godel1931CertifiedFormalLCELInstance,
      dpEmitterCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      godel_dp_certifiedSourceSensitiveRouteSemantics]
      using godel_dp_certified_transportBoundary_canonical

/-- Canonical packaged route-lift inputs on the Gödel ↔ benchmark pair. -/
def godel_benchmark_certifiedRouteLiftInputPackage :
    CertifiedRouteLiftInputPackage
      godel1931CertifiedFormalLCELInstance
      benchmarkTransportCertifiedFormalLCELInstance where
  routeSemantics := godel_benchmark_certifiedSourceSensitiveRouteSemantics
  transportBase_canonical := by
    simpa [godel1931CertifiedFormalLCELInstance,
      benchmarkTransportCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      godel_benchmark_certifiedSourceSensitiveRouteSemantics]
      using godel_benchmark_certified_transportBase_canonical
  transportLicense_canonical := by
    simpa [godel1931CertifiedFormalLCELInstance,
      benchmarkTransportCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      godel_benchmark_certifiedSourceSensitiveRouteSemantics]
      using godel_benchmark_certified_transportLicense_canonical
  transportReimport_canonical := by
    simpa [godel1931CertifiedFormalLCELInstance,
      benchmarkTransportCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      godel_benchmark_certifiedSourceSensitiveRouteSemantics]
      using godel_benchmark_certified_transportReimport_canonical
  transportBoundary_canonical := by
    simpa [godel1931CertifiedFormalLCELInstance,
      benchmarkTransportCertifiedFormalLCELInstance,
      CertifiedFormalLCELInstance.ofAdmissibilityData,
      CertifiedFormalLCELInstance.toAdmissibilityData,
      godel_benchmark_certifiedSourceSensitiveRouteSemantics]
      using godel_benchmark_certified_transportBoundary_canonical

/-- Route-lift blueprint assembled for the benchmark ↔ DP pair. -/
def benchmark_dp_certifiedRouteLiftBlueprint :
    CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint
      benchmarkTransportCertifiedFormalLCELInstance
      dpEmitterCertifiedFormalLCELInstance :=
  benchmark_dp_certifiedRouteLiftInputPackage.toBlueprint

/-- Route-lift blueprint assembled for the Gödel ↔ DP pair. -/
def godel_dp_certifiedRouteLiftBlueprint :
    CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint
      godel1931CertifiedFormalLCELInstance
      dpEmitterCertifiedFormalLCELInstance :=
  godel_dp_certifiedRouteLiftInputPackage.toBlueprint

/-- Route-lift blueprint assembled for the Gödel ↔ benchmark pair. -/
def godel_benchmark_certifiedRouteLiftBlueprint :
    CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint
      godel1931CertifiedFormalLCELInstance
      benchmarkTransportCertifiedFormalLCELInstance :=
  godel_benchmark_certifiedRouteLiftInputPackage.toBlueprint

/-- Benchmark ↔ DP residual package recovered from the supplied blueprint. -/
def benchmark_dp_certifiedRouteLiftResidualPackage :
    LCELRouteLiftResidualPackage
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  benchmark_dp_certifiedRouteLiftBlueprint.toResidualPackage

/-- Gödel ↔ DP residual package recovered from the supplied blueprint. -/
def godel_dp_certifiedRouteLiftResidualPackage :
    LCELRouteLiftResidualPackage
      godel1931LCELInstance
      dpEmitterLCELInstance :=
  godel_dp_certifiedRouteLiftBlueprint.toResidualPackage

/-- Gödel ↔ benchmark residual package recovered from the supplied blueprint. -/
def godel_benchmark_certifiedRouteLiftResidualPackage :
    LCELRouteLiftResidualPackage
      godel1931LCELInstance
      benchmarkTransportLCELInstance :=
  godel_benchmark_certifiedRouteLiftBlueprint.toResidualPackage

theorem benchmark_dp_hasRouteLiftResidualPackage :
    HasLCELRouteLiftResidualPackage
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  ⟨benchmark_dp_certifiedRouteLiftResidualPackage⟩

theorem godel_dp_hasRouteLiftResidualPackage :
    HasLCELRouteLiftResidualPackage
      godel1931LCELInstance
      dpEmitterLCELInstance :=
  ⟨godel_dp_certifiedRouteLiftResidualPackage⟩

theorem godel_benchmark_hasRouteLiftResidualPackage :
    HasLCELRouteLiftResidualPackage
      godel1931LCELInstance
      benchmarkTransportLCELInstance :=
  ⟨godel_benchmark_certifiedRouteLiftResidualPackage⟩

theorem benchmark_dp_admitsUnrestrictedWitness_viaCertifiedBlueprint :
    AdmitsLCELUnrestrictedWitness
      benchmarkTransportLCELInstance
      dpEmitterLCELInstance :=
  benchmark_dp_certifiedRouteLiftBlueprint.admitsUnrestrictedWitness

theorem godel_dp_admitsUnrestrictedWitness_viaCertifiedBlueprint :
    AdmitsLCELUnrestrictedWitness
      godel1931LCELInstance
      dpEmitterLCELInstance :=
  godel_dp_certifiedRouteLiftBlueprint.admitsUnrestrictedWitness

theorem godel_benchmark_admitsUnrestrictedWitness_viaCertifiedBlueprint :
    AdmitsLCELUnrestrictedWitness
      godel1931LCELInstance
      benchmarkTransportLCELInstance :=
  godel_benchmark_certifiedRouteLiftBlueprint.admitsUnrestrictedWitness

theorem benchmark_dp_witnessFreeStructuralIdentity_viaCertifiedBlueprint :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = benchmarkTransportLCELInstance
        ∧ A₂.instance_ = dpEmitterLCELInstance
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  benchmark_dp_certifiedRouteLiftBlueprint.witnessFreeStructuralIdentity

theorem godel_dp_witnessFreeStructuralIdentity_viaCertifiedBlueprint :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = godel1931LCELInstance
        ∧ A₂.instance_ = dpEmitterLCELInstance
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  godel_dp_certifiedRouteLiftBlueprint.witnessFreeStructuralIdentity

theorem godel_benchmark_witnessFreeStructuralIdentity_viaCertifiedBlueprint :
    ∃ A₁ A₂ : AdmissibleLCELInstance,
      A₁.instance_ = godel1931LCELInstance
        ∧ A₂.instance_ = benchmarkTransportLCELInstance
        ∧ Nonempty (LCELUniversalQuasiFunctor A₁ A₂) :=
  godel_benchmark_certifiedRouteLiftBlueprint.witnessFreeStructuralIdentity

/-- Finite catalog of the three named pairs carrying supplied route and
coherence data. Its scope is the listed benchmark ↔ DP, Gödel ↔ DP, and
Gödel ↔ benchmark pairs. -/
structure LCELP4CCanonicalBoundaryCatalog : Type 1 where
  godel1931 : CertifiedFormalLCELInstance
  benchmarkTransport : CertifiedFormalLCELInstance
  dpEmitter : CertifiedFormalLCELInstance
  godel_dp_blueprint :
    CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint
      godel1931
      dpEmitter
  godel_benchmark_blueprint :
    CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint
      godel1931
      benchmarkTransport
  benchmark_dp_blueprint :
    CertifiedFormalLCELInstance.CertifiedRouteLiftBlueprint
      benchmarkTransport
      dpEmitter

/-- Finite boundary catalog on the three named LCEL instances. Its fields are
the three pair-specific blueprints above. -/
def lcel_p4c_canonicalBoundaryCatalog : LCELP4CCanonicalBoundaryCatalog where
  godel1931 := godel1931CertifiedFormalLCELInstance
  benchmarkTransport := benchmarkTransportCertifiedFormalLCELInstance
  dpEmitter := dpEmitterCertifiedFormalLCELInstance
  godel_dp_blueprint := godel_dp_certifiedRouteLiftBlueprint
  godel_benchmark_blueprint := godel_benchmark_certifiedRouteLiftBlueprint
  benchmark_dp_blueprint := benchmark_dp_certifiedRouteLiftBlueprint

end OperatorKO7.LCELP4CCanonicalInstances
