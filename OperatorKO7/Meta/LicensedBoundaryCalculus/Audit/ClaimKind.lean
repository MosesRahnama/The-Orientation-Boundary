/-!
This module defines a finite claim-classification vocabulary and list fixtures. The declarations
classify metadata and establish list membership and length facts.










-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.Audit

inductive ClaimKind
  | objectTheorem
  | conditionalTheorem
  | definition
  | constructionData
  | finiteFixture
  | externalCitation
  | analogy
  | noTransport
  | runtimeClaim
  deriving DecidableEq, Repr

/-- Carrier with the constructors displayed below.

-/
inductive VerificationStatus
  | verifiedLean
  | verifiedExternal
  | sourceDefinition
  | analogyWithFalsifier
  | explicitNoTransport
  | runtimeEvidenceRequired
  | pendingVerification
  deriving DecidableEq, Repr

/-- Carrier with the constructors displayed below.
-/
inductive DiscrepancySeverity
  | low
  | medium
  | high
  | critical
  deriving DecidableEq, Repr

def DiscrepancySeverity.IsCriticalOrHigh : DiscrepancySeverity -> Prop
  | .high | .critical => True
  | .low | .medium => False

/-- Carrier with the constructors displayed below. -/
inductive TransportClaimKey
  | orientationFace
  | distinctionFace
  | observerQuotient
  | normalization
  | dependencyPairProjection
  | qecFiniteAdmission
  | supervisoryEngine
  | finiteMeasurementCarrier
  | landauerThermalErasure
  | quantumMeasurement
  | gravityUUET
  | financePlug
  | lawPlug
  | chemistryPlug
  | riemannHypothesisAnalogy
  deriving DecidableEq, Repr

def allClaimKinds : List ClaimKind :=
  [ .objectTheorem, .conditionalTheorem, .definition,
    .constructionData, .finiteFixture, .externalCitation,
    .analogy, .noTransport, .runtimeClaim ]

theorem allClaimKinds_length_fixture : allClaimKinds.length = 9 := by
  rfl

def allTransportClaimKeys : List TransportClaimKey :=
  [ .orientationFace, .distinctionFace, .observerQuotient, .normalization,
    .dependencyPairProjection, .qecFiniteAdmission, .supervisoryEngine,
    .finiteMeasurementCarrier, .landauerThermalErasure, .quantumMeasurement,
    .gravityUUET, .financePlug, .lawPlug, .chemistryPlug,
    .riemannHypothesisAnalogy ]

theorem allTransportClaimKeys_length_fixture :
    allTransportClaimKeys.length = 15 := by
  rfl

#check allClaimKinds_length_fixture
#print axioms allClaimKinds_length_fixture
#check allTransportClaimKeys_length_fixture
#print axioms allTransportClaimKeys_length_fixture

end OperatorKO7.Meta.LicensedBoundaryCalculus.Audit
