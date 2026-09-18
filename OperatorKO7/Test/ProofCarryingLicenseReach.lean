import OperatorKO7.Meta.LicensedBoundaryCalculus.ProofCarryingLicense

set_option autoImplicit false

open OperatorKO7.Meta.LicensedBoundaryCalculus

#check @CapabilityRole
#check @CapabilityRole.forward
#check @CapabilityRole.recovery
#check @LicenseVerdict
#check @LicenseVerdict.authorize
#check @LicenseVerdict.refuse
#check @ForwardRequest
#check @ForwardRequest.mk
#check @ForwardRequest.source
#check @ForwardRequest.target
#check @ForwardRequest.rawEdge
#check @LicenseProvenance
#check @LicenseProvenance.completedDynamics
#check @LicenseProvenance.persistentState
#check @LicenseProvenance.boundaryWitness
#check @ProofCarryingLicense
#check @ProofCarryingLicense.completedDynamics
#check @ProofCarryingLicense.persistentState
#check @ProofCarryingLicense.boundaryRefusal
#check @ProofCarryingLicense.provenance
#check @ProofCarryingLicense.no_recovery_certificate
#check @ProofCarryingLicense.output_eq_request_target
#check @ProofCarryingLicense.authorized_safeRel
#check @ProofCarryingLicense.replay_authorization
#check @ProofCarryingLicense.authorized_target
#check @ProofCarryingLicense.refused_boundary
#check @ProofCarryingLicense.replay_refusal
#check @ProofCarryingLicense.boundary_no_authorization
#check @LicenseFixtureState
#check @LicenseFixtureState.source
#check @LicenseFixtureState.accepted
#check @LicenseFixtureState.rejected
#check @licenseFixtureStep
#check @licenseFixturePredicate
#check @admittedFixtureRequest
#check @rejectedFixtureRequest
#check @admittedFixtureLicense
#check @rejectedFixtureLicense
#check @rejectedFixture_not_authorizable
#check @same_input_dependency_fixture
#check @admittedFixture_output_is_request_target

#print axioms CapabilityRole
#print axioms CapabilityRole.forward
#print axioms CapabilityRole.recovery
#print axioms LicenseVerdict
#print axioms LicenseVerdict.authorize
#print axioms LicenseVerdict.refuse
#print axioms ForwardRequest
#print axioms ForwardRequest.mk
#print axioms ForwardRequest.source
#print axioms ForwardRequest.target
#print axioms ForwardRequest.rawEdge
#print axioms LicenseProvenance
#print axioms LicenseProvenance.completedDynamics
#print axioms LicenseProvenance.persistentState
#print axioms LicenseProvenance.boundaryWitness
#print axioms ProofCarryingLicense
#print axioms ProofCarryingLicense.completedDynamics
#print axioms ProofCarryingLicense.persistentState
#print axioms ProofCarryingLicense.boundaryRefusal
#print axioms ProofCarryingLicense.provenance
#print axioms ProofCarryingLicense.no_recovery_certificate
#print axioms ProofCarryingLicense.output_eq_request_target
#print axioms ProofCarryingLicense.authorized_safeRel
#print axioms ProofCarryingLicense.replay_authorization
#print axioms ProofCarryingLicense.authorized_target
#print axioms ProofCarryingLicense.refused_boundary
#print axioms ProofCarryingLicense.replay_refusal
#print axioms ProofCarryingLicense.boundary_no_authorization
#print axioms LicenseFixtureState
#print axioms LicenseFixtureState.source
#print axioms LicenseFixtureState.accepted
#print axioms LicenseFixtureState.rejected
#print axioms licenseFixtureStep
#print axioms licenseFixturePredicate
#print axioms admittedFixtureRequest
#print axioms rejectedFixtureRequest
#print axioms admittedFixtureLicense
#print axioms rejectedFixtureLicense
#print axioms rejectedFixture_not_authorizable
#print axioms same_input_dependency_fixture
#print axioms admittedFixture_output_is_request_target
