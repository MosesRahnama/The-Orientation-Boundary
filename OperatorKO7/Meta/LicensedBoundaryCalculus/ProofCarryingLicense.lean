import OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryCompletion

/-!
# Proof-carrying forward license

The certificate is indexed by the exact request, output, capability role, and
verdict.  Public constructors carry independently meaningful boundary evidence;
there is no constructor that accepts a caller-supplied desired conclusion.
Provenance and replay evidence are derived from the certificate rather than
stored as arbitrary labels.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense

/-- Capability roles are type-level, so recovery evidence cannot be confused
with forward admission. -/
inductive CapabilityRole where
  | forward
  | recovery

/-- Verdict carried by the certificate index. -/
inductive LicenseVerdict where
  | authorize
  | refuse

/-- Exact forward request.  The raw edge is part of the request itself, not a
claim supplied later by a certificate constructor. -/
structure ForwardRequest {α : Type} (R : α → α → Prop) where
  source : α
  target : α
  rawEdge : R source target

/-- Typed, derived provenance class.  These are constructor identities, not
trust strings or authority claims. -/
inductive LicenseProvenance where
  | completedDynamics
  | persistentState
  | boundaryWitness

/-- Constructor-closed license indexed by exact request, output, role and verdict. -/
inductive ProofCarryingLicense {α : Type} (R : α → α → Prop) (P : α → Prop)
    (request : ForwardRequest R) : α → CapabilityRole → LicenseVerdict → Type
  | completedDynamics
      (evidence : SafeRel R P request.source request.target) :
      ProofCarryingLicense R P request request.target .forward .authorize
  | persistentState
      (evidence : Box R P request.source) :
      ProofCarryingLicense R P request request.target .forward .authorize
  | boundaryRefusal
      (evidence : BoundaryEdge R P request.source request.target) :
      ProofCarryingLicense R P request request.target .forward .refuse

namespace ProofCarryingLicense

/-- Provenance is generated from the evidence constructor; callers do not supply it. -/
def provenance {α : Type} {R : α → α → Prop} {P : α → Prop}
    {request : ForwardRequest R} {output : α} {role : CapabilityRole}
    {verdict : LicenseVerdict}
    (certificate : ProofCarryingLicense R P request output role verdict) :
    LicenseProvenance := by
  cases certificate with
  | completedDynamics => exact .completedDynamics
  | persistentState => exact .persistentState
  | boundaryRefusal => exact .boundaryWitness

/-- Every public certificate constructor is forward-role only. -/
theorem no_recovery_certificate {α : Type} {R : α → α → Prop} {P : α → Prop}
    {request : ForwardRequest R} {output : α} {verdict : LicenseVerdict}
    (certificate : ProofCarryingLicense R P request output .recovery verdict) : False := by
  cases certificate

/-- Same-output dependency is enforced by the output index. -/
theorem output_eq_request_target {α : Type} {R : α → α → Prop} {P : α → Prop}
    {request : ForwardRequest R} {output : α} {role : CapabilityRole}
    {verdict : LicenseVerdict}
    (certificate : ProofCarryingLicense R P request output role verdict) :
    output = request.target := by
  cases certificate <;> rfl

/-- Sound forward admission: every authorization constructor derives the exact
`SafeRel` evidence for the same request. -/
theorem authorized_safeRel {α : Type} {R : α → α → Prop} {P : α → Prop}
    {request : ForwardRequest R} {output : α}
    (certificate : ProofCarryingLicense R P request output .forward .authorize) :
    SafeRel R P request.source request.target := by
  cases certificate with
  | completedDynamics evidence => exact evidence
  | persistentState evidence =>
      refine ⟨request.rawEdge, ?_⟩
      intro _sourceLicensed
      exact evidence.persists request.target
        (Relation.ReflTransGen.single request.rawEdge)

/-- Authorization replay data are generated from exact request/evidence. -/
theorem replay_authorization {α : Type} {R : α → α → Prop} {P : α → Prop}
    {request : ForwardRequest R} {output : α}
    (certificate : ProofCarryingLicense R P request output .forward .authorize) :
    R request.source request.target ∧
      (P request.source → P request.target) :=
  authorized_safeRel certificate

/-- If the source is licensed, authorization derives the exact target license. -/
theorem authorized_target {α : Type} {R : α → α → Prop} {P : α → Prop}
    {request : ForwardRequest R} {output : α}
    (certificate : ProofCarryingLicense R P request output .forward .authorize)
    (hsource : P request.source) : P request.target :=
  (authorized_safeRel certificate).2 hsource

/-- Sound refusal: every refusal constructor returns the exact boundary edge for
that same request. -/
theorem refused_boundary {α : Type} {R : α → α → Prop} {P : α → Prop}
    {request : ForwardRequest R} {output : α}
    (certificate : ProofCarryingLicense R P request output .forward .refuse) :
    BoundaryEdge R P request.source request.target := by
  cases certificate with
  | boundaryRefusal evidence => exact evidence

/-- Refusal replay is likewise generated, not supplied as arbitrary metadata. -/
theorem replay_refusal {α : Type} {R : α → α → Prop} {P : α → Prop}
    {request : ForwardRequest R} {output : α}
    (certificate : ProofCarryingLicense R P request output .forward .refuse) :
    R request.source request.target ∧ P request.source ∧ ¬ P request.target :=
  refused_boundary certificate

/-- A genuine boundary-crossing request cannot have an authorization certificate. -/
theorem boundary_no_authorization {α : Type} {R : α → α → Prop} {P : α → Prop}
    (request : ForwardRequest R)
    (hboundary : BoundaryEdge R P request.source request.target) :
    ¬ Nonempty
      (ProofCarryingLicense R P request request.target .forward .authorize) := by
  rintro ⟨certificate⟩
  have hsafe := authorized_safeRel certificate
  exact hboundary.2.2 (hsafe.2 hboundary.2.1)

end ProofCarryingLicense

/-! ## Positive, refusal and cross-input fixtures -/

inductive LicenseFixtureState where
  | source
  | accepted
  | rejected

/-- Fixture dynamics has one accepted and one rejected edge from the same source. -/
def licenseFixtureStep (x y : LicenseFixtureState) : Prop :=
  x = LicenseFixtureState.source ∧
    (y = LicenseFixtureState.accepted ∨ y = LicenseFixtureState.rejected)

/-- Source and accepted target are licensed; rejected target is not. -/
def licenseFixturePredicate (x : LicenseFixtureState) : Prop :=
  x = LicenseFixtureState.source ∨ x = LicenseFixtureState.accepted

/-- Exact admitted request. -/
def admittedFixtureRequest : ForwardRequest licenseFixtureStep where
  source := .source
  target := .accepted
  rawEdge := ⟨rfl, Or.inl rfl⟩

/-- Exact rejected request. -/
def rejectedFixtureRequest : ForwardRequest licenseFixtureStep where
  source := .source
  target := .rejected
  rawEdge := ⟨rfl, Or.inr rfl⟩

/-- Positive nonvacuity: a safe request receives a constructor-derived forward license. -/
def admittedFixtureLicense :
    ProofCarryingLicense licenseFixtureStep licenseFixturePredicate
      admittedFixtureRequest LicenseFixtureState.accepted .forward .authorize :=
  .completedDynamics ⟨admittedFixtureRequest.rawEdge, fun _ => Or.inr rfl⟩

/-- Refusal nonvacuity: a boundary-crossing request receives typed refusal evidence. -/
def rejectedFixtureLicense :
    ProofCarryingLicense licenseFixtureStep licenseFixturePredicate
      rejectedFixtureRequest LicenseFixtureState.rejected .forward .refuse :=
  .boundaryRefusal
    ⟨rejectedFixtureRequest.rawEdge, Or.inl rfl,
      by rintro (h | h) <;> cases h⟩

/-- The rejected request cannot be authorized even though the same source has a
different admitted request. -/
theorem rejectedFixture_not_authorizable :
    ¬ Nonempty
      (ProofCarryingLicense licenseFixtureStep licenseFixturePredicate
        rejectedFixtureRequest LicenseFixtureState.rejected .forward .authorize) :=
  ProofCarryingLicense.boundary_no_authorization rejectedFixtureRequest
    ⟨rejectedFixtureRequest.rawEdge, Or.inl rfl,
      by rintro (h | h) <;> cases h⟩

/-- Cross-input negative fixture: evidence for one exact request does not certify
a distinct request merely because both can be mentioned together. -/
theorem same_input_dependency_fixture :
    Nonempty
      (ProofCarryingLicense licenseFixtureStep licenseFixturePredicate
        admittedFixtureRequest LicenseFixtureState.accepted .forward .authorize) ∧
    ¬ Nonempty
      (ProofCarryingLicense licenseFixtureStep licenseFixturePredicate
        rejectedFixtureRequest LicenseFixtureState.rejected .forward .authorize) :=
  ⟨⟨admittedFixtureLicense⟩, rejectedFixture_not_authorizable⟩

/-- Exact output dependency for the positive fixture. -/
theorem admittedFixture_output_is_request_target :
    LicenseFixtureState.accepted = admittedFixtureRequest.target :=
  ProofCarryingLicense.output_eq_request_target admittedFixtureLicense

end OperatorKO7.Meta.LicensedBoundaryCalculus
