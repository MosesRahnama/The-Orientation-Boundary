import OperatorKO7.Meta.LicensedBoundaryCalculus.Audit.ClaimKind
import OperatorKO7.Meta.LicensedBoundaryCalculus.Audit.AnchorVerificationElab

/-!
# Release-grade manuscript claim entries

Every source row carries one evidence-bearing verification status.  A live Lean
row stores the resolved `Lean.Name`, the full pretty-printed declaration type,
and the transitive axiom receipt captured from the imported environment.
Unresolved rows are explicit citation, analogy, runtime, or no-transport
records.  `pendingVerification` has no release inhabitant.

## Audit slots

Relation: exact source occurrence to a live declaration or a named block.
Closure: release status, source digest, scope fields, and optional transport key.
Trust: kernel checks the registry predicates; declaration capture is build-time metaprogramming.
Scope: exact governance crosswalk, not an automatic proof that prose and formal types are synonymous.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.Audit

inductive ManuscriptID
  | distinctionBoundary
  | operationalInexpressibilityQuant
  | licensedBoundaryCalculus
  | boundaryOperatorFramework
  deriving DecidableEq, Repr

/-- A typed and executable specification of what would falsify an analogy. -/
structure TypedFalsifierSpec where
  witnessType : String
  check : Nat -> Bool
  violatesClaim : Nat -> Prop
  check_sound : ∀ witness, check witness = true -> violatesClaim witness
  description : String
  description_nonempty : description ≠ ""

/-- Generic source-level counterexample test.  The checker is deliberately
conservative: concrete lanes may refine it, but it never guesses a failure. -/
def sourceCounterexampleFalsifier (description : String)
    (hdescription : description ≠ "") : TypedFalsifierSpec where
  witnessType := "encoded finite source-domain instance"
  check := fun _ => false
  violatesClaim := fun _ => False
  check_sound := by simp
  description := description
  description_nonempty := hdescription

structure ClaimEntry where
  manuscript : ManuscriptID
  claimID : String
  sourceLine : Nat
  sourceEnvironment : String
  statementDigest : String
  exactStatementRef : String
  relation : String
  closure : String
  strategy : String
  assumptions : String
  scope : String
  axiomFootprint : String
  kind : ClaimKind
  verification : VerificationStatus
  leanAnchor : Option String
  leanVerification : Option LeanAnchorVerification
  sourceCitation : Option String
  falsifier : Option TypedFalsifierSpec
  missingTransport : Option String
  runtimeSurface : Option String
  transportKey : Option TransportClaimKey

def ClaimEntry.HasReleaseStatus (entry : ClaimEntry) : Prop :=
  entry.exactStatementRef ≠ "" ∧
  entry.relation ≠ "" ∧
  entry.closure ≠ "" ∧
  entry.strategy ≠ "" ∧
  entry.assumptions ≠ "" ∧
  entry.scope ≠ "" ∧
  entry.axiomFootprint ≠ "" ∧
  match entry.verification with
  | .verifiedLean =>
      ∃ requested receipt,
        entry.leanAnchor = some requested ∧
        entry.leanVerification = some receipt ∧
        receipt.requested = requested ∧
        requested ≠ "" ∧
        receipt.prettyType ≠ ""
  | .verifiedExternal =>
      ∃ citation, entry.sourceCitation = some citation ∧ citation ≠ ""
  | .sourceDefinition => entry.kind = .definition
  | .analogyWithFalsifier =>
      ∃ spec, entry.falsifier = some spec
  | .explicitNoTransport =>
      ∃ missing, entry.missingTransport = some missing ∧ missing ≠ ""
  | .runtimeEvidenceRequired =>
      ∃ surface, entry.runtimeSurface = some surface ∧ surface ≠ ""
  | .pendingVerification => False

structure ClassifiedClaim where
  entry : ClaimEntry
  releaseStatus : entry.HasReleaseStatus

def EveryClaimExactlyVerifiedOrExplicitlyBlocked
    (registry : List ClassifiedClaim) : Prop :=
  ∀ row, row ∈ registry -> row.entry.HasReleaseStatus

def NoPendingClaims (registry : List ClassifiedClaim) : Prop :=
  ∀ row, row ∈ registry ->
    row.entry.verification ≠ .pendingVerification

/-- Only a pending row is an unresolved release discrepancy. Explicit
no-transport, citation, and analogy rows are resolved honesty outcomes. -/
def ClaimEntry.unresolvedDiscrepancySeverity
    (entry : ClaimEntry) : Option DiscrepancySeverity :=
  match entry.verification with
  | .pendingVerification => some .critical
  | _ => none

def NoUnresolvedCriticalOrHighClaims
    (registry : List ClassifiedClaim) : Prop :=
  ∀ row, row ∈ registry -> ∀ severity,
    row.entry.unresolvedDiscrepancySeverity = some severity ->
      ¬ severity.IsCriticalOrHigh

def ClaimEntry.RequiresTransport (entry : ClaimEntry) : Prop :=
  ∃ key, entry.transportKey = some key

theorem classifiedClaim_has_release_status (row : ClassifiedClaim) :
    row.entry.HasReleaseStatus :=
  row.releaseStatus

private def baseEntry
    (manuscript : ManuscriptID) (claimID : String) (sourceLine : Nat)
    (sourceEnvironment statementDigest : String)
    (kind : ClaimKind) (verification : VerificationStatus)
    (transportKey : Option TransportClaimKey) : ClaimEntry :=
  { manuscript := manuscript
    claimID := claimID
    sourceLine := sourceLine
    sourceEnvironment := sourceEnvironment
    statementDigest := statementDigest
    exactStatementRef :=
      "Normalized source statement in the generated CSV row keyed by manuscript, line, claim ID, and digest."
    relation := "Relation and quantifiers are those in the keyed source statement."
    closure := "Closure is limited to the hypotheses written in the keyed source statement."
    strategy := "Verification status and evidence are carried by this row."
    assumptions := "All explicit and implicit source assumptions remain in force."
    scope := "No scope beyond the keyed source statement and captured declaration type."
    axiomFootprint := "For Lean rows, use the captured transitive axiom receipt; other rows make no Lean proof claim."
    kind := kind
    verification := verification
    leanAnchor := none
    leanVerification := none
    sourceCitation := none
    falsifier := none
    missingTransport := none
    runtimeSurface := none
    transportKey := transportKey }

private theorem resolutionGap_nonempty (suffix : String) :
    "exact_live_declaration_resolution_for:" ++ suffix ≠ "" := by
  intro h
  have hlength := congrArg String.length h
  have hprefix : "exact_live_declaration_resolution_for:".length ≠ 0 := by
    decide
  have hparts :
      "exact_live_declaration_resolution_for:".length = 0 ∧
        suffix.length = 0 := by
    simpa using hlength
  exact hprefix hparts.1

private theorem sourceGap_nonempty (suffix : String) :
    "missing_source_theorem:" ++ suffix ≠ "" := by
  intro h
  have hlength := congrArg String.length h
  have hprefix : "missing_source_theorem:".length ≠ 0 := by
    decide
  have hparts :
      "missing_source_theorem:".length = 0 ∧ suffix.length = 0 := by
    simpa using hlength
  exact hprefix hparts.1

private theorem sourceCitation_nonempty (suffix : String) :
    "source_citation:" ++ suffix ≠ "" := by
  intro h
  have hlength := congrArg String.length h
  have hprefix : "source_citation:".length ≠ 0 := by
    decide
  have hparts :
      "source_citation:".length = 0 ∧ suffix.length = 0 := by
    simpa using hlength
  exact hprefix hparts.1

/-- Source definitions are release-complete as definitions and make no theorem
claim.  A separate Lean-anchor occurrence, when present, receives its own live
declaration row. -/
def definitionClaim
    (manuscript : ManuscriptID) (claimID : String) (sourceLine : Nat)
    (sourceEnvironment statementDigest : String)
    (transportKey : Option TransportClaimKey) : ClassifiedClaim where
  entry :=
    { baseEntry manuscript claimID sourceLine sourceEnvironment statementDigest
        .definition .sourceDefinition transportKey with
      strategy := "Source definition; no theorem promotion."
      axiomFootprint := "No proof claim is made by this source-definition row." }
  releaseStatus := by
    simp [ClaimEntry.HasReleaseStatus, baseEntry]

/-- A theorem or anchor backed by a live declaration.  Missing or ambiguous
resolution is converted to an explicit named no-transport row. -/
def leanBackedClaim
    (manuscript : ManuscriptID) (claimID : String) (sourceLine : Nat)
    (sourceEnvironment statementDigest requestedAnchor : String)
    (resolution : Option LeanAnchorVerification)
    (transportKey : Option TransportClaimKey) : ClassifiedClaim :=
  match resolution with
  | some receipt =>
      { entry :=
          { baseEntry manuscript claimID sourceLine sourceEnvironment
              statementDigest
              (if receipt.declarationKind = .proposition then
                .objectTheorem else .constructionData)
              .verifiedLean transportKey with
            strategy :=
              "Live-name resolution plus captured full declaration type and transitive axiom receipt."
            axiomFootprint :=
              "Exact transitive axiom names are stored in leanVerification.axiomReceipt."
            leanAnchor := some receipt.requested
            leanVerification := some receipt }
        releaseStatus := by
          simp [ClaimEntry.HasReleaseStatus, baseEntry]
          exact ⟨receipt.requested_nonempty, receipt.prettyType_nonempty⟩ }
  | none =>
      { entry :=
          { baseEntry manuscript claimID sourceLine sourceEnvironment
              statementDigest .noTransport .explicitNoTransport transportKey with
            strategy := "Explicit block: the requested Lean anchor is missing or ambiguous in the release import surface."
            leanAnchor := some requestedAnchor
            missingTransport := some
              ("exact_live_declaration_resolution_for:" ++ requestedAnchor) }
        releaseStatus := by
          simp [ClaimEntry.HasReleaseStatus, baseEntry]
          exact resolutionGap_nonempty requestedAnchor }

/-- A theorem-like source row without an attached Lean declaration. -/
def blockedTheoremClaim
    (manuscript : ManuscriptID) (claimID : String) (sourceLine : Nat)
    (sourceEnvironment statementDigest missing : String)
    (transportKey : Option TransportClaimKey) : ClassifiedClaim where
  entry :=
    { baseEntry manuscript claimID sourceLine sourceEnvironment statementDigest
        .noTransport .explicitNoTransport transportKey with
      strategy := "Explicit no-transport; no theorem language is licensed by this row."
      missingTransport := some ("missing_source_theorem:" ++ missing) }
  releaseStatus := by
    simp [ClaimEntry.HasReleaseStatus, baseEntry]
    exact sourceGap_nonempty missing

/-- A source theorem carried by an external citation, without Lean promotion. -/
def externalClaim
    (manuscript : ManuscriptID) (claimID : String) (sourceLine : Nat)
    (sourceEnvironment statementDigest citation : String)
    (transportKey : Option TransportClaimKey) : ClassifiedClaim where
  entry :=
    { baseEntry manuscript claimID sourceLine sourceEnvironment statementDigest
        .externalCitation .verifiedExternal transportKey with
      strategy := "External statement retained at citation strength."
      sourceCitation := some ("source_citation:" ++ citation) }
  releaseStatus := by
    simp [ClaimEntry.HasReleaseStatus, baseEntry]
    exact sourceCitation_nonempty citation

/-- A conjecture or prediction with a typed, executable falsifier interface. -/
def analogyClaim
    (manuscript : ManuscriptID) (claimID : String) (sourceLine : Nat)
    (sourceEnvironment statementDigest : String)
    (transportKey : Option TransportClaimKey) : ClassifiedClaim where
  entry :=
    { baseEntry manuscript claimID sourceLine sourceEnvironment statementDigest
        .analogy .analogyWithFalsifier transportKey with
      strategy := "Duck-rule candidate held at ANALOGY until its transport obligation is proved."
      falsifier := some (sourceCounterexampleFalsifier
        "A source-domain instance satisfying the premises and violating the conclusion falsifies this candidate."
        (by decide)) }
  releaseStatus := by
    simp [ClaimEntry.HasReleaseStatus, baseEntry]

#check classifiedClaim_has_release_status
#check definitionClaim
#check leanBackedClaim
#check blockedTheoremClaim
#check externalClaim
#check analogyClaim
#print axioms classifiedClaim_has_release_status

end OperatorKO7.Meta.LicensedBoundaryCalculus.Audit
