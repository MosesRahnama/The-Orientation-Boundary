/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
import OperatorKO7.Meta.LicensedBoundaryCalculus.FailureObject

/-!
# The diagnostic-consumption boundary on proof search

`ProofSearchState` contains a target, known constraints, open obligations, a proposal, and its claim status.

`Consumes` means every known applicable blocker is handled. `PrescriptionPersistent` means the source consumes and every state reachable through `NextProposal` consumes.

`SelfApplicationGap` means a known constraint applies to the state's proposal and a sound audit rejects that proposal. A sound gap refutes `Consumes`; a reachable gap refutes persistence. A trace from a consuming source to a gap yields a `FailureObject` for the first crossing.

`CorrectionDischarges` means an old known, applicable, unhandled constraint is handled by the revised proposal or ceases to apply. `PromotionMigrates` means the same constraint is known, applicable, and unhandled at both the old and revised states.

`UnsupportedPromotion` and `UnsupportedDemotion` express two status mismatches: certification without consumption, and withdrawal despite consumption.

Trust: kernel only, Mathlib baseline; generic theorems are axiom-free.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ProofSearchBoundary

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.LicensedBoundaryCalculus

/-- Claim status attached to a proposal. -/
inductive ClaimStatus where
  | «open»
  | conditional
  | certified
  | withdrawn
  deriving DecidableEq, Repr

/-- A proof-search state: target theorem, known certified constraints and
refutations, currently open obligations, the current proposed proof move, and
the claim status attached to that proposal. -/
structure ProofSearchState
    (Target Constraint Obligation Proposal : Type) where
  target : Target
  known : List Constraint
  openObligations : List Obligation
  proposal : Proposal
  status : ClaimStatus

variable {Target Constraint Obligation Proposal : Type}

/-- Every known blocker applicable to the current prescription is handled by
that prescription. -/
def Consumes
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  ∀ k, k ∈ s.known →
    Applicable k s.target s.openObligations s.proposal →
      Handles k s.target s.openObligations s.proposal

/-- The prescription consumes every applicable blocker now and at every state
reachable under the proposal dynamics. -/
def PrescriptionPersistent
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  Box NextProposal (Consumes Applicable Handles) s

/-- Failure of prescription persistence at a currently consuming source is
exactly existence of a proof-relevant first-crossing `FailureObject`. -/
theorem not_prescriptionPersistent_iff_exists_failureObject
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    [DecidablePred (Consumes Applicable Handles)]
    {source : ProofSearchState Target Constraint Obligation Proposal}
    (hsource : Consumes Applicable Handles source) :
    (¬ PrescriptionPersistent
        Applicable Handles NextProposal source) ↔
      ∃ endpoint path,
        Nonempty
          (FailureObject
            NextProposal
            (Consumes Applicable Handles)
            source endpoint path) := by
  exact
    FailureObject.not_box_iff_exists_failureObject_classical
      hsource

/-- For an explicit failed proposal trace, extraction of the first
constraint-consumption failure is constructive. -/
theorem failureObject_of_explicit_trace
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    [DecidablePred (Consumes Applicable Handles)]
    {source endpoint :
      ProofSearchState Target Constraint Obligation Proposal}
    (path : FinitePath NextProposal source endpoint)
    (hsource : Consumes Applicable Handles source)
    (hend : ¬ Consumes Applicable Handles endpoint) :
    Nonempty
      (FailureObject
        NextProposal
        (Consumes Applicable Handles)
        source endpoint path) := by
  exact FailureObject.of_explicit_path path hsource hend

/-- Audit rejection is sound when rejection under a blocker means the proposal
does not handle that blocker. -/
def AuditSound
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (AuditRejects :
      Constraint → Target → List Obligation → Proposal → Prop) : Prop :=
  ∀ k T O h,
    AuditRejects k T O h →
      ¬ Handles k T O h

/-- A self-application gap: a blocker already known to the proof-search state
applies to the state's own proposal, and the audit rejects that same proposal
under that blocker. -/
def SelfApplicationGap
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (AuditRejects :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  ∃ k,
    k ∈ s.known ∧
    Applicable k s.target s.openObligations s.proposal ∧
    AuditRejects k s.target s.openObligations s.proposal

/-- Exact proposal transition at which diagnostic consumption is lost. -/
def DiagnosticConsumptionBoundary
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    (x y : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  BoundaryEdge NextProposal (Consumes Applicable Handles) x y

/-- A soundly audited self-application gap cannot satisfy `Consumes`. -/
theorem selfApplicationGap_not_consumes
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (AuditRejects :
      Constraint → Target → List Obligation → Proposal → Prop)
    (hAudit : AuditSound Handles AuditRejects)
    {s : ProofSearchState Target Constraint Obligation Proposal}
    (hgap : SelfApplicationGap Applicable AuditRejects s) :
    ¬ Consumes Applicable Handles s := by
  intro hConsumes
  rcases hgap with ⟨k, hk, happ, hrejected⟩
  exact
    hAudit k s.target s.openObligations s.proposal hrejected
      (hConsumes k hk happ)

/-- A reachable self-application gap refutes prescription persistence at the
source.  No decidability assumption is needed: `Box.persists` supplies
`Consumes` at the gap state directly. -/
theorem selfApplicationGap_implies_not_prescriptionPersistent
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (AuditRejects :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    (hAudit : AuditSound Handles AuditRejects)
    {source gap :
      ProofSearchState Target Constraint Obligation Proposal}
    (hreach : Relation.ReflTransGen NextProposal source gap)
    (hgap : SelfApplicationGap Applicable AuditRejects gap) :
    ¬ PrescriptionPersistent Applicable Handles NextProposal source := by
  intro hpersistent
  have hgapConsumes : Consumes Applicable Handles gap :=
    hpersistent.persists gap hreach
  exact
    selfApplicationGap_not_consumes
      Applicable Handles AuditRejects hAudit hgap
      hgapConsumes

/-- An explicit proposal trace from a consuming source to a self-application
gap contains a canonical first diagnostic-consumption boundary.  The returned
`FailureObject` stores the all-consuming prefix, the last consuming state, the
first non-consuming state, the exact crossing proposal edge, and the remaining
suffix. -/
theorem selfApplicationGap_implies_first_diagnosticConsumption_boundary
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (AuditRejects :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    (hAudit : AuditSound Handles AuditRejects)
    [DecidablePred (Consumes Applicable Handles)]
    {source gap :
      ProofSearchState Target Constraint Obligation Proposal}
    (path : FinitePath NextProposal source gap)
    (hsource : Consumes Applicable Handles source)
    (hgap : SelfApplicationGap Applicable AuditRejects gap) :
    ∃ f :
        FailureObject
          NextProposal
          (Consumes Applicable Handles)
          source gap path,
      DiagnosticConsumptionBoundary
        Applicable Handles NextProposal
        f.lastSafe f.firstFail := by
  have hend : ¬ Consumes Applicable Handles gap :=
    selfApplicationGap_not_consumes
      Applicable Handles AuditRejects hAudit hgap
  rcases
      FailureObject.of_explicit_path path hsource hend
    with ⟨f⟩
  exact ⟨f, f.crossing⟩

/-- Any reachable self-application gap from a currently consuming source yields
an exact proof-relevant failure trace ending at that gap, and therefore refutes
prescription persistence at the source.  The embedded `FailureObject`
identifies the first diagnostic-consumption boundary along the recovered finite
path. -/
theorem
    reachable_selfApplicationGap_yields_failureObject_and_refutes_persistence
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (AuditRejects :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    (hAudit : AuditSound Handles AuditRejects)
    [DecidablePred (Consumes Applicable Handles)]
    {source gap :
      ProofSearchState Target Constraint Obligation Proposal}
    (hsource : Consumes Applicable Handles source)
    (hreach : Relation.ReflTransGen NextProposal source gap)
    (hgap : SelfApplicationGap Applicable AuditRejects gap) :
    (∃ path,
      Nonempty
        (FailureObject
          NextProposal
          (Consumes Applicable Handles)
          source gap path)) ∧
      ¬ PrescriptionPersistent
        Applicable Handles NextProposal source := by
  have hend : ¬ Consumes Applicable Handles gap :=
    selfApplicationGap_not_consumes
      Applicable Handles AuditRejects hAudit hgap
  have hnotPersistent :
      ¬ PrescriptionPersistent
        Applicable Handles NextProposal source :=
    selfApplicationGap_implies_not_prescriptionPersistent
      Applicable Handles AuditRejects NextProposal
      hAudit hreach hgap
  rcases FinitePath.nonempty_ofReflTransGen hreach with ⟨path⟩
  have hfailure :
      Nonempty
        (FailureObject
          NextProposal
          (Consumes Applicable Handles)
          source gap path) :=
    FailureObject.of_explicit_path path hsource hend
  exact ⟨⟨path, hfailure⟩, hnotPersistent⟩

/-! ## Correction retention versus promotion migration -/

/-- `CorrectionDischarges` holds when `k` was known, applicable, and unhandled before revision, and the revised proposal handles `k` or `k` no longer applies. -/
def CorrectionDischarges
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (k : Constraint)
    (s s' : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  k ∈ s.known ∧
    Applicable k s.target s.openObligations s.proposal ∧
    ¬ Handles k s.target s.openObligations s.proposal ∧
    (Handles k s'.target s'.openObligations s'.proposal ∨
      ¬ Applicable k s'.target s'.openObligations s'.proposal)

/-- `PromotionMigrates` holds when `k` is known, applicable, and unhandled at both the old and revised states. -/
def PromotionMigrates
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (k : Constraint)
    (s s' : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  k ∈ s.known ∧
    Applicable k s.target s.openObligations s.proposal ∧
    ¬ Handles k s.target s.openObligations s.proposal ∧
    k ∈ s'.known ∧
    Applicable k s'.target s'.openObligations s'.proposal ∧
    ¬ Handles k s'.target s'.openObligations s'.proposal

/-- A migrating correction leaves the revised state non-consuming. -/
theorem promotionMigrates_not_consumes
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    {k : Constraint}
    {s s' : ProofSearchState Target Constraint Obligation Proposal}
    (hmig : PromotionMigrates Applicable Handles k s s') :
    ¬ Consumes Applicable Handles s' := by
  intro hConsumes
  rcases hmig with ⟨_, _, _, hk', happ', hnh'⟩
  exact hnh' (hConsumes k hk' happ')

/-- Migration and discharge are exclusive: the same constraint cannot be both
carried through and removed by one revision. -/
theorem not_correctionDischarges_of_promotionMigrates
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    {k : Constraint}
    {s s' : ProofSearchState Target Constraint Obligation Proposal}
    (hmig : PromotionMigrates Applicable Handles k s s') :
    ¬ CorrectionDischarges Applicable Handles k s s' := by
  rcases hmig with ⟨_, _, _, _, happ', hnh'⟩
  rintro ⟨_, _, _, hdis⟩
  rcases hdis with hhandled | hnotapp
  · exact hnh' hhandled
  · exact hnotapp happ'

/-- If the audit soundly rejects the revised proposal under the migrated
constraint, the revised state is a self-application gap. -/
theorem selfApplicationGap_of_promotionMigrates
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (AuditRejects :
      Constraint → Target → List Obligation → Proposal → Prop)
    {k : Constraint}
    {s s' : ProofSearchState Target Constraint Obligation Proposal}
    (hmig : PromotionMigrates Applicable Handles k s s')
    (hrejected :
      AuditRejects k s'.target s'.openObligations s'.proposal) :
    SelfApplicationGap Applicable AuditRejects s' := by
  rcases hmig with ⟨_, _, _, hk', happ', _⟩
  exact ⟨k, hk', happ', hrejected⟩

/-! ## Claim status: unsupported promotion and unsupported demotion -/

/-- A state has a certified claim status. -/
def Commits (s : ProofSearchState Target Constraint Obligation Proposal) :
    Prop :=
  s.status = ClaimStatus.certified

/-- The state withdraws its proposal. -/
def Withdraws (s : ProofSearchState Target Constraint Obligation Proposal) :
    Prop :=
  s.status = ClaimStatus.withdrawn

/-- A state is licensed when certification implies consumption. -/
def Licensed
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  Commits s → Consumes Applicable Handles s

/-- An unsupported promotion: the proposal is certified while a known
applicable blocker remains unhandled. -/
def UnsupportedPromotion
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  Commits s ∧ ¬ Consumes Applicable Handles s

/-- An unsupported demotion: the proposal is withdrawn although every known
applicable blocker is handled. -/
def UnsupportedDemotion
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  Withdraws s ∧ Consumes Applicable Handles s

/-- An unsupported promotion is exactly a certified state that is not licensed. -/
theorem unsupportedPromotion_iff_not_licensed_and_commits
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) :
    UnsupportedPromotion Applicable Handles s ↔
      Commits s ∧ ¬ Licensed Applicable Handles s := by
  constructor
  · rintro ⟨hcommit, hnot⟩
    exact ⟨hcommit, fun hlic => hnot (hlic hcommit)⟩
  · rintro ⟨hcommit, hnotlic⟩
    exact ⟨hcommit, fun hcons => hnotlic (fun _ => hcons)⟩

/-- No state is both an unsupported promotion and an unsupported demotion. -/
theorem unsupportedPromotion_disjoint_unsupportedDemotion
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) :
    ¬ (UnsupportedPromotion Applicable Handles s ∧
        UnsupportedDemotion Applicable Handles s) := by
  rintro ⟨⟨hcert, _⟩, hwith, _⟩
  rw [Commits] at hcert
  rw [Withdraws] at hwith
  rw [hcert] at hwith
  cases hwith

/-- An explicit trace from a consuming source to an unsupported promotion
contains a canonical first diagnostic-consumption boundary. -/
theorem unsupportedPromotion_yields_first_diagnosticConsumption_boundary
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    [DecidablePred (Consumes Applicable Handles)]
    {source endpoint :
      ProofSearchState Target Constraint Obligation Proposal}
    (path : FinitePath NextProposal source endpoint)
    (hsource : Consumes Applicable Handles source)
    (hup : UnsupportedPromotion Applicable Handles endpoint) :
    ∃ f :
        FailureObject
          NextProposal
          (Consumes Applicable Handles)
          source endpoint path,
      DiagnosticConsumptionBoundary
        Applicable Handles NextProposal
        f.lastSafe f.firstFail := by
  rcases FailureObject.of_explicit_path path hsource hup.2 with ⟨f⟩
  exact ⟨f, f.crossing⟩

/-! ## License and consumption

`Licensed` requires consumption only when a state is certified, so an open or conditional state may remain licensed while applicable requirements are unhandled. `PrescriptionPersistent` instead requires `Consumes` at the source and every reachable state; a reachable open, non-consuming state refutes it.
-/

/-- `Commits` is decidable because claim statuses have decidable equality. -/
instance commitsDecidable
    (s : ProofSearchState Target Constraint Obligation Proposal) :
    Decidable (Commits s) :=
  inferInstanceAs (Decidable (s.status = ClaimStatus.certified))

/-- The license is decidable whenever consumption is. -/
instance licensedDecidable
    {Applicable :
      Constraint → Target → List Obligation → Proposal → Prop}
    {Handles :
      Constraint → Target → List Obligation → Proposal → Prop}
    [DecidablePred (Consumes Applicable Handles)] :
    DecidablePred (Licensed Applicable Handles) := fun s =>
  inferInstanceAs (Decidable (Commits s → Consumes Applicable Handles s))

/-- An unsupported promotion is equivalent to an unlicensed state. The proof splits on decidable claim status and uses no classical axiom. -/
theorem unsupportedPromotion_iff_not_licensed
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) :
    UnsupportedPromotion Applicable Handles s ↔
      ¬ Licensed Applicable Handles s := by
  constructor
  · rintro ⟨hcommit, hnot⟩ hlic
    exact hnot (hlic hcommit)
  · intro hnotlic
    by_cases hcommit : Commits s
    · exact ⟨hcommit, fun hcons => hnotlic (fun _ => hcons)⟩
    · exact absurd (fun h => absurd h hcommit) hnotlic

/-- A state that does not certify is licensed. -/
theorem licensed_of_not_commits
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    {s : ProofSearchState Target Constraint Obligation Proposal}
    (hs : ¬ Commits s) : Licensed Applicable Handles s :=
  fun hc => absurd hc hs

/-- A state that does not certify is never an unsupported promotion, regardless of its open obligations. -/
theorem not_unsupportedPromotion_of_not_commits
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    {s : ProofSearchState Target Constraint Obligation Proposal}
    (hs : ¬ Commits s) : ¬ UnsupportedPromotion Applicable Handles s :=
  fun hup => hs hup.1

/-- A certified state with a soundly rejected, known, applicable blocker is an unsupported promotion. -/
theorem certified_selfApplicationGap_unsupportedPromotion
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (AuditRejects :
      Constraint → Target → List Obligation → Proposal → Prop)
    (hAudit : AuditSound Handles AuditRejects)
    {s : ProofSearchState Target Constraint Obligation Proposal}
    (hcommit : Commits s)
    (hgap : SelfApplicationGap Applicable AuditRejects s) :
    UnsupportedPromotion Applicable Handles s :=
  ⟨hcommit, selfApplicationGap_not_consumes Applicable Handles AuditRejects
    hAudit hgap⟩

/-- Persistent licensing requires every state reachable under `NextProposal` to be licensed. -/
def PersistentLicensed
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  Box NextProposal (Licensed Applicable Handles) s

/-- A reachable unsupported promotion refutes persistent licensing at the source. -/
theorem reachable_unsupportedPromotion_not_persistentLicensed
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    {source endpoint :
      ProofSearchState Target Constraint Obligation Proposal}
    (hreach : Relation.ReflTransGen NextProposal source endpoint)
    (hup : UnsupportedPromotion Applicable Handles endpoint) :
    ¬ PersistentLicensed Applicable Handles NextProposal source :=
  fun hpers => hup.2 (hpers.persists endpoint hreach hup.1)

/-- An explicit trace from a licensed source to an unsupported promotion yields a `FailureObject` for `Licensed`, with the licensed prefix, last licensed state, first unlicensed state, and crossing edge. The first unlicensed state is an unsupported promotion. -/
theorem first_unsupportedPromotion_boundary
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (NextProposal :
      ProofSearchState Target Constraint Obligation Proposal →
      ProofSearchState Target Constraint Obligation Proposal → Prop)
    [DecidablePred (Licensed Applicable Handles)]
    {source endpoint :
      ProofSearchState Target Constraint Obligation Proposal}
    (path : FinitePath NextProposal source endpoint)
    (hsource : Licensed Applicable Handles source)
    (hup : UnsupportedPromotion Applicable Handles endpoint) :
    ∃ f :
        FailureObject NextProposal (Licensed Applicable Handles)
          source endpoint path,
      BoundaryEdge NextProposal (Licensed Applicable Handles)
          f.lastSafe f.firstFail ∧
        UnsupportedPromotion Applicable Handles f.firstFail := by
  rcases FailureObject.of_explicit_path path hsource
      ((unsupportedPromotion_iff_not_licensed Applicable Handles endpoint).mp
        hup) with ⟨f⟩
  exact ⟨f, f.crossing,
    (unsupportedPromotion_iff_not_licensed Applicable Handles f.firstFail).mpr
      f.crossing.2.2⟩

/-! ## Active defects, resolution, and migration -/

/-- `Bad` contains the known constraints that apply and remain unhandled. -/
def Bad
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal)
    (k : Constraint) : Prop :=
  k ∈ s.known ∧
    Applicable k s.target s.openObligations s.proposal ∧
    ¬ Handles k s.target s.openObligations s.proposal

/-- Consumption is emptiness of the active defect set. -/
theorem consumes_iff_no_bad
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) :
    Consumes Applicable Handles s ↔ ∀ k, ¬ Bad Applicable Handles s k := by
  constructor
  · rintro hcons k ⟨hk, happ, hnot⟩
    exact hnot (hcons k hk happ)
  · intro hno k hk happ
    exact Classical.byContradiction (fun hnot => hno k ⟨hk, happ, hnot⟩)

/-- `Resolves` holds when the revised state handles the prior defect or the defect no longer applies. -/
def Resolves
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (k : Constraint)
    (s' : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  Handles k s'.target s'.openObligations s'.proposal ∨
    ¬ Applicable k s'.target s'.openObligations s'.proposal

/-- `CorrectionRemovesPromotion` holds when the revision resolves every active defect of the old state and is licensed. -/
def CorrectionRemovesPromotion
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s s' : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  (∀ k, Bad Applicable Handles s k → Resolves Applicable Handles k s') ∧
    Licensed Applicable Handles s'

/-- `CertifiedPromotionMigration` holds when a prior defect still applies and remains unhandled in the revised certified state. The revised state need not retain the defect in its known list. -/
def CertifiedPromotionMigration
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (k : Constraint)
    (s s' : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  Bad Applicable Handles s k ∧ Commits s' ∧
    Applicable k s'.target s'.openObligations s'.proposal ∧
    ¬ Handles k s'.target s'.openObligations s'.proposal

/-- A certified migration blocks removal of the promotion. -/
theorem certifiedPromotionMigration_not_removes
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    {k : Constraint}
    {s s' : ProofSearchState Target Constraint Obligation Proposal}
    (hmig : CertifiedPromotionMigration Applicable Handles k s s') :
    ¬ CorrectionRemovesPromotion Applicable Handles s s' := by
  rintro ⟨hres, -⟩
  rcases hmig with ⟨hbad, -, happ', hnot'⟩
  rcases hres k hbad with hh | hna
  · exact hnot' hh
  · exact hna happ'

/-- A certified migration whose defect stays on record is an unsupported
promotion at the revised state. -/
theorem certifiedPromotionMigration_unsupportedPromotion
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    {k : Constraint}
    {s s' : ProofSearchState Target Constraint Obligation Proposal}
    (hmig : CertifiedPromotionMigration Applicable Handles k s s')
    (hk : k ∈ s'.known) :
    UnsupportedPromotion Applicable Handles s' :=
  ⟨hmig.2.1, fun hcons => hmig.2.2.2 (hcons k hk hmig.2.2.1)⟩

/-- A certified migration whose defect stays on record is a tracked migration
in the sense of `PromotionMigrates`. -/
theorem promotionMigrates_of_certifiedPromotionMigration
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    {k : Constraint}
    {s s' : ProofSearchState Target Constraint Obligation Proposal}
    (hmig : CertifiedPromotionMigration Applicable Handles k s s')
    (hk : k ∈ s'.known) :
    PromotionMigrates Applicable Handles k s s' :=
  ⟨hmig.1.1, hmig.1.2.1, hmig.1.2.2, hk, hmig.2.2.1, hmig.2.2.2⟩

/-! ## Refusal as handling

`ConsumesWithRefusal` treats refusal to certify as handling every applicable known blocker. Under this predicate, consumption is equivalent to `Licensed`, and every non-certified state resolves prior defects. Without this refusal condition, a revision that keeps its target, obligations, and proposal does not remove an active promotion.
-/

/-- Consumption with the refusal clause: each applicable known blocker is
handled, or the state does not certify. -/
def ConsumesWithRefusal
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  ∀ k, k ∈ s.known →
    Applicable k s.target s.openObligations s.proposal →
      Handles k s.target s.openObligations s.proposal ∨ ¬ Commits s

/-- With the refusal clause, consumption coincides with the license. -/
theorem consumesWithRefusal_iff_licensed
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) :
    ConsumesWithRefusal Applicable Handles s ↔
      Licensed Applicable Handles s := by
  constructor
  · intro h hcommit k hk happ
    rcases h k hk happ with hh | hno
    · exact hh
    · exact absurd hcommit hno
  · intro hlic k hk happ
    by_cases hcommit : Commits s
    · exact Or.inl (hlic hcommit k hk happ)
    · exact Or.inr hcommit

/-- Resolution with the refusal clause. -/
def ResolvesWithRefusal
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (k : Constraint)
    (s' : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  Resolves Applicable Handles k s' ∨ ¬ Commits s'

/-- With the refusal clause, every downgrade from certification resolves every
prior defect and is licensed. -/
theorem downgrade_removes_promotion_with_refusal
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    {s s' : ProofSearchState Target Constraint Obligation Proposal}
    (hs' : ¬ Commits s') :
    (∀ k, Bad Applicable Handles s k →
        ResolvesWithRefusal Applicable Handles k s') ∧
      Licensed Applicable Handles s' :=
  ⟨fun _ _ => Or.inr hs', licensed_of_not_commits Applicable Handles hs'⟩

/-- Without the refusal clause, a revision that keeps the target, the
obligations, and the proposal does not remove a promotion that has an active
defect. -/
theorem sameProposal_not_correctionRemovesPromotion
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    {s s' : ProofSearchState Target Constraint Obligation Proposal}
    (htarget : s'.target = s.target)
    (hobl : s'.openObligations = s.openObligations)
    (hprop : s'.proposal = s.proposal)
    {k : Constraint} (hbad : Bad Applicable Handles s k) :
    ¬ CorrectionRemovesPromotion Applicable Handles s s' := by
  rintro ⟨hres, -⟩
  rcases hres k hbad with hh | hna
  · rw [htarget, hobl, hprop] at hh
    exact hbad.2.2 hh
  · rw [htarget, hobl, hprop] at hna
    exact hna hbad.2.1

end OperatorKO7.Meta.ProofSearchBoundary
