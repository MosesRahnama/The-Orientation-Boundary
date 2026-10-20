/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.BoundaryGeneral.EchoLaw
import OperatorKO7.Meta.ProofSearchBoundary.Grades

/-!
# The echo-law adapter for proof search

`psEpisode` instantiates `EchoLaw.Episode` with proof-search states, constraints as objects, audit rejection as the Boolean answer, claim statuses as records, and `Consumes` as the distinction. Its raw surface emits the state's status, and its licensed surface emits that status only when the state is licensed.

`UnsupportedPromotion` is equivalent to `FalseFormalLegitimacyAt` for this episode. The equivalence follows from the licensed surface definition. The theorem `psEpisode_objectWitnessed_excludes_echo` shows that `ObjectWitnessed` and an echo state cannot hold together: clearing an echo state's known list preserves its answers and makes `Consumes` vacuous.

## Grade adapters

`EchoTrapGrade5` records five Boolean grading axes. `EchoTrapGrade` records four axes, with execution defined as the conjunction of transport and progress.

Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ProofSearchBoundary.EchoTrapAdapter

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.ProofSearchBoundary
open OperatorKO7.Meta.BoundaryGeneral.EchoLaw

variable {Target Constraint Obligation Proposal : Type}
  (Applicable : Constraint → Target → List Obligation → Proposal → Prop)
  (Handles : Constraint → Target → List Obligation → Proposal → Prop)
  (AuditRejects : Constraint → Target → List Obligation → Proposal → Prop)
  [∀ (k : Constraint) (T : Target) (O : List Obligation) (h : Proposal),
    Decidable (AuditRejects k T O h)]

/-- The episode induced by a proof-search development. -/
def psEpisode : Episode where
  State := ProofSearchState Target Constraint Obligation Proposal
  Object := Constraint
  Answer := Bool
  Record := ClaimStatus
  null := .«open»
  nonnull := fun r => r = .certified
  answer := fun s k => decide (AuditRejects k s.target s.openObligations s.proposal)
  Distinction := fun s => Consumes Applicable Handles s
  rawEmits := fun s r => s.status = r
  licensedEmits := fun s r => s.status = r ∧ Licensed Applicable Handles s

/-- The induced episode is distinction-sound. -/
theorem psEpisode_licensedSound :
    LicensedSound (psEpisode Applicable Handles AuditRejects) := by
  intro s r hemit hn
  have hr : r = ClaimStatus.certified := hn
  subst hr
  exact hemit.2 hemit.1

/-- The null record is null. -/
theorem psEpisode_null_not_nonnull :
    ¬ (psEpisode Applicable Handles AuditRejects).nonnull
        (psEpisode Applicable Handles AuditRejects).null :=
  fun h => ClaimStatus.noConfusion h

/-- An unsupported promotion is exactly a false-formal-legitimacy state of the
induced episode. -/
theorem unsupportedPromotion_iff_falseFormalLegitimacy
    {s : ProofSearchState Target Constraint Obligation Proposal} :
    UnsupportedPromotion Applicable Handles s ↔
      FalseFormalLegitimacyAt (psEpisode Applicable Handles AuditRejects) s := by
  constructor
  · rintro ⟨hcommit, hnot⟩
    refine ⟨⟨.certified, hcommit, rfl⟩, ?_⟩
    rintro ⟨r, ⟨hstat, hlic⟩, hn⟩
    subst hn
    exact hnot (hlic hstat)
  · rintro ⟨⟨r, hraw, hn⟩, hnot⟩
    subst hn
    exact ⟨hraw, fun hcons => hnot ⟨.certified, ⟨hraw, fun _ => hcons⟩, rfl⟩⟩

/-- The echo law's hypotheses cannot hold together on `psEpisode`: if the
distinction is object-witnessed, no state is an echo.  Clearing the known list
of an echo state keeps its answers and makes it consume vacuously. -/
theorem psEpisode_objectWitnessed_excludes_echo
    (hwit : ObjectWitnessed (psEpisode Applicable Handles AuditRejects))
    (s : ProofSearchState Target Constraint Obligation Proposal) :
    ¬ EchoAt (psEpisode Applicable Handles AuditRejects) s := by
  intro hecho
  have hcons : Consumes Applicable Handles { s with known := [] } := by
    intro k hk
    simp at hk
  have hinf := hwit { s with known := [] } hcons
  have hecho' : EchoAt (psEpisode Applicable Handles AuditRejects)
      { s with known := [] } := fun o o' => hecho o o'
  exact (echoAt_iff_not_informativeAt _ _).mp hecho' hinf

/-! ## The KlopTrace instance -/

/-- Decidability of `KlopTrace.AuditRejects` by finite case analysis. -/
instance klopAuditDecidable : ∀ (k : KlopTrace.Constraint) (T : KlopTrace.Target)
    (O : List KlopTrace.Obligation) (h : KlopTrace.Proposal),
    Decidable (KlopTrace.AuditRejects k T O h)
  | .htransObligation, _, _, .proposeTwoLevelShift => isFalse (fun hf => hf)
  | .htransObligation, _, _, .buildCrossRuleRefutation => isTrue trivial
  | .htransObligation, _, _, .celebrateKlopClosed => isTrue trivial
  | .htransObligation, _, _, .recommendRationalTree => isFalse (fun hf => hf)
  | .uniformConstructionOwed, _, _, .proposeTwoLevelShift =>
      isFalse (fun hf => hf)
  | .uniformConstructionOwed, _, _, .buildCrossRuleRefutation =>
      isFalse (fun hf => hf)
  | .uniformConstructionOwed, _, _, .celebrateKlopClosed =>
      isFalse (fun hf => hf)
  | .uniformConstructionOwed, _, _, .recommendRationalTree => isTrue trivial

/-- The KlopTrace episode. -/
def klopEpisode : Episode :=
  psEpisode KlopTrace.Applicable KlopTrace.Handles KlopTrace.AuditRejects

/-- The `KlopTrace.s2` state satisfies `FalseFormalLegitimacyAt`. -/
theorem s2_false_formal_legitimacy :
    FalseFormalLegitimacyAt klopEpisode KlopTrace.s2 :=
  (unsupportedPromotion_iff_falseFormalLegitimacy
    KlopTrace.Applicable KlopTrace.Handles KlopTrace.AuditRejects).mp
    KlopTrace.s2_unsupportedPromotion

/-- The channel at the celebration is informative: the audit answers
differently on the two known obligations. -/
theorem s2_channel_informative : InformativeAt klopEpisode KlopTrace.s2 :=
  ⟨.htransObligation, .uniformConstructionOwed, by
    show decide (KlopTrace.AuditRejects .htransObligation
        KlopTrace.s2.target KlopTrace.s2.openObligations KlopTrace.s2.proposal) ≠
      decide (KlopTrace.AuditRejects .uniformConstructionOwed
        KlopTrace.s2.target KlopTrace.s2.openObligations KlopTrace.s2.proposal)
    decide⟩

/-- The withdrawn state is not false formally legitimate: its raw surface
emits only the withdrawn status, which is null. -/
theorem s2withdraw_no_false_formal_legitimacy :
    ¬ FalseFormalLegitimacyAt klopEpisode KlopTrace.s2withdraw := by
  rintro ⟨⟨r, hraw, hn⟩, -⟩
  subst hn
  exact absurd hraw (by
    show ¬ (KlopTrace.s2withdraw.status = ClaimStatus.certified)
    decide)

/-! ## The O3 instance -/

/-- Decidability of the O3 audit, by exhaustion. -/
instance o3AuditDecidable : ∀ (k : O3Rho.O3Constraint) (T : O3Rho.O3Target)
    (O : List O3Rho.O3Obligation) (h : O3Rho.O3Proposal),
    Decidable (O3Rho.O3AuditRejects k T O h)
  | .kDup, _, _, .diagnose => isFalse (fun hf => hf)
  | .kDup, _, _, .naiveDrop => isTrue trivial
  | .kDup, _, _, .correctedDup => isFalse (fun hf => hf)
  | .kDup, _, _, .exactIdentity => isFalse (fun hf => hf)
  | .kNested, _, _, .diagnose => isFalse (fun hf => hf)
  | .kNested, _, _, .naiveDrop => isTrue trivial
  | .kNested, _, _, .correctedDup => isTrue trivial
  | .kNested, _, _, .exactIdentity => isFalse (fun hf => hf)

/-! ## The O3 instance -/
def o3Episode : Episode :=
  psEpisode O3Rho.O3Applicable O3Rho.O3Handles O3Rho.O3AuditRejects

/-- The `O3Rho.t2` state satisfies `FalseFormalLegitimacyAt`. -/
theorem t2_false_formal_legitimacy :
    FalseFormalLegitimacyAt o3Episode O3Rho.t2 :=
  (unsupportedPromotion_iff_falseFormalLegitimacy
    O3Rho.O3Applicable O3Rho.O3Handles O3Rho.O3AuditRejects).mp
    O3Rho.t2_unsupportedPromotion

/-! ## Grade adapters -/

/-- Five-axis grade representation derived from `Grades.GradeVector`. -/
structure EchoTrapGrade5 where
  R : Bool
  C : Bool
  X : Bool
  P : Bool
  H : Bool
  deriving DecidableEq, Repr

/-- Coordinatewise map into the five-axis mirror. -/
def toEchoTrapGrade5 (v : Grades.GradeVector) : EchoTrapGrade5 where
  R := v.recognition != 0
  C := v.construction != 0
  X := v.transport != 0
  P := v.progress != 0
  H := v.supervision != 0

theorem celebration_grade5_maps :
    toEchoTrapGrade5 Grades.report9CelebrationGrade =
      ⟨true, true, false, false, false⟩ := by
  decide

theorem o3_corrected_grade5_maps :
    toEchoTrapGrade5 Grades.o3CorrectedGrade =
      ⟨true, true, false, false, false⟩ := by
  decide

theorem audit_grade5_maps :
    toEchoTrapGrade5 Grades.report9AuditGrade =
      ⟨true, false, true, false, true⟩ := by
  decide

theorem f45_grade5_maps :
    toEchoTrapGrade5 Grades.f45InstanceGrade =
      ⟨true, true, true, true, false⟩ := by
  decide

/-- Four-axis grade representation derived from `Grades.GradeVector`. -/
structure EchoTrapGrade where
  /-- The blocker was recognized. -/
  recognition : Bool
  /-- A concrete proposal was constructed. -/
  construction : Bool
  /-- The proposal executed: transport with progress. -/
  execution : Bool
  /-- The audit supervised the episode. -/
  supervision : Bool
  deriving DecidableEq, Repr

/-- The four-axis projection maps execution to the conjunction of transport and progress. -/
def toEchoTrapGrade (v : Grades.GradeVector) : EchoTrapGrade where
  recognition := v.recognition != 0
  construction := v.construction != 0
  execution := (v.transport != 0) && (v.progress != 0)
  supervision := v.supervision != 0

theorem celebration_grade_maps :
    toEchoTrapGrade Grades.report9CelebrationGrade =
      ⟨true, true, false, false⟩ := by
  decide

theorem o3_corrected_grade_maps :
    toEchoTrapGrade Grades.o3CorrectedGrade = ⟨true, true, false, false⟩ := by
  decide

theorem audit_grade_maps :
    toEchoTrapGrade Grades.report9AuditGrade = ⟨true, false, false, true⟩ := by
  decide

theorem f45_grade_maps :
    toEchoTrapGrade Grades.f45InstanceGrade = ⟨true, true, true, false⟩ := by
  decide

/-- The celebration, classified: an unsupported promotion, a
false-formal-legitimacy state, graded `(1, 1, 0, 0, 0)`. -/
theorem celebration_full_classification :
    UnsupportedPromotion KlopTrace.Applicable KlopTrace.Handles KlopTrace.s2 ∧
      FalseFormalLegitimacyAt klopEpisode KlopTrace.s2 ∧
      toEchoTrapGrade5 Grades.report9CelebrationGrade =
        ⟨true, true, false, false, false⟩ :=
  ⟨KlopTrace.s2_unsupportedPromotion, s2_false_formal_legitimacy,
    celebration_grade5_maps⟩

/-- Classification of the O3 state `t2`. -/
theorem o3_corrected_full_classification :
    UnsupportedPromotion O3Rho.O3Applicable O3Rho.O3Handles O3Rho.t2 ∧
      FalseFormalLegitimacyAt o3Episode O3Rho.t2 ∧
      toEchoTrapGrade5 Grades.o3CorrectedGrade =
        ⟨true, true, false, false, false⟩ :=
  ⟨O3Rho.t2_unsupportedPromotion, t2_false_formal_legitimacy,
    o3_corrected_grade5_maps⟩

end OperatorKO7.Meta.ProofSearchBoundary.EchoTrapAdapter
