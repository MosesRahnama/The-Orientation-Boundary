/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import OperatorKO7.Meta.ProofSearchBoundary.KlopTrace
import OperatorKO7.Meta.ProofSearchBoundary.O3Rho
import OperatorKO7.Meta.UniqueNormalization.ModelInfeasibility

/-!
# The five-axis grades of the calibrating specimens

The `(R, C, X, P, H)` axes (recognition, construction, transport, progress,
supervision) assigned to the calibrating specimens.  The values are
annotations transcribed from `HIGHER-BOUNDRY.md` lines 3708-3714:

* O3 corrected `rho` (`t2`): `(1, 1, 0, 0, 0)`.
* Report 9 celebration (`KlopTrace.s2`): `(1, 1, 0, 0, 0)`.
* Report 9 self-correction (`KlopTrace.s2withdraw`): `(1, 0, 1, 0, 1)`.
* F45 instance: `(1, 1, 1, 1, 0)`.

The theorems below back the coordinates that have a formal counterpart.
Recognition is backed only by membership of the blocker in the known list;
it records that the blocker was on the page, not that the author read it.  F45
recognition is annotation only.

`DiagnosticallyClosed` makes the diagnostic/prescription split measurable: at
the corrected O3 state and at the celebration, every applicable known blocker
is handled or audit-rejected while `Consumes` fails.

Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ProofSearchBoundary.Grades

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.ProofSearchBoundary
open OperatorKO7.Meta.ProofSearchBoundary.GroundedSupport
open OperatorKO7.Meta.ProofSearchBoundary.KlopTrace
open OperatorKO7.Meta.ProofSearchBoundary.O3Rho

/-- The five supervision axes of a proof-search state, mirrored from the
`EchoTrap` five-axis grade `(R, C, X, P, H)`. -/
structure GradeVector where
  recognition : Nat
  construction : Nat
  transport : Nat
  progress : Nat
  supervision : Nat
  deriving DecidableEq, Repr

/-- The diagnostic picture is complete at a state when every known applicable
blocker is either handled by the proposal or flagged by the audit. -/
def DiagnosticallyClosed
    {Target Constraint Obligation Proposal : Type}
    (Applicable :
      Constraint → Target → List Obligation → Proposal → Prop)
    (Handles :
      Constraint → Target → List Obligation → Proposal → Prop)
    (AuditRejects :
      Constraint → Target → List Obligation → Proposal → Prop)
    (s : ProofSearchState Target Constraint Obligation Proposal) : Prop :=
  ∀ k, k ∈ s.known →
    Applicable k s.target s.openObligations s.proposal →
      Handles k s.target s.openObligations s.proposal ∨
        AuditRejects k s.target s.openObligations s.proposal

/-! ## O3 corrected `rho`: grade `(1, 1, 0, 0, 0)` -/

/-- The assigned grade of the corrected O3 state `t2`. -/
def o3CorrectedGrade : GradeVector := ⟨1, 1, 0, 0, 0⟩

/-- Recognition: both constraints are on record at `t2`. -/
theorem o3Corrected_recognition :
    O3Constraint.kDup ∈ t2.known ∧ O3Constraint.kNested ∈ t2.known := by
  simp [t2, o3Blockers]

/-- Construction: a concrete proposal is on the table. -/
theorem o3Corrected_construction : t2.proposal = O3Proposal.correctedDup :=
  rfl

/-- Transport `0`: the corrected state does not consume its known
blockers. -/
theorem o3Corrected_transport : ¬ Consumes O3Applicable O3Handles t2 :=
  t2_not_consumes

/-- Progress `0`: the universal drop claim the correction makes is still
false. -/
theorem o3Corrected_progress :
    ∃ b s n : O3Term,
      (rho (O3Term.G s (O3Term.F b s n)) : ℤ) ≠
        (rho (O3Term.F b s (O3Term.succ n)) : ℤ) - 1 + (rho s : ℤ) :=
  correctedDup_identity_fails

/-- Supervision `0`: the state certifies without consuming. -/
theorem o3Corrected_supervision :
    UnsupportedPromotion O3Applicable O3Handles t2 :=
  t2_unsupportedPromotion

/-- The diagnostic/prescription split at the corrected O3 state. -/
theorem o3Corrected_diag_closed_presc_open :
    DiagnosticallyClosed O3Applicable O3Handles O3AuditRejects t2 ∧
      ¬ Consumes O3Applicable O3Handles t2 := by
  refine ⟨?_, t2_not_consumes⟩
  intro k hk happ
  cases k <;>
    simp [t2, o3Blockers, O3Applicable, O3Handles, O3AuditRejects] at happ ⊢

/-- The exact-identity state `t3` is the positive control: consumption holds,
the claimed identity is a theorem, and the polynomial orients the step. -/
theorem o3Exact_positive_control :
    Consumes O3Applicable O3Handles t3 ∧
      (∀ b s n : O3Term,
        ((rho (O3Term.G s (O3Term.F b s n)) : ℤ) -
            (rho (O3Term.F b s (O3Term.succ n)) : ℤ)) =
          (rho s : ℤ) + (eps n : ℤ) - 1) ∧
      (∀ b s n : O3Term,
        polyM (O3Term.G s (O3Term.F b s n)) <
          polyM (O3Term.F b s (O3Term.succ n))) :=
  ⟨t3_consumes, rho_exact_identity, polyM_step_strict⟩

/-! ## Report 9 celebration: grade `(1, 1, 0, 0, 0)` -/

/-- The assigned grade of the celebration `s2`. -/
def report9CelebrationGrade : GradeVector := ⟨1, 1, 0, 0, 0⟩

/-- Recognition: the transitivity obligation is on record and applicable at
`s2`. -/
theorem report9Celebration_recognition :
    ∃ k, k ∈ s2.known ∧
      Applicable k s2.target s2.openObligations s2.proposal :=
  ⟨.htransObligation, by simp [s2, blockers], trivial⟩

/-- Construction: the announced proof is a concrete proposal. -/
theorem report9Celebration_construction :
    s2.proposal = Proposal.celebrateKlopClosed :=
  rfl

/-- Transport `0`: the celebration does not consume. -/
theorem report9Celebration_transport :
    ¬ Consumes Applicable Handles s2 :=
  s2_not_consumes

/-- Progress `0`: the celebration's support derives no transitivity. -/
theorem report9Celebration_progress :
    ¬ HornDeriv celebrationFacts celebrationRules
      CelebrationNode.downTransitivity :=
  celebration_target_underivable.1

/-- Supervision `0`: the celebration certifies without consuming. -/
theorem report9Celebration_supervision :
    UnsupportedPromotion Applicable Handles s2 :=
  s2_unsupportedPromotion

/-- The diagnostic/prescription split at the celebration. -/
theorem report9Celebration_diag_closed_presc_open :
    DiagnosticallyClosed Applicable Handles AuditRejects s2 ∧
      ¬ Consumes Applicable Handles s2 := by
  refine ⟨?_, s2_not_consumes⟩
  intro k hk happ
  cases k
  · exact Or.inr trivial
  · exact happ.elim

/-! ## Report 9 self-correction: grade `(1, 0, 1, 0, 1)` -/

/-- The assigned grade of the self-correction `s2withdraw`. -/
def report9AuditGrade : GradeVector := ⟨1, 0, 1, 0, 1⟩

/-- Construction `0`: the self-correction keeps the celebration's proposal. -/
theorem report9Audit_no_new_construction : s2withdraw.proposal = s2.proposal :=
  rfl

/-- Transport `1`: the obligation is applied to the state's own proposal (the
audit rejects it). -/
theorem report9Audit_transport :
    AuditRejects .htransObligation
      s2withdraw.target s2withdraw.openObligations s2withdraw.proposal :=
  trivial

/-- The withdrawn state keeps the unhandled obligation.  It is licensed because
it no longer certifies (`s2withdraw_licensed`); under the refusal clause of the
manuscript's Definition 2.1 the withdrawal removes the promotion
(`downgrade_removes_promotion_with_refusal`). -/
theorem report9Audit_not_consumes :
    ¬ Consumes Applicable Handles s2withdraw :=
  s2withdraw_not_consumes

/-- Supervision `1`: the state withdraws, which licenses it, while the
obligation stays unhandled. -/
theorem report9Audit_supervision :
    Withdraws s2withdraw ∧ Licensed Applicable Handles s2withdraw ∧
      ¬ Consumes Applicable Handles s2withdraw :=
  ⟨rfl, s2withdraw_licensed, s2withdraw_not_consumes⟩

/-- Withdrawing the unlicensed proposal is not an unsupported demotion. -/
theorem report9Audit_not_unsupportedDemotion :
    ¬ UnsupportedDemotion Applicable Handles s2withdraw := by
  rintro ⟨_, hcons⟩
  exact s2withdraw_not_consumes hcons

/-! ## F45 instance: grade `(1, 1, 1, 1, 0)` -/

/-- The assigned grade of the F45 per-instance certificate. -/
def f45InstanceGrade : GradeVector := ⟨1, 1, 1, 1, 0⟩

/-- Transport `1`: the two-element Boolean model satisfies the rules and
refutes every overlap of the linearization. -/
theorem f45Instance_transport :
    OperatorKO7.Meta.UniqueNormalization.F45Certificate.model.RulesHold
        OperatorKO7.Meta.UniqueNormalization.F45Certificate.trs ∧
      OperatorKO7.Meta.UniqueNormalization.ModelRefutesOverlaps
        OperatorKO7.Meta.UniqueNormalization.F45Certificate.lin
        OperatorKO7.Meta.UniqueNormalization.F45Certificate.model :=
  ⟨OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_rulesHold,
    OperatorKO7.Meta.UniqueNormalization.F45Certificate.model_refutes⟩

/-- Progress `1`: the Boolean model yields `UNconv` for the F45 system. -/
theorem f45Instance_progress :
    OperatorKO7.Meta.UniqueNormalization.UNconv
      OperatorKO7.Meta.UniqueNormalization.F45Certificate.trs :=
  OperatorKO7.Meta.UniqueNormalization.F45Certificate.UNconv_trs

end OperatorKO7.Meta.ProofSearchBoundary.Grades
