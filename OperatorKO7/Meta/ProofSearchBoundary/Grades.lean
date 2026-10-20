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
# Five-axis grades of proof-search states

The grade vector records recognition, construction, transport, progress, and supervision. The values below are annotations:

* O3 state `t2`: `(1, 1, 0, 0, 0)`.
* Celebration state `KlopTrace.s2`: `(1, 1, 0, 0, 0)`.
* Withdrawn state `KlopTrace.s2withdraw`: `(1, 0, 1, 0, 1)`.
* The two-element Boolean model: `(1, 1, 1, 1, 0)`.

Several theorems below establish formal properties associated with these grades. Recognition is supported only by blocker membership in the known list; this shows that the model contains the blocker, not that a person read it. Recognition for the Boolean model is annotation only.

At the O3 state and the celebration state, every applicable known blocker is handled or rejected by the audit while `Consumes` fails.

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

/-- A proof-search state grade with coordinates for recognition, construction, transport, progress, and supervision. -/
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

/-! ## O3 state `t2`: grade `(1, 1, 0, 0, 0)` -/

/-- The grade assigned to O3 state `t2`. -/
def o3CorrectedGrade : GradeVector := ⟨1, 1, 0, 0, 0⟩

/-- Both constraints belong to the known list at `t2`. -/
theorem o3Corrected_recognition :
    O3Constraint.kDup ∈ t2.known ∧ O3Constraint.kNested ∈ t2.known := by
  simp [t2, o3Blockers]

/-- The state carries the concrete proposal `O3Proposal.correctedDup`. -/
theorem o3Corrected_construction : t2.proposal = O3Proposal.correctedDup :=
  rfl

/-- Transport `0`: the corrected state does not consume its known
blockers. -/
theorem o3Corrected_transport : ¬ Consumes O3Applicable O3Handles t2 :=
  t2_not_consumes

/-- Progress is zero because a concrete term instance violates the claimed universal drop equation. -/
theorem o3Corrected_progress :
    ∃ b s n : O3Term,
      (rho (O3Term.G s (O3Term.F b s n)) : ℤ) ≠
        (rho (O3Term.F b s (O3Term.succ n)) : ℤ) - 1 + (rho s : ℤ) :=
  correctedDup_identity_fails

/-- Supervision is zero because the certified state does not consume. -/
theorem o3Corrected_supervision :
    UnsupportedPromotion O3Applicable O3Handles t2 :=
  t2_unsupportedPromotion

/-- At `t2`, every applicable known blocker is handled or rejected by the audit, while `Consumes` fails. -/
theorem o3Corrected_diag_closed_presc_open :
    DiagnosticallyClosed O3Applicable O3Handles O3AuditRejects t2 ∧
      ¬ Consumes O3Applicable O3Handles t2 := by
  refine ⟨?_, t2_not_consumes⟩
  intro k hk happ
  cases k <;>
    simp [t2, o3Blockers, O3Applicable, O3Handles, O3AuditRejects] at happ ⊢

/-- State `t3` consumes, satisfies the identity for every term, and has `rho` orienting the rewrite step. -/
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

/-! ## Celebration state `s2`: grade `(1, 1, 0, 0, 0)` -/

/-- The grade assigned to celebration state `s2`. -/
def report9CelebrationGrade : GradeVector := ⟨1, 1, 0, 0, 0⟩

/-- The transitivity obligation belongs to the known list and applies at `s2`. -/
theorem report9Celebration_recognition :
    ∃ k, k ∈ s2.known ∧
      Applicable k s2.target s2.openObligations s2.proposal :=
  ⟨.htransObligation, by simp [s2, blockers], trivial⟩

/-- The state carries the proposal `Proposal.celebrateKlopClosed`. -/
theorem report9Celebration_construction :
    s2.proposal = Proposal.celebrateKlopClosed :=
  rfl

/-- Transport `0`: the celebration does not consume. -/
theorem report9Celebration_transport :
    ¬ Consumes Applicable Handles s2 :=
  s2_not_consumes

/-- Progress is zero because the supplied facts do not derive `CelebrationNode.downTransitivity`. -/
theorem report9Celebration_progress :
    ¬ HornDeriv celebrationFacts celebrationRules
      CelebrationNode.downTransitivity :=
  celebration_target_underivable.1

/-- Supervision is zero because the certified state does not consume. -/
theorem report9Celebration_supervision :
    UnsupportedPromotion Applicable Handles s2 :=
  s2_unsupportedPromotion

/-- At `s2`, every applicable known blocker is handled or rejected by the audit, while `Consumes` fails. -/
theorem report9Celebration_diag_closed_presc_open :
    DiagnosticallyClosed Applicable Handles AuditRejects s2 ∧
      ¬ Consumes Applicable Handles s2 := by
  refine ⟨?_, s2_not_consumes⟩
  intro k hk happ
  cases k
  · exact Or.inr trivial
  · exact happ.elim

/-! ## Withdrawal state `s2withdraw`: grade `(1, 0, 1, 0, 1)` -/

/-- The grade assigned to withdrawn state `s2withdraw`. -/
def report9AuditGrade : GradeVector := ⟨1, 0, 1, 0, 1⟩

/-- Construction is zero because the withdrawn state retains the celebration proposal. -/
theorem report9Audit_no_new_construction : s2withdraw.proposal = s2.proposal :=
  rfl

/-- Transport is one because the audit rejects the state's proposal on the transitivity obligation. -/
theorem report9Audit_transport :
    AuditRejects .htransObligation
      s2withdraw.target s2withdraw.openObligations s2withdraw.proposal :=
  trivial

/-- The withdrawn state keeps the transitivity obligation unhandled and is licensed because it no longer certifies, as shown by `s2withdraw_licensed`. Under the refusal condition, withdrawal removes the promotion, as stated by `downgrade_removes_promotion_with_refusal`. -/
theorem report9Audit_not_consumes :
    ¬ Consumes Applicable Handles s2withdraw :=
  s2withdraw_not_consumes

/-- Supervision is one because the state withdraws and is licensed while the obligation remains unhandled. -/
theorem report9Audit_supervision :
    Withdraws s2withdraw ∧ Licensed Applicable Handles s2withdraw ∧
      ¬ Consumes Applicable Handles s2withdraw :=
  ⟨rfl, s2withdraw_licensed, s2withdraw_not_consumes⟩

/-- The withdrawal is not an unsupported demotion. -/
theorem report9Audit_not_unsupportedDemotion :
    ¬ UnsupportedDemotion Applicable Handles s2withdraw := by
  rintro ⟨_, hcons⟩
  exact s2withdraw_not_consumes hcons

/-! ## Finite Boolean model: grade `(1, 1, 1, 1, 0)` -/

/-- The grade assigned to the two-element Boolean model. -/
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

/-- Progress is one because the two-element Boolean model proves `UNconv` for its rewrite system. -/
theorem f45Instance_progress :
    OperatorKO7.Meta.UniqueNormalization.UNconv
      OperatorKO7.Meta.UniqueNormalization.F45Certificate.trs :=
  OperatorKO7.Meta.UniqueNormalization.F45Certificate.UNconv_trs

end OperatorKO7.Meta.ProofSearchBoundary.Grades
