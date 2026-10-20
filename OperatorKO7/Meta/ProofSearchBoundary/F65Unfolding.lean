/-
Copyright (c) 2026 Moses Rahnama. All rights reserved.
Source-available; see the file LICENSE. Free for individual research;
departmental academic use and commercial use require a paid license.
Authors: Moses Rahnama
-/
import Mathlib.Tactic
import OperatorKO7.Meta.ProofSearchBoundary.Grades
import OperatorKO7.Meta.ProofSearchBoundary.GroundedSupport
import OperatorKO7.Meta.UniqueNormalization.SemiEquationalConfluence

/-!
# Residual condition and unique normal forms

The theorem `UNconv_of_linHub_noFeasibleOverlap` derives unique normal forms from `NoFeasibleOverlap (linHub R) (cconv (linHub R))`.

For the rewrite rules `f(x,x) -> a` and `f(c,d) -> b`, the residual condition forces `c` and `d` to be non-convertible. Since both terms are distinct normal forms, this gives a concrete unique-normal-form instance. The proof-search episode represents a certified reduction claim and its withdrawal. The residual condition fails for `Controls.linHuet` and `Controls.linKO7`, which each admit a feasible overlap.

Trust: kernel only, Mathlib baseline.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.ProofSearchBoundary.F65Unfolding

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.ProofSearchBoundary
open OperatorKO7.Meta.ProofSearchBoundary.Grades
open OperatorKO7.Meta.ProofSearchBoundary.GroundedSupport
open OperatorKO7.Meta.Rewriting
open OperatorKO7.Meta.UniqueNormalization
open scoped Subst

/-! ## Proof-search state -/

/-- The target is the unique-normal-form property. -/
inductive F65Target where
  | problem79UN
  deriving DecidableEq, Repr

/-- The blocker concerns the proposed reduction to a smaller statement. The residual implies a unique-normal-form instance at `c` and `d`, as shown by `f65_residual_contains_UN_instance`; the reduction therefore needs a proof that the residual is strictly weaker. -/
inductive F65Constraint where
  | kSelfContainment
  deriving DecidableEq, Repr

/-- The outstanding obligation is to establish unique normal forms. -/
inductive F65Obligation where
  | dischargeProblem79
  deriving DecidableEq, Repr

/-- The proposals assert the reduction or withdraw it. -/
inductive F65Proposal where
  | reduceToLinHubNoFeasibleOverlap
  | withdrawReduction
  deriving DecidableEq, Repr

/-- The blocker applies to the reduction claim. -/
def F65Applicable : F65Constraint → F65Target → List F65Obligation →
    F65Proposal → Prop
  | .kSelfContainment, _, _, .reduceToLinHubNoFeasibleOverlap => True
  | _, _, _, _ => False

/-- No proposal of the episode supplies a reason the residual is smaller. -/
def F65Handles : F65Constraint → F65Target → List F65Obligation →
    F65Proposal → Prop :=
  fun _ _ _ _ => False

/-- The audit rejects the reduction claim. -/
def F65AuditRejects : F65Constraint → F65Target → List F65Obligation →
    F65Proposal → Prop
  | .kSelfContainment, _, _, .reduceToLinHubNoFeasibleOverlap => True
  | _, _, _, _ => False

/-- The blocking constraint. -/
def f65Blockers : List F65Constraint := [.kSelfContainment]

/-- The outstanding unique-normal-form obligation. -/
def f65Obligations : List F65Obligation := [.dischargeProblem79]

/-- The certified proposal claims that the residual discharges the unique-normal-form obligation. -/
def f65Propose : ProofSearchState F65Target F65Constraint F65Obligation
    F65Proposal where
  target := .problem79UN
  known := f65Blockers
  openObligations := f65Obligations
  proposal := .reduceToLinHubNoFeasibleOverlap
  status := .certified

/-- The withdrawn state: the same proposal, withdrawn. -/
def f65Withdraw : ProofSearchState F65Target F65Constraint F65Obligation
    F65Proposal :=
  { f65Propose with status := .withdrawn }

/-! ## Boundary theorems -/

theorem f65Propose_not_consumes :
    ¬ Consumes F65Applicable F65Handles f65Propose :=
  fun h => h .kSelfContainment (by simp [f65Propose, f65Blockers]) trivial

theorem f65Withdraw_not_consumes :
    ¬ Consumes F65Applicable F65Handles f65Withdraw :=
  fun h => h .kSelfContainment
    (by simp [f65Withdraw, f65Propose, f65Blockers]) trivial

theorem f65Withdraw_licensed : Licensed F65Applicable F65Handles f65Withdraw :=
  licensed_of_not_commits _ _ (by simp [Commits, f65Withdraw, f65Propose])

theorem f65Audit_sound : AuditSound F65Handles F65AuditRejects :=
  fun _ _ _ _ _ hh => hh

theorem f65Propose_selfApplicationGap :
    SelfApplicationGap F65Applicable F65AuditRejects f65Propose :=
  ⟨.kSelfContainment, by simp [f65Propose, f65Blockers], trivial, trivial⟩

/-- The claiming state certifies without consuming. -/
theorem f65Propose_unsupportedPromotion :
    UnsupportedPromotion F65Applicable F65Handles f65Propose :=
  ⟨rfl, f65Propose_not_consumes⟩

/-- The withdrawn state is not an unsupported demotion. -/
theorem f65Withdraw_not_unsupportedDemotion :
    ¬ UnsupportedDemotion F65Applicable F65Handles f65Withdraw :=
  fun h => f65Withdraw_not_consumes h.2

/-! ## Residual implies a unique-normal-form instance -/

/-- On `f(x,x) -> a` beside `f(c,d) -> b`, the residual for any condition
oracle `E` forces `c` and `d` apart in `E`. -/
theorem f65_residual_forces_cd_separation
    (E : Term Nat Nat → Term Nat Nat → Prop)
    (h : NoFeasibleOverlap InfeasibleOverlap.lin E) :
    ¬ E (Term.app 2 []) (Term.app 3 []) := by
  intro hcd
  have hbad := h ⟨.app 1 [.var 0, .var 9], .app 4 [], [(.var 0, .var 9)], rfl⟩
    (List.Mem.head _)
    ⟨.app 1 [.app 2 [], .app 3 []], .app 5 [], [], rfl⟩
    (List.Mem.tail _ (List.Mem.head _))
    (.app 1 [.var 0, .var 9]) (Subterm.refl _) rfl
    (fun v => if v = 0 then .app 2 [] else .app 3 []) (fun _ => .var 0)
    (by simp)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      simpa [Subst.apply_var] using hcd)
    (by
      intro p hp
      simp at hp)
  simp at hbad

theorem infeasibleOverlap_c_normal :
    OperatorKO7.Meta.UniqueNormalization.NormalForm InfeasibleOverlap.trs
      (Term.app 2 []) := by
  intro u h
  rcases OperatorKO7.Meta.UniqueNormalization.Step.app_inv h with
    hr | ⟨pre, post, a, b, hargs, -, -⟩
  · obtain ⟨rule, hmem, σ, hs, -⟩ := hr
    simp only [InfeasibleOverlap.trs, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with rfl | rfl <;> simp [Subst.apply_app] at hs
  · simp at hargs

theorem infeasibleOverlap_d_normal :
    OperatorKO7.Meta.UniqueNormalization.NormalForm InfeasibleOverlap.trs
      (Term.app 3 []) := by
  intro u h
  rcases OperatorKO7.Meta.UniqueNormalization.Step.app_inv h with
    hr | ⟨pre, post, a, b, hargs, -, -⟩
  · obtain ⟨rule, hmem, σ, hs, -⟩ := hr
    simp only [InfeasibleOverlap.trs, List.mem_cons, List.not_mem_nil,
      or_false] at hmem
    rcases hmem with rfl | rfl <;> simp [Subst.apply_app] at hs
  · simp at hargs

/-- The terms `c` and `d` are distinct normal forms, and the residual condition implies that they are not convertible. -/
theorem f65_residual_contains_UN_instance :
    (Term.app 2 [] : Term Nat Nat) ≠ Term.app 3 [] ∧
      OperatorKO7.Meta.UniqueNormalization.NormalForm InfeasibleOverlap.trs
        (Term.app 2 []) ∧
      OperatorKO7.Meta.UniqueNormalization.NormalForm InfeasibleOverlap.trs
        (Term.app 3 []) ∧
      (NoFeasibleOverlap InfeasibleOverlap.lin (cconv InfeasibleOverlap.lin) →
        ¬ OperatorKO7.Meta.UniqueNormalization.conv InfeasibleOverlap.trs
          (Term.app 2 []) (Term.app 3 [])) :=
  ⟨by simp, infeasibleOverlap_c_normal, infeasibleOverlap_d_normal,
    fun h hconv => f65_residual_forces_cd_separation _ h
      ((cconv_iff_conv InfeasibleOverlap.isLin _ _).2 hconv)⟩

/-! ## Systems with feasible overlaps -/

theorem f65_hypothesis_fails_on_huet :
    ¬ NoFeasibleOverlap Controls.linHuet (cconv Controls.linHuet) :=
  Controls.linHuet_feasibleOverlap

theorem f65_hypothesis_fails_on_ko7 :
    ¬ NoFeasibleOverlap Controls.linKO7 (cconv Controls.linKO7) :=
  Controls.linKO7_feasibleOverlap

/-- Both systems admit feasible overlaps, so neither satisfies the residual hypothesis. -/
theorem f65_residual_fails_on_nonUN_controls :
    (¬ NoFeasibleOverlap Controls.linHuet (cconv Controls.linHuet)) ∧
      ¬ NoFeasibleOverlap Controls.linKO7 (cconv Controls.linKO7) :=
  ⟨f65_hypothesis_fails_on_huet, f65_hypothesis_fails_on_ko7⟩

/-! ## Support arithmetic -/

/-- A replacement whose support still contains the replaced assumption never
shrinks the support. -/
theorem selfcontained_replacement_no_drop {α : Type} [DecidableEq α]
    (S D : Finset α) (h : α) (hh : h ∈ S) (hhD : h ∈ D) :
    (S.card : ℤ) ≤ (((S.erase h) ∪ D).card : ℤ) := by
  have hdel := support_substitution_delta S D h hh
  rw [if_pos hhD] at hdel
  omega

/-! ## The grade -/

/-- The episode grade is `(1, 1, 0, 0, 1)`: recognition and construction apply to the claim, transport and progress are absent, and supervision records the withdrawal. -/
def f65Grade : GradeVector := ⟨1, 1, 0, 0, 1⟩

/-- The certified state is a self-application gap that does not consume, the withdrawn state is licensed, and the residual condition implies that `c` and `d` are not convertible. -/
theorem f65_grade_justified :
    SelfApplicationGap F65Applicable F65AuditRejects f65Propose ∧
      (¬ Consumes F65Applicable F65Handles f65Propose) ∧
      Licensed F65Applicable F65Handles f65Withdraw ∧
      (NoFeasibleOverlap InfeasibleOverlap.lin (cconv InfeasibleOverlap.lin) →
        ¬ OperatorKO7.Meta.UniqueNormalization.conv InfeasibleOverlap.trs
          (Term.app 2 []) (Term.app 3 [])) :=
  ⟨f65Propose_selfApplicationGap, f65Propose_not_consumes, f65Withdraw_licensed,
    f65_residual_contains_UN_instance.2.2.2⟩

end OperatorKO7.Meta.ProofSearchBoundary.F65Unfolding
