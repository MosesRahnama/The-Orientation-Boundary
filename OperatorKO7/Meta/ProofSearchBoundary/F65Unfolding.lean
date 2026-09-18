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
# The F65 episode, unfolded

Ledger row F65 (`klop-failed-attempts.md`) records an overclaim: "Problem 79
reduced to one statement", `NoFeasibleOverlap (linHub R) (cconv (linHub R))`.
The row says the theorems stand and only the wording was wrong: the hypothesis
contains UN= instances ("for `f(x,x) -> a` beside `f(c,d) -> b` it says `c` and
`d` are not convertible"), so it is not a smaller problem.  The route is not
circular: `UNconv_of_linHub_noFeasibleOverlap` derives UN= from the residual
without assuming UN=.

This module gives the episode first-class treatment:

* a `ProofSearchState` fixture (`f65Propose`, certified; `f65Withdraw`) whose
  blocker is the missing reason for "smaller";
* the audit of that answer key, `f65_residual_contains_UN_instance`: on the
  ledger's own system the residual implies the UN= instance at the distinct
  normal forms `c` and `d`;
* positive controls `f65_residual_fails_on_nonUN_controls`: the residual fails
  on Huet's system and the KO7 kernel, as the reduction theorem forces for
  systems without UN=; they show the residual is not vacuous and are not
  evidence against the reduction.

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

/-! ## The fixture -/

/-- The F65 target: Problem 79, unique normal forms. -/
inductive F65Target where
  | problem79UN
  deriving DecidableEq, Repr

/-- The F65 blocker: a certified claim that Problem 79 is reduced to a smaller
statement needs a reason the residual is smaller.  The residual implies UN=
instances (`f65_residual_contains_UN_instance`), so no such reason exists. -/
inductive F65Constraint where
  | kSelfContainment
  deriving DecidableEq, Repr

/-- The F65 obligation: discharge Problem 79. -/
inductive F65Obligation where
  | dischargeProblem79
  deriving DecidableEq, Repr

/-- The F65 proposals: the "reduced to one statement" claim, and its
withdrawal. -/
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

/-- The blocker on record. -/
def f65Blockers : List F65Constraint := [.kSelfContainment]

/-- The obligation on record. -/
def f65Obligations : List F65Obligation := [.dischargeProblem79]

/-- The claiming state: "Problem 79 reduced to one statement", certified. -/
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

/-! ## Audit of the answer key: the residual contains a UN= instance -/

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

/-- F65, formally: `c` and `d` are distinct normal forms, and the residual
implies that they are not convertible, which is the UN= instance at `c`
and `d`. -/
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

/-! ## Positive controls -/

theorem f65_hypothesis_fails_on_huet :
    ¬ NoFeasibleOverlap Controls.linHuet (cconv Controls.linHuet) :=
  Controls.linHuet_feasibleOverlap

theorem f65_hypothesis_fails_on_ko7 :
    ¬ NoFeasibleOverlap Controls.linKO7 (cconv Controls.linKO7) :=
  Controls.linKO7_feasibleOverlap

/-- The residual fails on both control systems, which lack UN=; the reduction
theorem forces this.  The controls show the residual is not vacuous. -/
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

/-- Episode grade `(1, 1, 0, 0, 1)`, an annotation of this module: the source
notes assign no F65 grade.  Recognition and construction for the claim, no
transport and no progress, supervision for the withdrawal. -/
def f65Grade : GradeVector := ⟨1, 1, 0, 0, 1⟩

/-- The coordinates with a formal counterpart. -/
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
