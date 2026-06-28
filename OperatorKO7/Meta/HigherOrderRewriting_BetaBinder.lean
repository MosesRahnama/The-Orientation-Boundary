import OperatorKO7.Meta.HigherOrderRewriting_Boundary

/-!
# Higher-Order Rewriting Beta/Binder Layer

This module isolates the beta-compatible and binder-aware branch from the current
explicit higher-order rewriting syntax. The goal is not to overclaim a full
capture-avoiding semantics. Instead the file lands the strongest honest theorem
surface currently supported by the existing `HOTerm` and `substitute` layer:

- explicit beta-step transport into the existing rewrite relation,
- binder-free substitution and context closure over the old closed fragment,
- a concrete beta counterexample showing that the current policy counter does
  not orient every beta step,
- theorem-visible freshness obligations for binder-aware substitution.
-/

namespace OperatorKO7.HigherOrderRewritingBetaBinder

open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBoundary

/-- Binder-aware substitution reuses the existing theorem-visible syntactic substitution. -/
@[simp] def binderAwareSubstitute (name : Nat) (arg body : HOTerm) : HOTerm :=
  substitute name arg body

/-- Binder-free substitution is the same operation, restricted later by binder-free inputs. -/
@[simp] def binderFreeSubstitute (name : Nat) (arg body : HOTerm) : HOTerm :=
  substitute name arg body

/-- Direct beta step on the explicit higher-order rewriting carrier. -/
inductive BetaStep : HOTerm → HOTerm → Prop
  | mk (name : Nat) (body arg : HOTerm) :
      BetaStep (HOTerm.app (HOTerm.lam name body) arg) (binderAwareSubstitute name arg body)

/-- Policy-counter orientation restricted to beta steps only. -/
abbrev BetaStepOrientsPolicyCounter (policy : PolicyClass) : Prop :=
  ∀ {a b : HOTerm}, BetaStep a b → PolicyCounter policy b < PolicyCounter policy a

/-- Contextual closure interface for beta steps over the existing one-hole contexts. -/
inductive ContextualBetaStep : HOTerm → HOTerm → Prop
  | connector (context : Context) {a b : HOTerm} :
      BetaStep a b → ContextualBetaStep (Context.connector context a) (Context.connector context b)

/-- Free-variable occurrence predicate for the current binder-aware syntax. -/
@[simp] def FreeVarOccurs (name : Nat) : HOTerm → Prop
  | .var idx => idx = name
  | .atom => False
  | .succ t => FreeVarOccurs name t
  | .app f a => FreeVarOccurs name f ∨ FreeVarOccurs name a
  | .lam idx body => idx ≠ name ∧ FreeVarOccurs name body
  | .recur b s n => FreeVarOccurs name b ∨ FreeVarOccurs name s ∨ FreeVarOccurs name n
  | .share s r => FreeVarOccurs name s ∨ FreeVarOccurs name r

/-- Freshness predicate used to record the exact missing binder-aware semantics. -/
abbrev FreshFor (binderName : Nat) (t : HOTerm) : Prop :=
  ¬ FreeVarOccurs binderName t

/-- Named obligation for descending under a binder without a full capture-avoiding semantics. -/
structure BinderAwareSubstitutionObligation
    (name binderName : Nat) (arg body : HOTerm) : Prop where
  binderDistinct : binderName ≠ name
  freshArgument : FreshFor binderName arg

/-- Binder-free contexts preserve the existing closed fragment. -/
inductive BinderFreeContext : Context → Prop
  | hole : BinderFreeContext .hole
  | succ {c : Context} : BinderFreeContext c → BinderFreeContext (.succ c)
  | appLeft {c : Context} {arg : HOTerm} :
      BinderFreeContext c → ClosedFragment arg → BinderFreeContext (.appLeft c arg)
  | appRight {fn : HOTerm} {c : Context} :
      ClosedFragment fn → BinderFreeContext c → BinderFreeContext (.appRight fn c)
  | recurBase {c : Context} {s n : HOTerm} :
      BinderFreeContext c → ClosedFragment s → ClosedFragment n →
      BinderFreeContext (.recurBase c s n)
  | recurStep {b : HOTerm} {c : Context} {n : HOTerm} :
      ClosedFragment b → BinderFreeContext c → ClosedFragment n →
      BinderFreeContext (.recurStep b c n)
  | recurArg {b s : HOTerm} {c : Context} :
      ClosedFragment b → ClosedFragment s → BinderFreeContext c →
      BinderFreeContext (.recurArg b s c)
  | shareLeft {c : Context} {r : HOTerm} :
      BinderFreeContext c → ClosedFragment r → BinderFreeContext (.shareLeft c r)
  | shareRight {s : HOTerm} {c : Context} :
      ClosedFragment s → BinderFreeContext c → BinderFreeContext (.shareRight s c)

/-- Closed-fragment terms are binder-free enough that substitution leaves them unchanged. -/
theorem closedFragment_substitute_eq
    (name : Nat) (replacement : HOTerm) {t : HOTerm}
    (ht : ClosedFragment t) :
    substitute name replacement t = t := by
  induction ht with
  | atom => rfl
  | succ ht ih => simpa [substitute] using congrArg HOTerm.succ ih
  | app hf ha ihf iha => simp [substitute, ihf, iha]
  | recur hb hs hn ihb ihs ihn => simp [substitute, ihb, ihs, ihn]
  | share hs hr ihs ihr => simp [substitute, ihs, ihr]

/-- Binder-free substitution agrees with the identity on the old closed fragment. -/
theorem closedFragment_binderFreeSubstitute_eq
    (name : Nat) (replacement : HOTerm) {t : HOTerm}
    (ht : ClosedFragment t) :
    binderFreeSubstitute name replacement t = t :=
  closedFragment_substitute_eq name replacement ht

/-- Binder-free substitution preserves the old closed fragment. -/
theorem closedFragment_binderFreeSubstitute_closed
    (name : Nat) (replacement : HOTerm) {t : HOTerm}
    (ht : ClosedFragment t) :
    ClosedFragment (binderFreeSubstitute name replacement t) := by
  rw [closedFragment_binderFreeSubstitute_eq name replacement ht]
  exact ht

namespace BinderFreeContext

/-- Connectorging a closed-fragment term into a binder-free context stays in the old closed fragment. -/
theorem connector_closed {c : Context}
    (hc : BinderFreeContext c) {t : HOTerm} (ht : ClosedFragment t) :
    ClosedFragment (Context.connector c t) := by
  induction hc generalizing t with
  | hole => simpa using ht
  | succ hc ih => simpa [Context.connector] using ClosedFragment.succ (ih ht)
  | appLeft hc harg ih => simpa [Context.connector] using ClosedFragment.app (ih ht) harg
  | appRight hfn hc ih => simpa [Context.connector] using ClosedFragment.app hfn (ih ht)
  | recurBase hc hs hn ih =>
      simpa [Context.connector] using ClosedFragment.recur (ih ht) hs hn
  | recurStep hb hc hn ih =>
      simpa [Context.connector] using ClosedFragment.recur hb (ih ht) hn
  | recurArg hb hs hc ih =>
      simpa [Context.connector] using ClosedFragment.recur hb hs (ih ht)
  | shareLeft hc hr ih =>
      simpa [Context.connector] using ClosedFragment.share (ih ht) hr
  | shareRight hs hc ih =>
      simpa [Context.connector] using ClosedFragment.share hs (ih ht)

end BinderFreeContext

/-- Tree-policy binder-free substitution closure on the old closed fragment. -/
theorem tree_policy_binder_free_substitution_closed
    (name : Nat) (replacement : HOTerm) {t : HOTerm}
    (ht : ClosedFragment t) :
    ClosedFragment (binderFreeSubstitute name replacement t) :=
  closedFragment_binderFreeSubstitute_closed name replacement ht

/-- Shared-policy binder-free substitution closure on the old closed fragment. -/
theorem shared_policy_binder_free_substitution_closed
    (name : Nat) (replacement : HOTerm) {t : HOTerm}
    (ht : ClosedFragment t) :
    ClosedFragment (binderFreeSubstitute name replacement t) :=
  closedFragment_binderFreeSubstitute_closed name replacement ht

/-- Explicit-sharing binder-free substitution closure on the old closed fragment. -/
theorem explicit_sharing_policy_binder_free_substitution_closed
    (name : Nat) (replacement : HOTerm) {t : HOTerm}
    (ht : ClosedFragment t) :
    ClosedFragment (binderFreeSubstitute name replacement t) :=
  closedFragment_binderFreeSubstitute_closed name replacement ht

/-- Tree-policy binder-free context closure on the old closed fragment. -/
theorem tree_policy_binder_free_context_closed
    {c : Context} (hc : BinderFreeContext c) {t : HOTerm} (ht : ClosedFragment t) :
    ClosedFragment (Context.connector c t) :=
  BinderFreeContext.connector_closed hc ht

/-- Shared-policy binder-free context closure on the old closed fragment. -/
theorem shared_policy_binder_free_context_closed
    {c : Context} (hc : BinderFreeContext c) {t : HOTerm} (ht : ClosedFragment t) :
    ClosedFragment (Context.connector c t) :=
  BinderFreeContext.connector_closed hc ht

/-- Explicit-sharing binder-free context closure on the old closed fragment. -/
theorem explicit_sharing_policy_binder_free_context_closed
    {c : Context} (hc : BinderFreeContext c) {t : HOTerm} (ht : ClosedFragment t) :
    ClosedFragment (Context.connector c t) :=
  BinderFreeContext.connector_closed hc ht

/-- Beta steps land directly in the existing rewrite relation for the beta-compatible policy. -/
theorem beta_step_rewriteStep
    {a b : HOTerm} (h : BetaStep a b) :
    RewriteStep betaCompatiblePolicy a b := by
  cases h with
  | mk name body arg =>
      simpa [binderAwareSubstitute, betaCompatiblePolicy] using
        RewriteStep.beta betaCompatiblePolicy rfl name body arg

/-- Any beta step induces a contextual beta step under every one-hole context. -/
theorem beta_step_contextual_closure
    {a b : HOTerm} (h : BetaStep a b) (context : Context) :
    ContextualBetaStep (Context.connector context a) (Context.connector context b) :=
  ContextualBetaStep.connector context h

/-- The binder-aware obligation exposes the required argument freshness for descent under a binder. -/
theorem binderAwareSubstitutionObligation_requires_freshness
    {name binderName : Nat} {arg body : HOTerm}
    (h : BinderAwareSubstitutionObligation name binderName arg body) :
    FreshFor binderName arg :=
  h.freshArgument

/-- Under the named binder-aware obligation, substitution may descend under the binder. -/
theorem binderAwareSubstitute_under_binder
    {name binderName : Nat} {arg body : HOTerm}
    (h : BinderAwareSubstitutionObligation name binderName arg body) :
    binderAwareSubstitute name arg (HOTerm.lam binderName body) =
      HOTerm.lam binderName (binderAwareSubstitute name arg body) := by
  simp [binderAwareSubstitute, substitute, h.binderDistinct]

/-- Substitution preserves binder freshness when both the argument and the input term are
fresh for the tracked binder name. -/
theorem substitute_preserves_freshness
    {name binderName : Nat} {arg t : HOTerm}
    (hArgFresh : FreshFor binderName arg)
    (hFresh : FreshFor binderName t) :
    FreshFor binderName (substitute name arg t) := by
  induction t with
  | var idx =>
      by_cases hEq : idx = name
      · simpa [substitute, hEq] using hArgFresh
      · simpa [FreshFor, FreeVarOccurs, substitute, hEq] using hFresh
  | atom =>
      simpa [FreshFor, FreeVarOccurs, substitute]
  | succ t ih =>
      simpa [FreshFor, FreeVarOccurs, substitute] using ih hFresh
  | app f a ihf iha =>
      have hFreshF : FreshFor binderName f := by
        intro hOccurs
        exact hFresh (Or.inl hOccurs)
      have hFreshA : FreshFor binderName a := by
        intro hOccurs
        exact hFresh (Or.inr hOccurs)
      intro hOccurs
      rcases hOccurs with hOccurs | hOccurs
      · exact ihf hFreshF hOccurs
      · exact iha hFreshA hOccurs
  | lam idx body ih =>
      by_cases hEq : idx = name
      · simpa [FreshFor, FreeVarOccurs, substitute, hEq] using hFresh
      · by_cases hBinder : idx = binderName
        · have hDistinct : binderName ≠ name := by
            simpa [hBinder] using hEq
          simpa [FreshFor, FreeVarOccurs, substitute, hBinder, hDistinct]
        · have hFreshBody : FreshFor binderName body := by
            intro hOccurs
            exact hFresh ⟨hBinder, hOccurs⟩
          simpa [FreshFor, FreeVarOccurs, substitute, hEq, hBinder] using
            ih hFreshBody
  | recur b s n ihb ihs ihn =>
      have hFreshB : FreshFor binderName b := by
        intro hOccurs
        exact hFresh (Or.inl hOccurs)
      have hFreshS : FreshFor binderName s := by
        intro hOccurs
        exact hFresh (Or.inr (Or.inl hOccurs))
      have hFreshN : FreshFor binderName n := by
        intro hOccurs
        exact hFresh (Or.inr (Or.inr hOccurs))
      intro hOccurs
      rcases hOccurs with hOccurs | hRest
      · exact ihb hFreshB hOccurs
      · rcases hRest with hOccurs | hOccurs
        · exact ihs hFreshS hOccurs
        · exact ihn hFreshN hOccurs
  | share s r ihs ihr =>
      have hFreshS : FreshFor binderName s := by
        intro hOccurs
        exact hFresh (Or.inl hOccurs)
      have hFreshR : FreshFor binderName r := by
        intro hOccurs
        exact hFresh (Or.inr hOccurs)
      intro hOccurs
      rcases hOccurs with hOccurs | hOccurs
      · exact ihs hFreshS hOccurs
      · exact ihr hFreshR hOccurs

/-- Binder-aware substitution inherits the same freshness-preservation fact. -/
theorem binderAwareSubstitute_preserves_freshness
    {name binderName : Nat} {arg body : HOTerm}
    (hArgFresh : FreshFor binderName arg)
    (hBodyFresh : FreshFor binderName body) :
    FreshFor binderName (binderAwareSubstitute name arg body) := by
  simpa [binderAwareSubstitute] using
    substitute_preserves_freshness (name := name) (binderName := binderName)
      (arg := arg) (t := body) hArgFresh hBodyFresh

/-- Concrete beta counterexample: the current policy counter does not strictly decrease on the
identity redex. -/
theorem beta_compatible_policy_counterexample :
    ∃ a b : HOTerm,
      BetaStep a b ∧
        ¬ PolicyCounter betaCompatiblePolicy b < PolicyCounter betaCompatiblePolicy a := by
  refine ⟨HOTerm.app (HOTerm.lam 0 (HOTerm.var 0)) HOTerm.atom, HOTerm.atom, ?_, ?_⟩
  · exact BetaStep.mk 0 (HOTerm.var 0) HOTerm.atom
  · simp [PolicyCounter, betaCompatiblePolicy]

/-- The beta-compatible policy does not orient every beta step under the current policy counter. -/
theorem beta_compatible_policy_does_not_orient_beta_steps :
    ¬ BetaStepOrientsPolicyCounter betaCompatiblePolicy := by
  intro h
  rcases beta_compatible_policy_counterexample with ⟨a, b, hbeta, hnotlt⟩
  exact hnotlt (h hbeta)

/-- Exact split of the current policy branches after landing the beta/binder layer. -/
structure PolicyBranchSplitStatus : Prop where
  treeBranchCoveredByBinderFreeClosure :
    ∀ {name : Nat} {replacement t : HOTerm},
      ClosedFragment t → ClosedFragment (binderFreeSubstitute name replacement t)
  sharedBranchCoveredByExistingBoundary : PolicyOrientsStep sharedPolicy
  explicitSharingBranchCoveredByExistingBoundary :
    PolicyOrientsStep explicitSharingPolicy
  betaCompatibleBranchTransport :
    ∀ {a b : HOTerm}, BetaStep a b → RewriteStep betaCompatiblePolicy a b
  betaCompatibleBranchBlocked :
    ¬ BetaStepOrientsPolicyCounter betaCompatiblePolicy
  binderAwareBranchObligation :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      BinderAwareSubstitutionObligation name binderName arg body →
        FreshFor binderName arg

/-- The current policy branches split cleanly between the old blocker surface, the new
beta/binder theorem layer, and the named binder-aware obligation. -/
theorem policy_branch_split_status : PolicyBranchSplitStatus where
  treeBranchCoveredByBinderFreeClosure := by
    intro name replacement t ht
    exact tree_policy_binder_free_substitution_closed name replacement ht
  sharedBranchCoveredByExistingBoundary := shared_policy_counter_orients_step
  explicitSharingBranchCoveredByExistingBoundary := explicit_sharing_counter_orients_step
  betaCompatibleBranchTransport := by
    intro a b h
    exact beta_step_rewriteStep h
  betaCompatibleBranchBlocked := beta_compatible_policy_does_not_orient_beta_steps
  binderAwareBranchObligation := by
    intro name binderName arg body h
    exact binderAwareSubstitutionObligation_requires_freshness h

end OperatorKO7.HigherOrderRewritingBetaBinder
