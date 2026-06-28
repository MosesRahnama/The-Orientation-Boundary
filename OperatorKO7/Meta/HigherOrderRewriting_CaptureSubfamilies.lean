import OperatorKO7.Meta.HigherOrderRewriting_BetaBinder

/-!
# Higher-Order Rewriting Capture and Subfamilies

This module adds the next honest theorem layer above the beta/binder sprint.
It does not claim a full capture-avoiding higher-order rewriting semantics.
Instead it records the exact term fragments, context fragments, and named
obligations that are mechanically supported by the current syntax.
-/

namespace OperatorKO7.HigherOrderRewritingCaptureSubfamilies

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBoundary
open OperatorKO7.HigherOrderRewritingBetaBinder

/-- Predicate detecting lambda terms at the top level. -/
@[simp] def IsLam : HOTerm -> Prop
  | .lam _ _ => True
  | _ => False

/-- Terms with no lambda constructor anywhere. -/
@[simp] def BinderFreeHOTerm : HOTerm -> Prop
  | .var _ => True
  | .atom => True
  | .succ t => BinderFreeHOTerm t
  | .app f a => BinderFreeHOTerm f /\ BinderFreeHOTerm a
  | .lam _ _ => False
  | .recur b s n => BinderFreeHOTerm b /\ BinderFreeHOTerm s /\ BinderFreeHOTerm n
  | .share s r => BinderFreeHOTerm s /\ BinderFreeHOTerm r

/-- Terms with no explicit sharing node anywhere. -/
@[simp] def ShareFreeHOTerm : HOTerm -> Prop
  | .var _ => True
  | .atom => True
  | .succ t => ShareFreeHOTerm t
  | .app f a => ShareFreeHOTerm f /\ ShareFreeHOTerm a
  | .lam _ body => ShareFreeHOTerm body
  | .recur b s n => ShareFreeHOTerm b /\ ShareFreeHOTerm s /\ ShareFreeHOTerm n
  | .share _ _ => False

/-- Terms with no beta redex anywhere. Lambda nodes themselves are allowed; only
applications with a lambda in function position are excluded. -/
@[simp] def BetaFreeHOTerm : HOTerm -> Prop
  | .var _ => True
  | .atom => True
  | .succ t => BetaFreeHOTerm t
  | .app f a => ¬ IsLam f /\ BetaFreeHOTerm f /\ BetaFreeHOTerm a
  | .lam _ body => BetaFreeHOTerm body
  | .recur b s n => BetaFreeHOTerm b /\ BetaFreeHOTerm s /\ BetaFreeHOTerm n
  | .share s r => BetaFreeHOTerm s /\ BetaFreeHOTerm r

/-- Conservative linear fragment supported by the current syntax: binder-free and
share-free. No variable-multiplicity theorem is claimed here. -/
abbrev LinearHOTerm (t : HOTerm) : Prop :=
  BinderFreeHOTerm t /\ ShareFreeHOTerm t

/-- Conservative DAG/shared fragment supported by the current syntax: the existing
closed fragment with explicit sharing nodes allowed. No graph-uniqueness theorem
is claimed here. -/
abbrev DAGSharedHOTerm (t : HOTerm) : Prop :=
  ClosedFragment t

/-- Beta-free contexts that never place the hole in function position. This is the
exact context fragment for which beta-freeness is mechanically preserved by connectorging. -/
inductive BetaFreeContext : Context -> Prop
  | hole : BetaFreeContext .hole
  | succ {c : Context} : BetaFreeContext c -> BetaFreeContext (.succ c)
  | appRight {fn : HOTerm} {c : Context} :
      (¬ IsLam fn) -> BetaFreeHOTerm fn -> BetaFreeContext c ->
      BetaFreeContext (.appRight fn c)
  | lam {name : Nat} {c : Context} :
      BetaFreeContext c -> BetaFreeContext (.lam name c)
  | recurBase {c : Context} {s n : HOTerm} :
      BetaFreeContext c -> BetaFreeHOTerm s -> BetaFreeHOTerm n ->
      BetaFreeContext (.recurBase c s n)
  | recurStep {b : HOTerm} {c : Context} {n : HOTerm} :
      BetaFreeHOTerm b -> BetaFreeContext c -> BetaFreeHOTerm n ->
      BetaFreeContext (.recurStep b c n)
  | recurArg {b s : HOTerm} {c : Context} :
      BetaFreeHOTerm b -> BetaFreeHOTerm s -> BetaFreeContext c ->
      BetaFreeContext (.recurArg b s c)
  | shareLeft {c : Context} {r : HOTerm} :
      BetaFreeContext c -> BetaFreeHOTerm r -> BetaFreeContext (.shareLeft c r)
  | shareRight {s : HOTerm} {c : Context} :
      BetaFreeHOTerm s -> BetaFreeContext c -> BetaFreeContext (.shareRight s c)

/-- Exact capture-side obligation supported by the current syntax. This records only
the projections and substitution-closure facts that Lean can prove today. -/
structure CaptureSafeSubstitutionObligation
    (name binderName : Nat) (arg body : HOTerm) : Prop where
  binderAware : BinderAwareSubstitutionObligation name binderName arg body
  argumentBinderFree : BinderFreeHOTerm arg
  argumentShareFree : ShareFreeHOTerm arg
  bodyBinderFree : BinderFreeHOTerm body
  bodyShareFree : ShareFreeHOTerm body

/-- Exact context-side obligation supported by the current syntax. -/
structure ContextSafeSubstitutionObligation
    (c : Context) (t : HOTerm) : Prop where
  binderFreeContext : BinderFreeContext c
  betaFreeContext : BetaFreeContext c
  termBinderFree : BinderFreeHOTerm t
  termBetaFree : BetaFreeHOTerm t

/-- Exact package for the current beta-compatible counterexample. -/
structure BetaCounterexamplePackage : Prop where
  witness :
    ∃ redex contractum : HOTerm,
      BetaStep redex contractum ∧
        ¬ PolicyCounter betaCompatiblePolicy contractum <
            PolicyCounter betaCompatiblePolicy redex

/-- Witness that a share-free closed fragment re-embeds into the old no-sharing
boundary carrier. -/
structure ShareFreeBoundaryEmbedding (t : HOTerm) : Prop where
  witness :
    ∃ boundaryTerm : OperatorKO7.HigherOrderSharingBoundary.HOTerm,
      embedBoundaryHOTerm boundaryTerm = t

/-- Marker for the current manuscript boundary: full capture-avoiding semantics is
still open on the present theorem surface. -/
inductive FullCaptureSemanticsStatus : Prop
  | open

/-- Catalog splitting the current explicit higher-order rewriting layer into the exact
subfamilies and obligation surfaces presently justified by Lean. -/
structure HigherOrderCaptureSubfamilyCatalog : Prop where
  closedFragmentBetaFree :
    ∀ {t : HOTerm}, ClosedFragment t -> BetaFreeHOTerm t
  closedFragmentBinderFree :
    ∀ {t : HOTerm}, ClosedFragment t -> BinderFreeHOTerm t
  binderFreeContextClosure :
    ∀ {c : Context} {t : HOTerm},
      BinderFreeContext c -> BinderFreeHOTerm t -> BinderFreeHOTerm (Context.connector c t)
  betaFreeContextClosure :
    ∀ {c : Context} {t : HOTerm},
      BetaFreeContext c -> BetaFreeHOTerm t -> BetaFreeHOTerm (Context.connector c t)
  shareFreeBoundaryEmbedding :
    ∀ {t : HOTerm},
      ClosedFragment t -> ShareFreeHOTerm t -> ShareFreeBoundaryEmbedding t
  betaCounterexamplePackage :
    BetaCounterexamplePackage
  betaStepTransport :
    ∀ {a b : HOTerm}, BetaStep a b -> RewriteStep betaCompatiblePolicy a b
  betaCompatibleBlocked :
    ¬ BetaStepOrientsPolicyCounter betaCompatiblePolicy
  captureSafeFreshness :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      CaptureSafeSubstitutionObligation name binderName arg body ->
        FreshFor binderName arg
  captureSafeBinderFreeClosure :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      CaptureSafeSubstitutionObligation name binderName arg body ->
        BinderFreeHOTerm (binderAwareSubstitute name arg body)
  captureSafeShareFreeClosure :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      CaptureSafeSubstitutionObligation name binderName arg body ->
        ShareFreeHOTerm (binderAwareSubstitute name arg body)
  treeBinderFreeBranch :
    ∀ {t : HOTerm},
      ClosedFragment t -> ShareFreeHOTerm t ->
        LinearHOTerm t /\ ShareFreeBoundaryEmbedding t
  sharedDAGBranch :
    ∀ t : SharedTerm, DAGSharedHOTerm (embedSharedTerm t)
  explicitSharingBranch :
    ExplicitSharingHO explicitSharingPolicy
  betaCompatibleBranch :
    BetaCompatibleStatus betaCompatiblePolicy
  contextSafeBinderFreeClosure :
    ∀ {c : Context} {t : HOTerm},
      ContextSafeSubstitutionObligation c t ->
        BinderFreeHOTerm (Context.connector c t)
  contextSafeBetaFreeClosure :
    ∀ {c : Context} {t : HOTerm},
      ContextSafeSubstitutionObligation c t ->
        BetaFreeHOTerm (Context.connector c t)
  fullCaptureSemanticsOpen :
    FullCaptureSemanticsStatus

/-- Closed fragments never have a lambda at the top. -/
theorem closedFragment_not_lam
    {t : HOTerm} (ht : ClosedFragment t) :
    ¬ IsLam t := by
  cases ht <;> simp [IsLam]

/-- Closed fragments lie in the conservative beta-free fragment. -/
theorem closedFragment_betaFree
    {t : HOTerm} (ht : ClosedFragment t) :
    BetaFreeHOTerm t := by
  induction ht with
  | atom => simp [BetaFreeHOTerm]
  | succ ht ih => simpa [BetaFreeHOTerm] using ih
  | app hf ha ihf iha =>
      exact ⟨closedFragment_not_lam hf, ihf, iha⟩
  | recur hb hs hn ihb ihs ihn =>
      exact ⟨ihb, ihs, ihn⟩
  | share hs hr ihs ihr =>
      exact ⟨ihs, ihr⟩

/-- Closed fragments lie in the conservative binder-free fragment. -/
theorem closedFragment_binderFree
    {t : HOTerm} (ht : ClosedFragment t) :
    BinderFreeHOTerm t := by
  induction ht with
  | atom => simp [BinderFreeHOTerm]
  | succ ht ih => simpa [BinderFreeHOTerm] using ih
  | app hf ha ihf iha =>
      exact ⟨ihf, iha⟩
  | recur hb hs hn ihb ihs ihn =>
      exact ⟨ihb, ihs, ihn⟩
  | share hs hr ihs ihr =>
      exact ⟨ihs, ihr⟩

/-- Embedded shared terms lie in the conservative DAG/shared fragment. -/
theorem embedSharedTerm_dagShared
    (t : SharedTerm) :
    DAGSharedHOTerm (embedSharedTerm t) :=
  embedSharedTerm_closed t

/-- A share-free closed fragment lies in the conservative linear fragment. -/
theorem shareFree_closedFragment_linear
    {t : HOTerm} (hClosed : ClosedFragment t) (hShareFree : ShareFreeHOTerm t) :
    LinearHOTerm t :=
  ⟨closedFragment_binderFree hClosed, hShareFree⟩

/-- Binder-free substitution preserves the conservative binder-free fragment. -/
theorem binderFree_substitute
    (name : Nat) {replacement t : HOTerm}
    (hReplacement : BinderFreeHOTerm replacement)
    (ht : BinderFreeHOTerm t) :
    BinderFreeHOTerm (substitute name replacement t) := by
  induction t generalizing replacement with
  | var idx =>
      by_cases hEq : idx = name
      · simp [substitute, hEq, hReplacement]
      · simp [substitute, hEq]
  | atom =>
      simp [substitute, BinderFreeHOTerm]
  | succ t ih =>
      simpa [substitute, BinderFreeHOTerm] using ih hReplacement ht
  | app f a ihf iha =>
      rcases ht with ⟨hf, ha⟩
      exact ⟨ihf hReplacement hf, iha hReplacement ha⟩
  | lam idx body ih =>
      cases ht
  | recur b s n ihb ihs ihn =>
      rcases ht with ⟨hb, hs, hn⟩
      exact ⟨ihb hReplacement hb, ihs hReplacement hs, ihn hReplacement hn⟩
  | share s r ihs ihr =>
      rcases ht with ⟨hs, hr⟩
      exact ⟨ihs hReplacement hs, ihr hReplacement hr⟩

/-- Share-free substitution preserves the conservative share-free fragment. -/
theorem shareFree_substitute
    (name : Nat) {replacement t : HOTerm}
    (hReplacement : ShareFreeHOTerm replacement)
    (ht : ShareFreeHOTerm t) :
    ShareFreeHOTerm (substitute name replacement t) := by
  induction t generalizing replacement with
  | var idx =>
      by_cases hEq : idx = name
      · simp [substitute, hEq, hReplacement]
      · simp [substitute, hEq]
  | atom =>
      simp [substitute, ShareFreeHOTerm]
  | succ t ih =>
      simpa [substitute, ShareFreeHOTerm] using ih hReplacement ht
  | app f a ihf iha =>
      rcases ht with ⟨hf, ha⟩
      exact ⟨ihf hReplacement hf, iha hReplacement ha⟩
  | lam idx body ih =>
      by_cases hEq : idx = name
      · simpa [substitute, ShareFreeHOTerm, hEq] using ht
      · simpa [substitute, ShareFreeHOTerm, hEq] using ih hReplacement ht
  | recur b s n ihb ihs ihn =>
      rcases ht with ⟨hb, hs, hn⟩
      exact ⟨ihb hReplacement hb, ihs hReplacement hs, ihn hReplacement hn⟩
  | share s r ihs ihr =>
      cases ht

namespace BinderFreeContext

/-- Connectorging a binder-free term into a binder-free context preserves binder-freeness. -/
theorem connector_binderFree {c : Context}
    (hc : BinderFreeContext c) {t : HOTerm} (ht : BinderFreeHOTerm t) :
    BinderFreeHOTerm (Context.connector c t) := by
  induction hc generalizing t with
  | hole =>
      simpa using ht
  | succ hc ih =>
      simpa [Context.connector, BinderFreeHOTerm] using ih ht
  | appLeft hc harg ih =>
      exact ⟨ih ht, closedFragment_binderFree harg⟩
  | appRight hfn hc ih =>
      exact ⟨closedFragment_binderFree hfn, ih ht⟩
  | recurBase hc hs hn ih =>
      exact ⟨ih ht, closedFragment_binderFree hs, closedFragment_binderFree hn⟩
  | recurStep hb hc hn ih =>
      exact ⟨closedFragment_binderFree hb, ih ht, closedFragment_binderFree hn⟩
  | recurArg hb hs hc ih =>
      exact ⟨closedFragment_binderFree hb, closedFragment_binderFree hs, ih ht⟩
  | shareLeft hc hr ih =>
      exact ⟨ih ht, closedFragment_binderFree hr⟩
  | shareRight hs hc ih =>
      exact ⟨closedFragment_binderFree hs, ih ht⟩

end BinderFreeContext

namespace BetaFreeContext

/-- Connectorging a beta-free term into a beta-free context preserves beta-freeness. -/
theorem connector_betaFree {c : Context}
    (hc : BetaFreeContext c) {t : HOTerm} (ht : BetaFreeHOTerm t) :
    BetaFreeHOTerm (Context.connector c t) := by
  induction hc generalizing t with
  | hole =>
      simpa using ht
  | succ hc ih =>
      simpa [Context.connector, BetaFreeHOTerm] using ih ht
  | appRight hfnNotLam hfnBeta hc ih =>
      exact ⟨hfnNotLam, hfnBeta, ih ht⟩
  | lam hc ih =>
      simpa [Context.connector, BetaFreeHOTerm] using ih ht
  | recurBase hc hs hn ih =>
      exact ⟨ih ht, hs, hn⟩
  | recurStep hb hc hn ih =>
      exact ⟨hb, ih ht, hn⟩
  | recurArg hb hs hc ih =>
      exact ⟨hb, hs, ih ht⟩
  | shareLeft hc hr ih =>
      exact ⟨ih ht, hr⟩
  | shareRight hs hc ih =>
      exact ⟨hs, ih ht⟩

end BetaFreeContext

/-- Share-free closed fragments have an exact witness in the old no-sharing boundary. -/
theorem shareFree_closedFragment_has_boundary_term
    {t : HOTerm} (hClosed : ClosedFragment t) (hShare : ShareFreeHOTerm t) :
    ∃ boundaryTerm : OperatorKO7.HigherOrderSharingBoundary.HOTerm,
      embedBoundaryHOTerm boundaryTerm = t := by
  induction hClosed with
  | atom =>
      exact ⟨.base, rfl⟩
  | succ ht ih =>
      rcases ih hShare with ⟨boundaryTerm, hBoundary⟩
      exact ⟨.succ boundaryTerm, by simp [hBoundary]⟩
  | app hf ha ihf iha =>
      rcases hShare with ⟨hShareF, hShareA⟩
      rcases ihf hShareF with ⟨boundaryF, hBoundaryF⟩
      rcases iha hShareA with ⟨boundaryA, hBoundaryA⟩
      exact ⟨.app boundaryF boundaryA, by simp [hBoundaryF, hBoundaryA]⟩
  | recur hb hs hn ihb ihs ihn =>
      rcases hShare with ⟨hShareB, hShareS, hShareN⟩
      rcases ihb hShareB with ⟨boundaryB, hBoundaryB⟩
      rcases ihs hShareS with ⟨boundaryS, hBoundaryS⟩
      rcases ihn hShareN with ⟨boundaryN, hBoundaryN⟩
      exact ⟨.recur boundaryB boundaryS boundaryN, by simp [hBoundaryB, hBoundaryS, hBoundaryN]⟩
  | share hs hr ihs ihr =>
      cases hShare

/-- Exact embedding theorem for share-free fragments into the old no-sharing boundary. -/
theorem shareFree_fragment_embeds_old_no_sharing_boundary
    {t : HOTerm} (hClosed : ClosedFragment t) (hShare : ShareFreeHOTerm t) :
    ShareFreeBoundaryEmbedding t := by
  exact ⟨shareFree_closedFragment_has_boundary_term hClosed hShare⟩

/-- The exact beta-compatible counterexample packaged as named data. -/
theorem beta_compatible_counterexample_package :
    BetaCounterexamplePackage := by
  refine ⟨?_⟩
  refine ⟨HOTerm.app (HOTerm.lam 0 (HOTerm.var 0)) HOTerm.atom, HOTerm.atom, ?_, ?_⟩
  · exact BetaStep.mk 0 (HOTerm.var 0) HOTerm.atom
  · simp [PolicyCounter, betaCompatiblePolicy]

/-- Projection from the capture-safe obligation to the underlying binder-aware obligation. -/
theorem captureSafeSubstitutionObligation_projects_binder_aware
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    BinderAwareSubstitutionObligation name binderName arg body :=
  h.binderAware

/-- Projection from the capture-safe obligation to freshness. -/
theorem captureSafeSubstitutionObligation_requires_freshness
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    FreshFor binderName arg :=
  binderAwareSubstitutionObligation_requires_freshness h.binderAware

/-- Projection from the capture-safe obligation to binder-free arguments. -/
theorem captureSafeSubstitutionObligation_projects_argument_binder_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    BinderFreeHOTerm arg :=
  h.argumentBinderFree

/-- Projection from the capture-safe obligation to share-free arguments. -/
theorem captureSafeSubstitutionObligation_projects_argument_share_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    ShareFreeHOTerm arg :=
  h.argumentShareFree

/-- Projection from the capture-safe obligation to binder-free bodies. -/
theorem captureSafeSubstitutionObligation_projects_body_binder_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    BinderFreeHOTerm body :=
  h.bodyBinderFree

/-- Projection from the capture-safe obligation to share-free bodies. -/
theorem captureSafeSubstitutionObligation_projects_body_share_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    ShareFreeHOTerm body :=
  h.bodyShareFree

/-- Under the exact capture-safe obligation, substitution may descend under the binder. -/
theorem captureSafeSubstitutionObligation_under_binder
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    binderAwareSubstitute name arg (HOTerm.lam binderName body) =
      HOTerm.lam binderName (binderAwareSubstitute name arg body) :=
  binderAwareSubstitute_under_binder h.binderAware

/-- The exact capture-safe obligation preserves binder-freeness of the substituted body. -/
theorem captureSafeSubstitutionObligation_preserves_binder_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    BinderFreeHOTerm (binderAwareSubstitute name arg body) := by
  simpa [binderAwareSubstitute] using
    binderFree_substitute name h.argumentBinderFree h.bodyBinderFree

/-- The exact capture-safe obligation preserves share-freeness of the substituted body. -/
theorem captureSafeSubstitutionObligation_preserves_share_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    ShareFreeHOTerm (binderAwareSubstitute name arg body) := by
  simpa [binderAwareSubstitute] using
    shareFree_substitute name h.argumentShareFree h.bodyShareFree

/-- Projection from the context-safe obligation to binder-free contexts. -/
theorem contextSafeSubstitutionObligation_projects_binder_free_context
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BinderFreeContext c :=
  h.binderFreeContext

/-- Projection from the context-safe obligation to beta-free contexts. -/
theorem contextSafeSubstitutionObligation_projects_beta_free_context
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BetaFreeContext c :=
  h.betaFreeContext

/-- Projection from the context-safe obligation to binder-free connectorged terms. -/
theorem contextSafeSubstitutionObligation_projects_term_binder_free
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BinderFreeHOTerm t :=
  h.termBinderFree

/-- Projection from the context-safe obligation to beta-free connectorged terms. -/
theorem contextSafeSubstitutionObligation_projects_term_beta_free
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BetaFreeHOTerm t :=
  h.termBetaFree

/-- The exact context-safe obligation preserves binder-freeness under connectorging. -/
theorem contextSafeSubstitutionObligation_connector_binder_free
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BinderFreeHOTerm (Context.connector c t) :=
  BinderFreeContext.connector_binderFree h.binderFreeContext h.termBinderFree

/-- The exact context-safe obligation preserves beta-freeness under connectorging. -/
theorem contextSafeSubstitutionObligation_connector_beta_free
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BetaFreeHOTerm (Context.connector c t) :=
  BetaFreeContext.connector_betaFree h.betaFreeContext h.termBetaFree

/-- The current theorem-visible full-capture status remains explicitly open. -/
theorem full_capture_semantics_open :
    FullCaptureSemanticsStatus :=
  .open

/-- Canonical catalog of the current capture/freshness and subfamily layer. -/
theorem capture_subfamily_catalog :
    HigherOrderCaptureSubfamilyCatalog := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact closedFragment_betaFree ht
  · intro t ht
    exact closedFragment_binderFree ht
  · intro c t hc ht
    exact BinderFreeContext.connector_binderFree hc ht
  · intro c t hc ht
    exact BetaFreeContext.connector_betaFree hc ht
  · intro t hClosed hShare
    exact shareFree_fragment_embeds_old_no_sharing_boundary hClosed hShare
  · exact beta_compatible_counterexample_package
  · intro a b h
    exact beta_step_rewriteStep h
  · exact beta_compatible_policy_does_not_orient_beta_steps
  · intro name binderName arg body h
    exact captureSafeSubstitutionObligation_requires_freshness h
  · intro name binderName arg body h
    exact captureSafeSubstitutionObligation_preserves_binder_free h
  · intro name binderName arg body h
    exact captureSafeSubstitutionObligation_preserves_share_free h
  · intro t hClosed hShare
    exact ⟨shareFree_closedFragment_linear hClosed hShare,
      shareFree_fragment_embeds_old_no_sharing_boundary hClosed hShare⟩
  · intro t
    exact embedSharedTerm_dagShared t
  · exact explicitSharingPolicy_is_explicitSharingHO
  · exact betaCompatiblePolicy_is_betaCompatible
  · intro c t h
    exact contextSafeSubstitutionObligation_connector_binder_free h
  · intro c t h
    exact contextSafeSubstitutionObligation_connector_beta_free h
  · exact full_capture_semantics_open

end OperatorKO7.HigherOrderRewritingCaptureSubfamilies
