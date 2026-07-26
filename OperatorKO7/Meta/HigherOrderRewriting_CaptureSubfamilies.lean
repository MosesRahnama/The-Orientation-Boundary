import OperatorKO7.Meta.HigherOrderRewriting_BetaBinder

/-!
This module catalogs syntactic subfamilies and status markers. LinearHOTerm records binder-free
and sharing-free syntax, DAGSharedHOTerm aliases ClosedFragment, and FullCaptureSemanticsStatus
is a two-constructor tag. Theorems establish the displayed structural projections and finite
catalog facts.


-/

namespace OperatorKO7.HigherOrderRewritingCaptureSubfamilies

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBoundary
open OperatorKO7.HigherOrderRewritingBetaBinder

/-- Field requirements are given by the displayed type. -/
@[simp] def IsLam : HOTerm -> Prop
  | .lam _ _ => True
  | _ => False

/-- Field requirements are given by the displayed type. -/
@[simp] def BinderFreeHOTerm : HOTerm -> Prop
  | .var _ => True
  | .atom => True
  | .succ t => BinderFreeHOTerm t
  | .app f a => BinderFreeHOTerm f /\ BinderFreeHOTerm a
  | .lam _ _ => False
  | .recur b s n => BinderFreeHOTerm b /\ BinderFreeHOTerm s /\ BinderFreeHOTerm n
  | .share s r => BinderFreeHOTerm s /\ BinderFreeHOTerm r

/-- Field requirements are given by the displayed type. -/
@[simp] def ShareFreeHOTerm : HOTerm -> Prop
  | .var _ => True
  | .atom => True
  | .succ t => ShareFreeHOTerm t
  | .app f a => ShareFreeHOTerm f /\ ShareFreeHOTerm a
  | .lam _ body => ShareFreeHOTerm body
  | .recur b s n => ShareFreeHOTerm b /\ ShareFreeHOTerm s /\ ShareFreeHOTerm n
  | .share _ _ => False

/-- Field requirements are given by the displayed type.
-/
@[simp] def BetaFreeHOTerm : HOTerm -> Prop
  | .var _ => True
  | .atom => True
  | .succ t => BetaFreeHOTerm t
  | .app f a => ¬ IsLam f /\ BetaFreeHOTerm f /\ BetaFreeHOTerm a
  | .lam _ body => BetaFreeHOTerm body
  | .recur b s n => BetaFreeHOTerm b /\ BetaFreeHOTerm s /\ BetaFreeHOTerm n
  | .share s r => BetaFreeHOTerm s /\ BetaFreeHOTerm r

/-- Abbreviation for the displayed type.
-/
abbrev LinearHOTerm (t : HOTerm) : Prop :=
  BinderFreeHOTerm t /\ ShareFreeHOTerm t

/-- Abbreviation for the displayed type.

-/
abbrev DAGSharedHOTerm (t : HOTerm) : Prop :=
  ClosedFragment t

/-- Carrier with the constructors displayed below.
-/
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

/-- Data record whose requirements are the fields displayed below.
-/
structure CaptureSafeSubstitutionObligation
    (name binderName : Nat) (arg body : HOTerm) : Prop where
  binderAware : BinderAwareSubstitutionObligation name binderName arg body
  argumentBinderFree : BinderFreeHOTerm arg
  argumentShareFree : ShareFreeHOTerm arg
  bodyBinderFree : BinderFreeHOTerm body
  bodyShareFree : ShareFreeHOTerm body

/-- Data record whose requirements are the fields displayed below. -/
structure ContextSafeSubstitutionObligation
    (c : Context) (t : HOTerm) : Prop where
  binderFreeContext : BinderFreeContext c
  betaFreeContext : BetaFreeContext c
  termBinderFree : BinderFreeHOTerm t
  termBetaFree : BetaFreeHOTerm t

/-- Data record whose requirements are the fields displayed below. -/
structure BetaCounterexamplePackage : Prop where
  witness :
    ∃ redex contractum : HOTerm,
      BetaStep redex contractum ∧
        ¬ PolicyCounter betaCompatiblePolicy contractum <
            PolicyCounter betaCompatiblePolicy redex

/-- Data record whose requirements are the fields displayed below.
-/
structure ShareFreeBoundaryEmbedding (t : HOTerm) : Prop where
  witness :
    ∃ boundaryTerm : OperatorKO7.HigherOrderSharingBoundary.HOTerm,
      embedBoundaryHOTerm boundaryTerm = t

/-- A direct additive higher-order measure: the shape `PolicyCounter` carries in
tree mode. `eval` adds across application, passes transparently through binders,
and is blind to variable occurrences. This is the class of direct measures the
orientation-boundary program quantifies over: the universal statement below ranges
over every member, not one hand-picked counter. -/
structure DirectHOMeasure where
  eval : HOTerm → Nat
  eval_app : ∀ f a, eval (HOTerm.app f a) = eval f + eval a
  eval_lam : ∀ n b, eval (HOTerm.lam n b) = eval b
  eval_var : ∀ i, eval (HOTerm.var i) = 0

/-- The beta-compatible policy counter is a direct measure. This witnesses that
the class is inhabited by the program's own counter rather than an artificial
construction. -/
def policyDirectMeasure : DirectHOMeasure where
  eval := PolicyCounter betaCompatiblePolicy
  eval_app := by intro f a; rfl
  eval_lam := by intro n b; rfl
  eval_var := by intro i; rfl

/-- The canonical direct measure is nontrivial: `succ atom` has measure one. This
is the higher-order analogue of the affine positivity pump, and it excludes only
the degenerate zero measure. -/
theorem policyDirectMeasure_nontrivial :
    ∃ t : HOTerm, 0 < policyDirectMeasure.eval t :=
  ⟨HOTerm.succ HOTerm.atom, by decide⟩

/-- A direct measure orients the duplicating beta family when it strictly decreases
across every duplicating redex `(λ0. v0 v0) arg → arg arg`. -/
def OrientsDuplicatingBeta (M : DirectHOMeasure) : Prop :=
  ∀ arg : HOTerm,
    M.eval (HOTerm.app arg arg) <
      M.eval (HOTerm.app (HOTerm.lam 0 (HOTerm.app (HOTerm.var 0) (HOTerm.var 0))) arg)

/-- Universal full-capture no-go: no direct measure orients the duplicating beta
family, unconditionally.

The duplicating redex `(λ0. v0 v0) arg` reduces to `arg arg`. Additivity across
application sends the measure from `eval arg` (redex) to `eval arg + eval arg`
(contractum) with no offset, so a strict decrease would force `2 * eval arg <
eval arg`, impossible in the naturals for every argument, including `atom`. The
class is quantified in full and no positivity or pump hypothesis is required, so
this closes the boundary for every direct measure at once and supersedes the
single-counter witness. -/
theorem no_directHOMeasure_orients_duplicating_beta (M : DirectHOMeasure) :
    ¬ OrientsDuplicatingBeta M := by
  intro h
  have hstep := h HOTerm.atom
  simp only [M.eval_app, M.eval_lam, M.eval_var] at hstep
  omega

/-- Universal full-capture boundary certificate: the direct-measure class is
inhabited by the program counter, that counter is nontrivial (so the class is not
degenerate), and no direct measure whatsoever orients the duplicating beta
family. -/
structure FullCaptureUniversalBoundary : Prop where
  classInhabited : Nonempty DirectHOMeasure
  canonicalWitnessNontrivial : ∃ t : HOTerm, 0 < policyDirectMeasure.eval t
  universalNoGo :
    ∀ M : DirectHOMeasure, ¬ OrientsDuplicatingBeta M

/-- The universal full-capture boundary holds. -/
theorem full_capture_universal_boundary : FullCaptureUniversalBoundary where
  classInhabited := ⟨policyDirectMeasure⟩
  canonicalWitnessNontrivial := policyDirectMeasure_nontrivial
  universalNoGo := no_directHOMeasure_orients_duplicating_beta

/-- The universal no-go specializes to the program's policy counter: the
beta-compatible policy counter fails to orient the duplicating beta step. This
recovers the single-counter obstruction as a corollary of the class-wide theorem. -/
theorem betaCompatible_policyCounter_not_orients_duplicating :
    ¬ BetaStepOrientsPolicyCounter betaCompatiblePolicy := by
  intro hOrients
  refine no_directHOMeasure_orients_duplicating_beta policyDirectMeasure ?_
  intro arg
  have hbeta :
      BetaStep
        (HOTerm.app (HOTerm.lam 0 (HOTerm.app (HOTerm.var 0) (HOTerm.var 0))) arg)
        (HOTerm.app arg arg) := by
    simpa using BetaStep.mk 0 (HOTerm.app (HOTerm.var 0) (HOTerm.var 0)) arg
  exact hOrients hbeta

/-- The full-capture lane is closed at a counterexample boundary.

This unfolds to the unconditional refutation of
`BetaStepOrientsPolicyCounter betaCompatiblePolicy`: no policy-counter orientation
of beta steps exists for the beta-compatible policy. The statement carries the
mathematical content directly, so inhabiting it requires exhibiting the
obstruction rather than asserting a status tag.
-/
def FullCaptureSemanticsStatus : Prop :=
  ¬ BetaStepOrientsPolicyCounter betaCompatiblePolicy

/-- Data record whose requirements are the fields displayed below.
-/
structure HigherOrderCaptureSubfamilyCatalog : Prop where
  closedFragmentBetaFree :
    ∀ {t : HOTerm}, ClosedFragment t -> BetaFreeHOTerm t
  closedFragmentBinderFree :
    ∀ {t : HOTerm}, ClosedFragment t -> BinderFreeHOTerm t
  binderFreeContextClosure :
    ∀ {c : Context} {t : HOTerm},
      BinderFreeContext c -> BinderFreeHOTerm t -> BinderFreeHOTerm (Context.plug c t)
  betaFreeContextClosure :
    ∀ {c : Context} {t : HOTerm},
      BetaFreeContext c -> BetaFreeHOTerm t -> BetaFreeHOTerm (Context.plug c t)
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
        BinderFreeHOTerm (Context.plug c t)
  contextSafeBetaFreeClosure :
    ∀ {c : Context} {t : HOTerm},
      ContextSafeSubstitutionObligation c t ->
        BetaFreeHOTerm (Context.plug c t)
  fullCaptureSemanticsExactBoundary :
    FullCaptureSemanticsStatus

/-- The displayed proposition follows from the stated hypotheses. -/
theorem closedFragment_not_lam
    {t : HOTerm} (ht : ClosedFragment t) :
    ¬ IsLam t := by
  cases ht <;> simp [IsLam]

/-- The displayed proposition follows from the stated hypotheses. -/
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

/-- The displayed proposition follows from the stated hypotheses. -/
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

/-- The displayed proposition follows from the stated hypotheses. -/
theorem embedSharedTerm_dagShared
    (t : SharedTerm) :
    DAGSharedHOTerm (embedSharedTerm t) :=
  embedSharedTerm_closed t

/-- The displayed proposition follows from the stated hypotheses. -/
theorem shareFree_closedFragment_linear
    {t : HOTerm} (hClosed : ClosedFragment t) (hShareFree : ShareFreeHOTerm t) :
    LinearHOTerm t :=
  ⟨closedFragment_binderFree hClosed, hShareFree⟩

/-- The displayed proposition follows from the stated hypotheses. -/
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

/-- The displayed proposition follows from the stated hypotheses. -/
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

/-- The displayed proposition follows from the stated hypotheses. -/
theorem plug_binderFree {c : Context}
    (hc : BinderFreeContext c) {t : HOTerm} (ht : BinderFreeHOTerm t) :
    BinderFreeHOTerm (Context.plug c t) := by
  induction hc generalizing t with
  | hole =>
      simpa using ht
  | succ hc ih =>
      simpa [Context.plug, BinderFreeHOTerm] using ih ht
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

/-- The displayed proposition follows from the stated hypotheses. -/
theorem plug_betaFree {c : Context}
    (hc : BetaFreeContext c) {t : HOTerm} (ht : BetaFreeHOTerm t) :
    BetaFreeHOTerm (Context.plug c t) := by
  induction hc generalizing t with
  | hole =>
      simpa using ht
  | succ hc ih =>
      simpa [Context.plug, BetaFreeHOTerm] using ih ht
  | appRight hfnNotLam hfnBeta hc ih =>
      exact ⟨hfnNotLam, hfnBeta, ih ht⟩
  | lam hc ih =>
      simpa [Context.plug, BetaFreeHOTerm] using ih ht
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

/-- The displayed proposition follows from the stated hypotheses. -/
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

/-- The displayed proposition follows from the stated hypotheses. -/
theorem shareFree_fragment_embeds_old_no_sharing_boundary
    {t : HOTerm} (hClosed : ClosedFragment t) (hShare : ShareFreeHOTerm t) :
    ShareFreeBoundaryEmbedding t := by
  exact ⟨shareFree_closedFragment_has_boundary_term hClosed hShare⟩

/-- The displayed proposition follows from the stated hypotheses. -/
theorem beta_compatible_counterexample_package :
    BetaCounterexamplePackage := by
  refine ⟨?_⟩
  refine ⟨HOTerm.app (HOTerm.lam 0 (HOTerm.var 0)) HOTerm.atom, HOTerm.atom, ?_, ?_⟩
  · exact BetaStep.mk 0 (HOTerm.var 0) HOTerm.atom
  · simp [PolicyCounter, betaCompatiblePolicy]

/-- The displayed proposition follows from the stated hypotheses. -/
theorem captureSafeSubstitutionObligation_projects_binder_aware
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    BinderAwareSubstitutionObligation name binderName arg body :=
  h.binderAware

/-- The displayed proposition follows from the stated hypotheses. -/
theorem captureSafeSubstitutionObligation_requires_freshness
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    FreshFor binderName arg :=
  binderAwareSubstitutionObligation_requires_freshness h.binderAware

/-- The displayed proposition follows from the stated hypotheses. -/
theorem captureSafeSubstitutionObligation_projects_argument_binder_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    BinderFreeHOTerm arg :=
  h.argumentBinderFree

/-- The displayed proposition follows from the stated hypotheses. -/
theorem captureSafeSubstitutionObligation_projects_argument_share_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    ShareFreeHOTerm arg :=
  h.argumentShareFree

/-- The displayed proposition follows from the stated hypotheses. -/
theorem captureSafeSubstitutionObligation_projects_body_binder_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    BinderFreeHOTerm body :=
  h.bodyBinderFree

/-- The displayed proposition follows from the stated hypotheses. -/
theorem captureSafeSubstitutionObligation_projects_body_share_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    ShareFreeHOTerm body :=
  h.bodyShareFree

/-- The displayed proposition follows from the stated hypotheses. -/
theorem captureSafeSubstitutionObligation_under_binder
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    binderAwareSubstitute name arg (HOTerm.lam binderName body) =
      HOTerm.lam binderName (binderAwareSubstitute name arg body) :=
  binderAwareSubstitute_under_binder h.binderAware

/-- The displayed proposition follows from the stated hypotheses. -/
theorem captureSafeSubstitutionObligation_preserves_binder_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    BinderFreeHOTerm (binderAwareSubstitute name arg body) := by
  simpa [binderAwareSubstitute] using
    binderFree_substitute name h.argumentBinderFree h.bodyBinderFree

/-- The displayed proposition follows from the stated hypotheses. -/
theorem captureSafeSubstitutionObligation_preserves_share_free
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    ShareFreeHOTerm (binderAwareSubstitute name arg body) := by
  simpa [binderAwareSubstitute] using
    shareFree_substitute name h.argumentShareFree h.bodyShareFree

/-- The displayed proposition follows from the stated hypotheses. -/
theorem contextSafeSubstitutionObligation_projects_binder_free_context
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BinderFreeContext c :=
  h.binderFreeContext

/-- The displayed proposition follows from the stated hypotheses. -/
theorem contextSafeSubstitutionObligation_projects_beta_free_context
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BetaFreeContext c :=
  h.betaFreeContext

/-- The displayed proposition follows from the stated hypotheses. -/
theorem contextSafeSubstitutionObligation_projects_term_binder_free
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BinderFreeHOTerm t :=
  h.termBinderFree

/-- The displayed proposition follows from the stated hypotheses. -/
theorem contextSafeSubstitutionObligation_projects_term_beta_free
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BetaFreeHOTerm t :=
  h.termBetaFree

/-- The displayed proposition follows from the stated hypotheses. -/
theorem contextSafeSubstitutionObligation_plug_binder_free
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BinderFreeHOTerm (Context.plug c t) :=
  BinderFreeContext.plug_binderFree h.binderFreeContext h.termBinderFree

/-- The displayed proposition follows from the stated hypotheses. -/
theorem contextSafeSubstitutionObligation_plug_beta_free
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    BetaFreeHOTerm (Context.plug c t) :=
  BetaFreeContext.plug_betaFree h.betaFreeContext h.termBetaFree

/-- The full-capture lane is closed at an exact counterexample boundary:
the beta-compatible policy has a concrete step not oriented by the declared
counter, so an unqualified universal orientation interface is impossible. -/
theorem full_capture_semantics_exact_boundary :
    FullCaptureSemanticsStatus := by
  show ¬ BetaStepOrientsPolicyCounter betaCompatiblePolicy
  intro hOrients
  obtain ⟨redex, contractum, hStep, hNotLt⟩ :=
    beta_compatible_counterexample_package.witness
  exact hNotLt (hOrients hStep)

/-- The displayed proposition follows from the stated hypotheses. -/
theorem capture_subfamily_catalog :
    HigherOrderCaptureSubfamilyCatalog := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact closedFragment_betaFree ht
  · intro t ht
    exact closedFragment_binderFree ht
  · intro c t hc ht
    exact BinderFreeContext.plug_binderFree hc ht
  · intro c t hc ht
    exact BetaFreeContext.plug_betaFree hc ht
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
    exact contextSafeSubstitutionObligation_plug_binder_free h
  · intro c t h
    exact contextSafeSubstitutionObligation_plug_beta_free h
  · exact full_capture_semantics_exact_boundary

end OperatorKO7.HigherOrderRewritingCaptureSubfamilies
