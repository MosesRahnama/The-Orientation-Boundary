import OperatorKO7.Meta.HigherOrderRewriting_DecidableClassifications

/-!
# Higher-Order Rewriting Capture Decision Layer

This module adds an executable decision layer above the existing higher-order
classification surface. It remains obligation-scoped: successful checks recover the
current exact obligation structures, and the full capture-avoiding semantics
surface remains explicitly open.
-/

namespace OperatorKO7.HigherOrderRewritingCaptureDecidable

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBetaBinder
open OperatorKO7.HigherOrderRewritingCaptureSubfamilies
open OperatorKO7.HigherOrderRewritingDecidableClassifications

/-- Executable free-variable occurrence classification for the current higher-order syntax. -/
@[simp] def freeVarOccurs? (name : Nat) : HOTerm → Bool
  | .var idx => decide (idx = name)
  | .atom => false
  | .succ t => freeVarOccurs? name t
  | .app f a => freeVarOccurs? name f || freeVarOccurs? name a
  | .lam idx body => decide (idx ≠ name) && freeVarOccurs? name body
  | .recur b s n => freeVarOccurs? name b || freeVarOccurs? name s || freeVarOccurs? name n
  | .share s r => freeVarOccurs? name s || freeVarOccurs? name r

/-- Executable freshness classification for binder descent. -/
@[simp] def freshFor? (binderName : Nat) (t : HOTerm) : Bool :=
  ! freeVarOccurs? binderName t

/-- Executable summary of currently free variable names, with multiplicity retained. -/
@[simp] def freeVariableSummary : HOTerm → List Nat
  | .var idx => [idx]
  | .atom => []
  | .succ t => freeVariableSummary t
  | .app f a => freeVariableSummary f ++ freeVariableSummary a
  | .lam idx body => (freeVariableSummary body).erase idx
  | .recur b s n => freeVariableSummary b ++ freeVariableSummary s ++ freeVariableSummary n
  | .share s r => freeVariableSummary s ++ freeVariableSummary r

/-- Executable binder-occurrence summary, with multiplicity retained. -/
@[simp] def binderOccurrenceSummary : HOTerm → List Nat
  | .var _ => []
  | .atom => []
  | .succ t => binderOccurrenceSummary t
  | .app f a => binderOccurrenceSummary f ++ binderOccurrenceSummary a
  | .lam idx body => idx :: binderOccurrenceSummary body
  | .recur b s n => binderOccurrenceSummary b ++ binderOccurrenceSummary s ++ binderOccurrenceSummary n
  | .share s r => binderOccurrenceSummary s ++ binderOccurrenceSummary r

/-- Executable binder-occurrence classification driven by the current syntax summary. -/
@[simp] def binderOccurs? (binderName : Nat) : HOTerm → Bool
  | .var _ => false
  | .atom => false
  | .succ t => binderOccurs? binderName t
  | .app f a => binderOccurs? binderName f || binderOccurs? binderName a
  | .lam idx body => decide (idx = binderName) || binderOccurs? binderName body
  | .recur b s n =>
      binderOccurs? binderName b || binderOccurs? binderName s || binderOccurs? binderName n
  | .share s r => binderOccurs? binderName s || binderOccurs? binderName r

@[simp] theorem freeVarOccurs_classification_eq_true_iff {name : Nat} {t : HOTerm} :
    freeVarOccurs? name t = true ↔ FreeVarOccurs name t := by
  induction t with
  | var idx =>
      by_cases hEq : idx = name
      · simp [freeVarOccurs?, FreeVarOccurs, hEq]
      · simp [freeVarOccurs?, FreeVarOccurs, hEq]
  | atom =>
      simp [freeVarOccurs?, FreeVarOccurs]
  | succ t ih =>
      simp [freeVarOccurs?, FreeVarOccurs, ih]
  | app f a ihf iha =>
      simp [freeVarOccurs?, FreeVarOccurs, ihf, iha, Bool.or_eq_true]
  | lam idx body ih =>
      by_cases hEq : idx = name
      · simp [freeVarOccurs?, FreeVarOccurs, hEq]
      · simp [freeVarOccurs?, FreeVarOccurs, hEq, ih]
  | recur b s n ihb ihs ihn =>
      simp [freeVarOccurs?, FreeVarOccurs, ihb, ihs, ihn, Bool.or_eq_true, or_assoc]
  | share s r ihs ihr =>
      simp [freeVarOccurs?, FreeVarOccurs, ihs, ihr, Bool.or_eq_true]

@[simp] theorem freeVarOccurs_classification_eq_false_iff {name : Nat} {t : HOTerm} :
    freeVarOccurs? name t = false ↔ ¬ FreeVarOccurs name t := by
  constructor
  · intro hFalse hOccurs
    have hTrue : freeVarOccurs? name t = true :=
      freeVarOccurs_classification_eq_true_iff.mpr hOccurs
    rw [hFalse] at hTrue
    cases hTrue
  · intro hNot
    cases hTrue : freeVarOccurs? name t with
    | false => rfl
    | true =>
        exfalso
        exact hNot (freeVarOccurs_classification_eq_true_iff.mp hTrue)

@[simp] theorem freshFor_classification_eq_true_iff {binderName : Nat} {t : HOTerm} :
    freshFor? binderName t = true ↔ FreshFor binderName t := by
  simp [freshFor?, FreshFor, freeVarOccurs_classification_eq_false_iff]

@[simp] theorem freshFor_classification_eq_false_iff {binderName : Nat} {t : HOTerm} :
    freshFor? binderName t = false ↔ ¬ FreshFor binderName t := by
  constructor
  · intro hFalse hFresh
    have hTrue : freshFor? binderName t = true :=
      freshFor_classification_eq_true_iff.mpr hFresh
    rw [hFalse] at hTrue
    cases hTrue
  · intro hNot
    cases hTrue : freshFor? binderName t with
    | false => rfl
    | true =>
        exfalso
        exact hNot (freshFor_classification_eq_true_iff.mp hTrue)

/-- Boolean gate for the current exact capture-side obligation surface. -/
@[simp] def captureSafeSubstitutionGate
    (name binderName : Nat) (arg body : HOTerm) : Bool :=
  decide (binderName ≠ name) &&
    freshFor? binderName arg &&
    binderFree? arg &&
    shareFree? arg &&
    binderFree? body &&
    shareFree? body

/-- Boolean gate for the current exact context-side obligation surface. -/
@[simp] def contextSafeSubstitutionGate (c : Context) (t : HOTerm) : Bool :=
  binderFreeContext? c && betaFreeContext? c && binderFree? t && betaFree? t

@[simp] theorem captureSafeSubstitutionGate_eq_true_iff
    {name binderName : Nat} {arg body : HOTerm} :
    captureSafeSubstitutionGate name binderName arg body = true ↔
      binderName ≠ name ∧
      FreshFor binderName arg ∧
      BinderFreeHOTerm arg ∧
      ShareFreeHOTerm arg ∧
      BinderFreeHOTerm body ∧
      ShareFreeHOTerm body := by
  simp [captureSafeSubstitutionGate, Bool.and_eq_true, and_assoc,
    binderFree_classification_eq_true_iff, shareFree_classification_eq_true_iff]

@[simp] theorem contextSafeSubstitutionGate_eq_true_iff
    {c : Context} {t : HOTerm} :
    contextSafeSubstitutionGate c t = true ↔
      BinderFreeContext c ∧ BetaFreeContext c ∧ BinderFreeHOTerm t ∧ BetaFreeHOTerm t := by
  simp [contextSafeSubstitutionGate, Bool.and_eq_true, and_assoc,
    binderFreeContext_classification_eq_true_iff, betaFreeContext_classification_eq_true_iff,
    binderFree_classification_eq_true_iff, betaFree_classification_eq_true_iff]

/-- Executable capture-side success token for the current exact obligation surface. -/
abbrev CaptureSafeSubstitutionCertificate
    (_name _binderName : Nat) (_arg _body : HOTerm) : Type := Unit

/-- Executable context-side success token for the current exact obligation surface. -/
abbrev ContextSafeSubstitutionCertificate (_c : Context) (_t : HOTerm) : Type := Unit

/-- Option-valued checker for the current exact capture-side obligation surface. -/
@[simp] def captureSafeSubstitutionCheck
    (name binderName : Nat) (arg body : HOTerm) :
    Option (CaptureSafeSubstitutionCertificate name binderName arg body) :=
  if captureSafeSubstitutionGate name binderName arg body = true then
    some ()
  else
    none

/-- Option-valued checker for the current exact context-side obligation surface. -/
@[simp] def contextSafeSubstitutionCheck (c : Context) (t : HOTerm) :
    Option (ContextSafeSubstitutionCertificate c t) :=
  if contextSafeSubstitutionGate c t = true then
    some ()
  else
    none

/-- Binder-free terms never expose a lambda at the top level. -/
theorem binderFree_not_lam {t : HOTerm}
    (h : BinderFreeHOTerm t) : ¬ IsLam t := by
  cases t <;> simp [BinderFreeHOTerm, IsLam] at h ⊢

/-- Binder-free terms are automatically beta-free on the current syntax. -/
theorem binderFree_implies_betaFree {t : HOTerm}
    (h : BinderFreeHOTerm t) : BetaFreeHOTerm t := by
  induction t with
  | var idx =>
      simp [BinderFreeHOTerm, BetaFreeHOTerm] at h ⊢
  | atom =>
      simp [BinderFreeHOTerm, BetaFreeHOTerm] at h ⊢
  | succ t ih =>
      simp [BinderFreeHOTerm, BetaFreeHOTerm] at h ⊢
      exact ih h
  | app f a ihf iha =>
      rcases h with ⟨hf, ha⟩
      exact ⟨binderFree_not_lam hf, ihf hf, iha ha⟩
  | lam idx body ih =>
      cases h
  | recur b s n ihb ihs ihn =>
      rcases h with ⟨hb, hs, hn⟩
      exact ⟨ihb hb, ihs hs, ihn hn⟩
  | share s r ihs ihr =>
      rcases h with ⟨hs, hr⟩
      exact ⟨ihs hs, ihr hr⟩

/-- Successful capture checks recover the current exact capture-safe obligation. -/
theorem captureSafeSubstitutionCheck_success_implies_obligation
    {name binderName : Nat} {arg body : HOTerm} :
    (∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert) →
      CaptureSafeSubstitutionObligation name binderName arg body := by
  rintro ⟨_, hCheck⟩
  have hGate : captureSafeSubstitutionGate name binderName arg body = true := by
    by_cases hGate : captureSafeSubstitutionGate name binderName arg body = true
    · exact hGate
    · have hNone :
          captureSafeSubstitutionCheck name binderName arg body = none := by
          unfold captureSafeSubstitutionCheck
          rw [if_neg hGate]
      rw [hNone] at hCheck
      cases hCheck
  rcases captureSafeSubstitutionGate_eq_true_iff.mp hGate with
    ⟨hDistinct, hFresh, hArgBinder, hArgShare, hBodyBinder, hBodyShare⟩
  exact {
    binderAware := {
      binderDistinct := hDistinct
      freshArgument := hFresh
    }
    argumentBinderFree := hArgBinder
    argumentShareFree := hArgShare
    bodyBinderFree := hBodyBinder
    bodyShareFree := hBodyShare
  }

/-- Successful context checks recover the current exact context-safe obligation. -/
theorem contextSafeSubstitutionCheck_success_implies_obligation
    {c : Context} {t : HOTerm} :
    (∃ cert, contextSafeSubstitutionCheck c t = some cert) →
      ContextSafeSubstitutionObligation c t := by
  rintro ⟨_, hCheck⟩
  have hGate : contextSafeSubstitutionGate c t = true := by
    by_cases hGate : contextSafeSubstitutionGate c t = true
    · exact hGate
    · have hNone : contextSafeSubstitutionCheck c t = none := by
          unfold contextSafeSubstitutionCheck
          rw [if_neg hGate]
      rw [hNone] at hCheck
      cases hCheck
  rcases contextSafeSubstitutionGate_eq_true_iff.mp hGate with
    ⟨hBinderContext, hBetaContext, hBinderTerm, hBetaTerm⟩
  exact {
    binderFreeContext := hBinderContext
    betaFreeContext := hBetaContext
    termBinderFree := hBinderTerm
    termBetaFree := hBetaTerm
  }

/-- Exact capture-side obligations are accepted by the executable checker. -/
theorem captureSafeSubstitutionCheck_succeeds_of_captureSafeSubstitutionObligation
    {name binderName : Nat} {arg body : HOTerm}
    (h : CaptureSafeSubstitutionObligation name binderName arg body) :
    ∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert := by
  have hDistinctBool : decide (binderName ≠ name) = true := by
    simp [h.binderAware.binderDistinct]
  have hFreshBool : freshFor? binderName arg = true :=
    freshFor_classification_eq_true_iff.mpr h.binderAware.freshArgument
  have hArgBinderBool : binderFree? arg = true :=
    binderFree_classification_eq_true_iff.mpr h.argumentBinderFree
  have hArgShareBool : shareFree? arg = true :=
    shareFree_classification_eq_true_iff.mpr h.argumentShareFree
  have hBodyBinderBool : binderFree? body = true :=
    binderFree_classification_eq_true_iff.mpr h.bodyBinderFree
  have hBodyShareBool : shareFree? body = true :=
    shareFree_classification_eq_true_iff.mpr h.bodyShareFree
  have hGate : captureSafeSubstitutionGate name binderName arg body = true :=
    by
      unfold captureSafeSubstitutionGate
      rw [hDistinctBool, hFreshBool, hArgBinderBool, hArgShareBool, hBodyBinderBool, hBodyShareBool]
      rfl
  refine ⟨(), ?_⟩
  unfold captureSafeSubstitutionCheck
  rw [if_pos hGate]

/-- Conservative binder-free and share-free inputs are accepted by the capture checker. -/
theorem captureSafeSubstitutionCheck_succeeds_of_binderFree_shareFree
    {name binderName : Nat} {arg body : HOTerm}
    (hDistinct : binderName ≠ name)
    (hFresh : FreshFor binderName arg)
    (hArgBinder : BinderFreeHOTerm arg)
    (hArgShare : ShareFreeHOTerm arg)
    (hBodyBinder : BinderFreeHOTerm body)
    (hBodyShare : ShareFreeHOTerm body) :
    ∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert := by
  exact captureSafeSubstitutionCheck_succeeds_of_captureSafeSubstitutionObligation {
    binderAware := {
      binderDistinct := hDistinct
      freshArgument := hFresh
    }
    argumentBinderFree := hArgBinder
    argumentShareFree := hArgShare
    bodyBinderFree := hBodyBinder
    bodyShareFree := hBodyShare
  }

/-- Closed-fragment share-free inputs are accepted by the capture checker. -/
theorem captureSafeSubstitutionCheck_succeeds_of_closedFragment_shareFree
    {name binderName : Nat} {arg body : HOTerm}
    (hDistinct : binderName ≠ name)
    (hFresh : FreshFor binderName arg)
    (hArgClosed : ClosedFragment arg)
    (hArgShare : ShareFreeHOTerm arg)
    (hBodyClosed : ClosedFragment body)
    (hBodyShare : ShareFreeHOTerm body) :
    ∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert := by
  exact captureSafeSubstitutionCheck_succeeds_of_binderFree_shareFree
    hDistinct hFresh
    (closedFragment_binderFree hArgClosed)
    hArgShare
    (closedFragment_binderFree hBodyClosed)
    hBodyShare

/-- Exact context-safe obligations are accepted by the executable context checker. -/
theorem contextSafeSubstitutionCheck_succeeds_of_contextSafeSubstitutionObligation
    {c : Context} {t : HOTerm}
    (h : ContextSafeSubstitutionObligation c t) :
    ∃ cert, contextSafeSubstitutionCheck c t = some cert := by
  have hBinderContextBool : binderFreeContext? c = true :=
    binderFreeContext_classification_eq_true_iff.mpr h.binderFreeContext
  have hBetaContextBool : betaFreeContext? c = true :=
    betaFreeContext_classification_eq_true_iff.mpr h.betaFreeContext
  have hBinderTermBool : binderFree? t = true :=
    binderFree_classification_eq_true_iff.mpr h.termBinderFree
  have hBetaTermBool : betaFree? t = true :=
    betaFree_classification_eq_true_iff.mpr h.termBetaFree
  have hGate : contextSafeSubstitutionGate c t = true :=
    by
      unfold contextSafeSubstitutionGate
      rw [hBinderContextBool, hBetaContextBool, hBinderTermBool, hBetaTermBool]
      rfl
  refine ⟨(), ?_⟩
  unfold contextSafeSubstitutionCheck
  rw [if_pos hGate]

/-- Conservative binder-free and beta-free inputs are accepted by the context checker. -/
theorem contextSafeSubstitutionCheck_succeeds_of_binderFree_betaFree
    {c : Context} {t : HOTerm}
    (hBinderContext : BinderFreeContext c)
    (hBetaContext : BetaFreeContext c)
    (hBinderTerm : BinderFreeHOTerm t)
    (hBetaTerm : BetaFreeHOTerm t) :
    ∃ cert, contextSafeSubstitutionCheck c t = some cert := by
  exact contextSafeSubstitutionCheck_succeeds_of_contextSafeSubstitutionObligation {
    binderFreeContext := hBinderContext
    betaFreeContext := hBetaContext
    termBinderFree := hBinderTerm
    termBetaFree := hBetaTerm
  }

/-- Closed-fragment terms are accepted by the context checker when the context is already exact. -/
theorem contextSafeSubstitutionCheck_succeeds_of_closedFragment
    {c : Context} {t : HOTerm}
    (hBinderContext : BinderFreeContext c)
    (hBetaContext : BetaFreeContext c)
    (hClosed : ClosedFragment t) :
    ∃ cert, contextSafeSubstitutionCheck c t = some cert := by
  exact contextSafeSubstitutionCheck_succeeds_of_binderFree_betaFree
    hBinderContext hBetaContext (closedFragment_binderFree hClosed) (closedFragment_betaFree hClosed)

/-- Successful capture checks preserve binder-freeness of the checked substitution. -/
theorem captureSafeSubstitutionCheck_success_preserves_binderFree
    {name binderName : Nat} {arg body : HOTerm} :
    (∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert) →
      BinderFreeHOTerm (binderAwareSubstitute name arg body) := by
  intro hSuccess
  exact captureSafeSubstitutionObligation_preserves_binder_free
    (captureSafeSubstitutionCheck_success_implies_obligation hSuccess)

/-- Successful capture checks preserve share-freeness of the checked substitution. -/
theorem captureSafeSubstitutionCheck_success_preserves_shareFree
    {name binderName : Nat} {arg body : HOTerm} :
    (∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert) →
      ShareFreeHOTerm (binderAwareSubstitute name arg body) := by
  intro hSuccess
  exact captureSafeSubstitutionObligation_preserves_share_free
    (captureSafeSubstitutionCheck_success_implies_obligation hSuccess)

/-- Successful capture checks preserve beta-freeness on the current conservative fragment. -/
theorem captureSafeSubstitutionCheck_success_preserves_betaFree
    {name binderName : Nat} {arg body : HOTerm} :
    (∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert) →
      BetaFreeHOTerm (binderAwareSubstitute name arg body) := by
  intro hSuccess
  exact binderFree_implies_betaFree
    (captureSafeSubstitutionCheck_success_preserves_binderFree hSuccess)

/-- Successful context checks preserve binder-freeness under connectorging. -/
theorem contextSafeSubstitutionCheck_success_preserves_binderFree_connector
    {c : Context} {t : HOTerm} :
    (∃ cert, contextSafeSubstitutionCheck c t = some cert) →
      BinderFreeHOTerm (Context.connector c t) := by
  intro hSuccess
  exact contextSafeSubstitutionObligation_connector_binder_free
    (contextSafeSubstitutionCheck_success_implies_obligation hSuccess)

/-- Successful context checks preserve beta-freeness under connectorging. -/
theorem contextSafeSubstitutionCheck_success_preserves_betaFree_connector
    {c : Context} {t : HOTerm} :
    (∃ cert, contextSafeSubstitutionCheck c t = some cert) →
      BetaFreeHOTerm (Context.connector c t) := by
  intro hSuccess
  exact contextSafeSubstitutionObligation_connector_beta_free
    (contextSafeSubstitutionCheck_success_implies_obligation hSuccess)

/-- The executable capture-decision layer remains exact only at the current obligation surface. -/
theorem captureSafeSubstitutionCheck_success_is_obligation_scoped
    {name binderName : Nat} {arg body : HOTerm} :
    (∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert) →
      CaptureSafeSubstitutionObligation name binderName arg body :=
  captureSafeSubstitutionCheck_success_implies_obligation

/-- Full capture-avoiding semantics remains open at the current executable decision layer. -/
theorem capture_decision_full_capture_semantics_open :
    FullCaptureSemanticsStatus :=
  full_capture_semantics_open

/-- Theorem-visible boundary marker for the current executable decision layer. -/
structure CaptureDecisionBoundaryStatus : Prop where
  obligationScoped :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      (∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert) →
        CaptureSafeSubstitutionObligation name binderName arg body
  fullCaptureSemanticsOpen : FullCaptureSemanticsStatus

/-- Canonical boundary marker for the current executable decision layer. -/
theorem capture_decision_boundary_status : CaptureDecisionBoundaryStatus := by
  refine ⟨?_, ?_⟩
  · intro name binderName arg body hSuccess
    exact captureSafeSubstitutionCheck_success_is_obligation_scoped hSuccess
  · exact capture_decision_full_capture_semantics_open

/-- Paper-facing catalog for the current higher-order capture-decision layer. -/
structure HigherOrderCaptureDecidableCatalog : Prop where
  freeVarOccursClassificationIff :
    ∀ {name : Nat} {t : HOTerm}, freeVarOccurs? name t = true ↔ FreeVarOccurs name t
  freshForClassificationIff :
    ∀ {binderName : Nat} {t : HOTerm}, freshFor? binderName t = true ↔ FreshFor binderName t
  captureSafeGateIff :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      captureSafeSubstitutionGate name binderName arg body = true ↔
        binderName ≠ name ∧ FreshFor binderName arg ∧ BinderFreeHOTerm arg ∧
          ShareFreeHOTerm arg ∧ BinderFreeHOTerm body ∧ ShareFreeHOTerm body
  contextSafeGateIff :
    ∀ {c : Context} {t : HOTerm},
      contextSafeSubstitutionGate c t = true ↔
        BinderFreeContext c ∧ BetaFreeContext c ∧ BinderFreeHOTerm t ∧ BetaFreeHOTerm t
  captureSafeCheckerSound :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      (∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert) →
        CaptureSafeSubstitutionObligation name binderName arg body
  contextSafeCheckerSound :
    ∀ {c : Context} {t : HOTerm},
      (∃ cert, contextSafeSubstitutionCheck c t = some cert) →
        ContextSafeSubstitutionObligation c t
  captureSafeCheckerTotalOnExactObligation :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      CaptureSafeSubstitutionObligation name binderName arg body →
        ∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert
  captureSafeCheckerTotalOnBinderFreeShareFree :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      binderName ≠ name → FreshFor binderName arg → BinderFreeHOTerm arg → ShareFreeHOTerm arg →
        BinderFreeHOTerm body → ShareFreeHOTerm body →
          ∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert
  captureSafeCheckerTotalOnClosedShareFree :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      binderName ≠ name → FreshFor binderName arg → ClosedFragment arg → ShareFreeHOTerm arg →
        ClosedFragment body → ShareFreeHOTerm body →
          ∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert
  contextSafeCheckerTotalOnExactObligation :
    ∀ {c : Context} {t : HOTerm},
      ContextSafeSubstitutionObligation c t →
        ∃ cert, contextSafeSubstitutionCheck c t = some cert
  contextSafeCheckerTotalOnBinderFreeBetaFree :
    ∀ {c : Context} {t : HOTerm},
      BinderFreeContext c → BetaFreeContext c → BinderFreeHOTerm t → BetaFreeHOTerm t →
        ∃ cert, contextSafeSubstitutionCheck c t = some cert
  contextSafeCheckerTotalOnClosedFragment :
    ∀ {c : Context} {t : HOTerm},
      BinderFreeContext c → BetaFreeContext c → ClosedFragment t →
        ∃ cert, contextSafeSubstitutionCheck c t = some cert
  captureSafeCheckerBinderFreePreservation :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      (∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert) →
        BinderFreeHOTerm (binderAwareSubstitute name arg body)
  captureSafeCheckerShareFreePreservation :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      (∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert) →
        ShareFreeHOTerm (binderAwareSubstitute name arg body)
  captureSafeCheckerBetaFreePreservation :
    ∀ {name binderName : Nat} {arg body : HOTerm},
      (∃ cert, captureSafeSubstitutionCheck name binderName arg body = some cert) →
        BetaFreeHOTerm (binderAwareSubstitute name arg body)
  contextSafeCheckerBinderFreeConnectorPreservation :
    ∀ {c : Context} {t : HOTerm},
      (∃ cert, contextSafeSubstitutionCheck c t = some cert) →
        BinderFreeHOTerm (Context.connector c t)
  contextSafeCheckerBetaFreeConnectorPreservation :
    ∀ {c : Context} {t : HOTerm},
      (∃ cert, contextSafeSubstitutionCheck c t = some cert) →
        BetaFreeHOTerm (Context.connector c t)
  boundaryStatus : CaptureDecisionBoundaryStatus

/-- Canonical catalog for the current higher-order capture-decision layer. -/
theorem higher_order_capture_decidable_catalog :
    HigherOrderCaptureDecidableCatalog := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro name t
    exact freeVarOccurs_classification_eq_true_iff
  · intro binderName t
    exact freshFor_classification_eq_true_iff
  · intro name binderName arg body
    exact captureSafeSubstitutionGate_eq_true_iff
  · intro c t
    exact contextSafeSubstitutionGate_eq_true_iff
  · intro name binderName arg body hSuccess
    exact captureSafeSubstitutionCheck_success_implies_obligation hSuccess
  · intro c t hSuccess
    exact contextSafeSubstitutionCheck_success_implies_obligation hSuccess
  · intro name binderName arg body h
    exact captureSafeSubstitutionCheck_succeeds_of_captureSafeSubstitutionObligation h
  · intro name binderName arg body hDistinct hFresh hArgBinder hArgShare hBodyBinder hBodyShare
    exact captureSafeSubstitutionCheck_succeeds_of_binderFree_shareFree
      hDistinct hFresh hArgBinder hArgShare hBodyBinder hBodyShare
  · intro name binderName arg body hDistinct hFresh hArgClosed hArgShare hBodyClosed hBodyShare
    exact captureSafeSubstitutionCheck_succeeds_of_closedFragment_shareFree
      hDistinct hFresh hArgClosed hArgShare hBodyClosed hBodyShare
  · intro c t h
    exact contextSafeSubstitutionCheck_succeeds_of_contextSafeSubstitutionObligation h
  · intro c t hBinderContext hBetaContext hBinderTerm hBetaTerm
    exact contextSafeSubstitutionCheck_succeeds_of_binderFree_betaFree
      hBinderContext hBetaContext hBinderTerm hBetaTerm
  · intro c t hBinderContext hBetaContext hClosed
    exact contextSafeSubstitutionCheck_succeeds_of_closedFragment hBinderContext hBetaContext hClosed
  · intro name binderName arg body hSuccess
    exact captureSafeSubstitutionCheck_success_preserves_binderFree hSuccess
  · intro name binderName arg body hSuccess
    exact captureSafeSubstitutionCheck_success_preserves_shareFree hSuccess
  · intro name binderName arg body hSuccess
    exact captureSafeSubstitutionCheck_success_preserves_betaFree hSuccess
  · intro c t hSuccess
    exact contextSafeSubstitutionCheck_success_preserves_binderFree_connector hSuccess
  · intro c t hSuccess
    exact contextSafeSubstitutionCheck_success_preserves_betaFree_connector hSuccess
  · exact capture_decision_boundary_status

end OperatorKO7.HigherOrderRewritingCaptureDecidable
