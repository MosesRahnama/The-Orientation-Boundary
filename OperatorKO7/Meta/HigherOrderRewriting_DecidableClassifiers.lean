import OperatorKO7.Meta.HigherOrderRewriting_CaptureSubfamilies

/-!
# Higher-Order Rewriting Decidable Classifiers

This module makes the conservative higher-order subfamily layer executable.
It mirrors the declared Prop predicates with boolean classifiers and packages the
resulting iff theorems and closure interactions in a theorem-visible catalog.
-/

namespace OperatorKO7.HigherOrderRewritingDecidableClassifiers

open OperatorKO7.SharingBarrierLift
open OperatorKO7.HigherOrderRewritingSyntax
open OperatorKO7.HigherOrderRewritingBetaBinder
open OperatorKO7.HigherOrderRewritingCaptureSubfamilies

/-- Executable classifier for top-level lambda terms. -/
@[simp] def isLam : HOTerm → Bool
  | .lam _ _ => true
  | _ => false

/-- Executable classifier for binder-free higher-order terms. -/
@[simp] def binderFree? : HOTerm → Bool
  | .var _ => true
  | .atom => true
  | .succ t => binderFree? t
  | .app f a => binderFree? f && binderFree? a
  | .lam _ _ => false
  | .recur b s n => binderFree? b && binderFree? s && binderFree? n
  | .share s r => binderFree? s && binderFree? r

/-- Executable classifier for share-free higher-order terms. -/
@[simp] def shareFree? : HOTerm → Bool
  | .var _ => true
  | .atom => true
  | .succ t => shareFree? t
  | .app f a => shareFree? f && shareFree? a
  | .lam _ body => shareFree? body
  | .recur b s n => shareFree? b && shareFree? s && shareFree? n
  | .share _ _ => false

/-- Executable classifier for beta-free higher-order terms. -/
@[simp] def betaFree? : HOTerm → Bool
  | .var _ => true
  | .atom => true
  | .succ t => betaFree? t
  | .app f a => (! isLam f) && betaFree? f && betaFree? a
  | .lam _ body => betaFree? body
  | .recur b s n => betaFree? b && betaFree? s && betaFree? n
  | .share s r => betaFree? s && betaFree? r

/-- Executable classifier for the conservative linear fragment. -/
@[simp] def linear? (t : HOTerm) : Bool :=
  binderFree? t && shareFree? t

/-- Internal executable classifier for the existing closed fragment. -/
@[simp] private def closedFragmentClassifier : HOTerm → Bool
  | .var _ => false
  | .atom => true
  | .succ t => closedFragmentClassifier t
  | .app f a => closedFragmentClassifier f && closedFragmentClassifier a
  | .lam _ _ => false
  | .recur b s n =>
      closedFragmentClassifier b && closedFragmentClassifier s && closedFragmentClassifier n
  | .share s r => closedFragmentClassifier s && closedFragmentClassifier r

/-- Executable classifier for the conservative DAG/shared fragment. -/
@[simp] def dagShared? (t : HOTerm) : Bool :=
  closedFragmentClassifier t

/-- Executable classifier for binder-free higher-order contexts. -/
@[simp] def binderFreeContext? : Context → Bool
  | .hole => true
  | .succ c => binderFreeContext? c
  | .appLeft c arg => binderFreeContext? c && closedFragmentClassifier arg
  | .appRight fn c => closedFragmentClassifier fn && binderFreeContext? c
  | .lam _ _ => false
  | .recurBase c s n =>
      binderFreeContext? c && closedFragmentClassifier s && closedFragmentClassifier n
  | .recurStep b c n =>
      closedFragmentClassifier b && binderFreeContext? c && closedFragmentClassifier n
  | .recurArg b s c =>
      closedFragmentClassifier b && closedFragmentClassifier s && binderFreeContext? c
  | .shareLeft c r => binderFreeContext? c && closedFragmentClassifier r
  | .shareRight s c => closedFragmentClassifier s && binderFreeContext? c

/-- Executable classifier for beta-free higher-order contexts. -/
@[simp] def betaFreeContext? : Context → Bool
  | .hole => true
  | .succ c => betaFreeContext? c
  | .appLeft _ _ => false
  | .appRight fn c => (! isLam fn) && betaFree? fn && betaFreeContext? c
  | .lam _ c => betaFreeContext? c
  | .recurBase c s n => betaFreeContext? c && betaFree? s && betaFree? n
  | .recurStep b c n => betaFree? b && betaFreeContext? c && betaFree? n
  | .recurArg b s c => betaFree? b && betaFree? s && betaFreeContext? c
  | .shareLeft c r => betaFreeContext? c && betaFree? r
  | .shareRight s c => betaFree? s && betaFreeContext? c

@[simp] theorem isLam_classifier_eq_true_iff {t : HOTerm} :
    isLam t = true ↔ IsLam t := by
  cases t <;> simp [isLam, IsLam]

@[simp] theorem isLam_classifier_eq_false_iff {t : HOTerm} :
    isLam t = false ↔ ¬ IsLam t := by
  cases t <;> simp [isLam, IsLam]

@[simp] private theorem closedFragment_classifier_eq_true_iff {t : HOTerm} :
    closedFragmentClassifier t = true ↔ ClosedFragment t := by
  induction t with
  | var idx =>
      constructor <;> intro h <;> cases h
  | atom =>
      constructor
      · intro _
        exact ClosedFragment.atom
      · intro _
        rfl
  | succ t ih =>
      calc
        closedFragmentClassifier (.succ t) = true ↔ closedFragmentClassifier t = true := by
          simp [closedFragmentClassifier]
        _ ↔ ClosedFragment t := ih
        _ ↔ ClosedFragment (.succ t) := by
          constructor
          · intro h
            exact ClosedFragment.succ h
          · intro h
            cases h with
            | succ ht => exact ht
  | app f a ihf iha =>
      calc
        closedFragmentClassifier (.app f a) = true ↔
            closedFragmentClassifier f = true ∧ closedFragmentClassifier a = true := by
          simp [closedFragmentClassifier, Bool.and_eq_true]
        _ ↔ ClosedFragment f ∧ ClosedFragment a := by
          simp [ihf, iha]
        _ ↔ ClosedFragment (.app f a) := by
          constructor
          · rintro ⟨hf, ha⟩
            exact ClosedFragment.app hf ha
          · intro h
            cases h with
            | app hf ha => exact ⟨hf, ha⟩
  | lam name body ih =>
      constructor <;> intro h <;> cases h
  | recur b s n ihb ihs ihn =>
      calc
        closedFragmentClassifier (.recur b s n) = true ↔
            closedFragmentClassifier b = true ∧
              closedFragmentClassifier s = true ∧
              closedFragmentClassifier n = true := by
          simp [closedFragmentClassifier, Bool.and_eq_true, and_assoc]
        _ ↔ ClosedFragment b ∧ ClosedFragment s ∧ ClosedFragment n := by
          simp [ihb, ihs, ihn]
        _ ↔ ClosedFragment (.recur b s n) := by
          constructor
          · rintro ⟨hb, hs, hn⟩
            exact ClosedFragment.recur hb hs hn
          · intro h
            cases h with
            | recur hb hs hn => exact ⟨hb, hs, hn⟩
  | share s r ihs ihr =>
      calc
        closedFragmentClassifier (.share s r) = true ↔
            closedFragmentClassifier s = true ∧ closedFragmentClassifier r = true := by
          simp [closedFragmentClassifier, Bool.and_eq_true]
        _ ↔ ClosedFragment s ∧ ClosedFragment r := by
          simp [ihs, ihr]
        _ ↔ ClosedFragment (.share s r) := by
          constructor
          · rintro ⟨hs, hr⟩
            exact ClosedFragment.share hs hr
          · intro h
            cases h with
            | share hs hr => exact ⟨hs, hr⟩

@[simp] theorem binderFree_classifier_eq_true_iff {t : HOTerm} :
    binderFree? t = true ↔ BinderFreeHOTerm t := by
  induction t with
  | var idx => simp [binderFree?, BinderFreeHOTerm]
  | atom => simp [binderFree?, BinderFreeHOTerm]
  | succ t ih => simp [binderFree?, BinderFreeHOTerm, ih]
  | app f a ihf iha =>
      simp [binderFree?, BinderFreeHOTerm, ihf, iha, Bool.and_eq_true]
  | lam name body ih => simp [binderFree?, BinderFreeHOTerm]
  | recur b s n ihb ihs ihn =>
      simp [binderFree?, BinderFreeHOTerm, ihb, ihs, ihn, Bool.and_eq_true, and_assoc]
  | share s r ihs ihr =>
      simp [binderFree?, BinderFreeHOTerm, ihs, ihr, Bool.and_eq_true]

@[simp] theorem shareFree_classifier_eq_true_iff {t : HOTerm} :
    shareFree? t = true ↔ ShareFreeHOTerm t := by
  induction t with
  | var idx => simp [shareFree?, ShareFreeHOTerm]
  | atom => simp [shareFree?, ShareFreeHOTerm]
  | succ t ih => simp [shareFree?, ShareFreeHOTerm, ih]
  | app f a ihf iha =>
      simp [shareFree?, ShareFreeHOTerm, ihf, iha, Bool.and_eq_true]
  | lam name body ih => simp [shareFree?, ShareFreeHOTerm, ih]
  | recur b s n ihb ihs ihn =>
      simp [shareFree?, ShareFreeHOTerm, ihb, ihs, ihn, Bool.and_eq_true, and_assoc]
  | share s r ihs ihr =>
      simp [shareFree?, ShareFreeHOTerm]

@[simp] theorem betaFree_classifier_eq_true_iff {t : HOTerm} :
    betaFree? t = true ↔ BetaFreeHOTerm t := by
  induction t with
  | var idx => simp [betaFree?, BetaFreeHOTerm]
  | atom => simp [betaFree?, BetaFreeHOTerm]
  | succ t ih => simp [betaFree?, BetaFreeHOTerm, ih]
  | app f a ihf iha =>
      calc
        betaFree? (.app f a) = true ↔
            isLam f = false ∧ betaFree? f = true ∧ betaFree? a = true := by
          simp [betaFree?, Bool.and_eq_true, and_assoc]
        _ ↔ ¬ IsLam f ∧ BetaFreeHOTerm f ∧ BetaFreeHOTerm a := by
          constructor
          · rintro ⟨hLam, hf, ha⟩
            exact ⟨isLam_classifier_eq_false_iff.mp hLam, ihf.mp hf, iha.mp ha⟩
          · rintro ⟨hLam, hf, ha⟩
            exact ⟨isLam_classifier_eq_false_iff.mpr hLam, ihf.mpr hf, iha.mpr ha⟩
        _ ↔ BetaFreeHOTerm (.app f a) := by
          rfl
  | lam name body ih => simp [betaFree?, BetaFreeHOTerm, ih]
  | recur b s n ihb ihs ihn =>
      simp [betaFree?, BetaFreeHOTerm, ihb, ihs, ihn, Bool.and_eq_true, and_assoc]
  | share s r ihs ihr =>
      simp [betaFree?, BetaFreeHOTerm, ihs, ihr, Bool.and_eq_true]

@[simp] theorem linear_classifier_eq_true_iff {t : HOTerm} :
    linear? t = true ↔ LinearHOTerm t := by
  simp [linear?, LinearHOTerm, Bool.and_eq_true,
    binderFree_classifier_eq_true_iff, shareFree_classifier_eq_true_iff]

@[simp] theorem dagShared_classifier_eq_true_iff {t : HOTerm} :
    dagShared? t = true ↔ DAGSharedHOTerm t := by
  show closedFragmentClassifier t = true ↔ ClosedFragment t
  exact closedFragment_classifier_eq_true_iff (t := t)

@[simp] theorem binderFreeContext_classifier_eq_true_iff {c : Context} :
    binderFreeContext? c = true ↔ BinderFreeContext c := by
  induction c with
  | hole =>
      constructor
      · intro _
        exact BinderFreeContext.hole
      · intro _
        rfl
  | succ c ih =>
      calc
        binderFreeContext? (.succ c) = true ↔ binderFreeContext? c = true := by
          simp [binderFreeContext?]
        _ ↔ BinderFreeContext c := ih
        _ ↔ BinderFreeContext (.succ c) := by
          constructor
          · intro h
            exact BinderFreeContext.succ h
          · intro h
            cases h with
            | succ hc => exact hc
  | appLeft c arg ih =>
      calc
        binderFreeContext? (.appLeft c arg) = true ↔
            binderFreeContext? c = true ∧ closedFragmentClassifier arg = true := by
          simp [binderFreeContext?, Bool.and_eq_true]
        _ ↔ BinderFreeContext c ∧ ClosedFragment arg := by
          simp [ih, closedFragment_classifier_eq_true_iff]
        _ ↔ BinderFreeContext (.appLeft c arg) := by
          constructor
          · rintro ⟨hc, harg⟩
            exact BinderFreeContext.appLeft hc harg
          · intro h
            cases h with
            | appLeft hc harg => exact ⟨hc, harg⟩
  | appRight fn c ih =>
      calc
        binderFreeContext? (.appRight fn c) = true ↔
            closedFragmentClassifier fn = true ∧ binderFreeContext? c = true := by
          simp [binderFreeContext?, Bool.and_eq_true]
        _ ↔ ClosedFragment fn ∧ BinderFreeContext c := by
          simp [ih, closedFragment_classifier_eq_true_iff]
        _ ↔ BinderFreeContext (.appRight fn c) := by
          constructor
          · rintro ⟨hfn, hc⟩
            exact BinderFreeContext.appRight hfn hc
          · intro h
            cases h with
            | appRight hfn hc => exact ⟨hfn, hc⟩
  | lam name c ih =>
      constructor <;> intro h <;> cases h
  | recurBase c s n ih =>
      calc
        binderFreeContext? (.recurBase c s n) = true ↔
            binderFreeContext? c = true ∧
              closedFragmentClassifier s = true ∧
              closedFragmentClassifier n = true := by
          simp [binderFreeContext?, Bool.and_eq_true, and_assoc]
        _ ↔ BinderFreeContext c ∧ ClosedFragment s ∧ ClosedFragment n := by
          simp [ih, closedFragment_classifier_eq_true_iff]
        _ ↔ BinderFreeContext (.recurBase c s n) := by
          constructor
          · rintro ⟨hc, hs, hn⟩
            exact BinderFreeContext.recurBase hc hs hn
          · intro h
            cases h with
            | recurBase hc hs hn => exact ⟨hc, hs, hn⟩
  | recurStep b c n ih =>
      calc
        binderFreeContext? (.recurStep b c n) = true ↔
            closedFragmentClassifier b = true ∧
              binderFreeContext? c = true ∧
              closedFragmentClassifier n = true := by
          simp [binderFreeContext?, Bool.and_eq_true, and_assoc]
        _ ↔ ClosedFragment b ∧ BinderFreeContext c ∧ ClosedFragment n := by
          simp [ih, closedFragment_classifier_eq_true_iff]
        _ ↔ BinderFreeContext (.recurStep b c n) := by
          constructor
          · rintro ⟨hb, hc, hn⟩
            exact BinderFreeContext.recurStep hb hc hn
          · intro h
            cases h with
            | recurStep hb hc hn => exact ⟨hb, hc, hn⟩
  | recurArg b s c ih =>
      calc
        binderFreeContext? (.recurArg b s c) = true ↔
            closedFragmentClassifier b = true ∧
              closedFragmentClassifier s = true ∧
              binderFreeContext? c = true := by
          simp [binderFreeContext?, Bool.and_eq_true, and_assoc]
        _ ↔ ClosedFragment b ∧ ClosedFragment s ∧ BinderFreeContext c := by
          simp [ih, closedFragment_classifier_eq_true_iff]
        _ ↔ BinderFreeContext (.recurArg b s c) := by
          constructor
          · rintro ⟨hb, hs, hc⟩
            exact BinderFreeContext.recurArg hb hs hc
          · intro h
            cases h with
            | recurArg hb hs hc => exact ⟨hb, hs, hc⟩
  | shareLeft c r ih =>
      calc
        binderFreeContext? (.shareLeft c r) = true ↔
            binderFreeContext? c = true ∧ closedFragmentClassifier r = true := by
          simp [binderFreeContext?, Bool.and_eq_true]
        _ ↔ BinderFreeContext c ∧ ClosedFragment r := by
          simp [ih, closedFragment_classifier_eq_true_iff]
        _ ↔ BinderFreeContext (.shareLeft c r) := by
          constructor
          · rintro ⟨hc, hr⟩
            exact BinderFreeContext.shareLeft hc hr
          · intro h
            cases h with
            | shareLeft hc hr => exact ⟨hc, hr⟩
  | shareRight s c ih =>
      calc
        binderFreeContext? (.shareRight s c) = true ↔
            closedFragmentClassifier s = true ∧ binderFreeContext? c = true := by
          simp [binderFreeContext?, Bool.and_eq_true]
        _ ↔ ClosedFragment s ∧ BinderFreeContext c := by
          simp [ih, closedFragment_classifier_eq_true_iff]
        _ ↔ BinderFreeContext (.shareRight s c) := by
          constructor
          · rintro ⟨hs, hc⟩
            exact BinderFreeContext.shareRight hs hc
          · intro h
            cases h with
            | shareRight hs hc => exact ⟨hs, hc⟩

@[simp] theorem betaFreeContext_classifier_eq_true_iff {c : Context} :
    betaFreeContext? c = true ↔ BetaFreeContext c := by
  induction c with
  | hole =>
      constructor
      · intro _
        exact BetaFreeContext.hole
      · intro _
        rfl
  | succ c ih =>
      calc
        betaFreeContext? (.succ c) = true ↔ betaFreeContext? c = true := by
          simp [betaFreeContext?]
        _ ↔ BetaFreeContext c := ih
        _ ↔ BetaFreeContext (.succ c) := by
          constructor
          · intro h
            exact BetaFreeContext.succ h
          · intro h
            cases h with
            | succ hc => exact hc
  | appLeft c arg ih =>
      constructor <;> intro h <;> cases h
  | appRight fn c ih =>
      calc
        betaFreeContext? (.appRight fn c) = true ↔
            isLam fn = false ∧ betaFree? fn = true ∧ betaFreeContext? c = true := by
          simp [betaFreeContext?, Bool.and_eq_true, and_assoc]
        _ ↔ ¬ IsLam fn ∧ BetaFreeHOTerm fn ∧ BetaFreeContext c := by
          constructor
          · rintro ⟨hLam, hBeta, hc⟩
            exact ⟨isLam_classifier_eq_false_iff.mp hLam,
              betaFree_classifier_eq_true_iff.mp hBeta,
              ih.mp hc⟩
          · rintro ⟨hLam, hBeta, hc⟩
            exact ⟨isLam_classifier_eq_false_iff.mpr hLam,
              betaFree_classifier_eq_true_iff.mpr hBeta,
              ih.mpr hc⟩
        _ ↔ BetaFreeContext (.appRight fn c) := by
          constructor
          · rintro ⟨hNotLam, hBeta, hc⟩
            exact BetaFreeContext.appRight hNotLam hBeta hc
          · intro h
            cases h with
            | appRight hNotLam hBeta hc => exact ⟨hNotLam, hBeta, hc⟩
  | lam name c ih =>
      calc
        betaFreeContext? (.lam name c) = true ↔ betaFreeContext? c = true := by
          simp [betaFreeContext?]
        _ ↔ BetaFreeContext c := ih
        _ ↔ BetaFreeContext (.lam name c) := by
          constructor
          · intro h
            exact BetaFreeContext.lam h
          · intro h
            cases h with
            | lam hc => exact hc
  | recurBase c s n ih =>
      calc
        betaFreeContext? (.recurBase c s n) = true ↔
            betaFreeContext? c = true ∧ betaFree? s = true ∧ betaFree? n = true := by
          simp [betaFreeContext?, Bool.and_eq_true, and_assoc]
        _ ↔ BetaFreeContext c ∧ BetaFreeHOTerm s ∧ BetaFreeHOTerm n := by
          simp [ih, betaFree_classifier_eq_true_iff]
        _ ↔ BetaFreeContext (.recurBase c s n) := by
          constructor
          · rintro ⟨hc, hs, hn⟩
            exact BetaFreeContext.recurBase hc hs hn
          · intro h
            cases h with
            | recurBase hc hs hn => exact ⟨hc, hs, hn⟩
  | recurStep b c n ih =>
      calc
        betaFreeContext? (.recurStep b c n) = true ↔
            betaFree? b = true ∧ betaFreeContext? c = true ∧ betaFree? n = true := by
          simp [betaFreeContext?, Bool.and_eq_true, and_assoc]
        _ ↔ BetaFreeHOTerm b ∧ BetaFreeContext c ∧ BetaFreeHOTerm n := by
          simp [ih, betaFree_classifier_eq_true_iff]
        _ ↔ BetaFreeContext (.recurStep b c n) := by
          constructor
          · rintro ⟨hb, hc, hn⟩
            exact BetaFreeContext.recurStep hb hc hn
          · intro h
            cases h with
            | recurStep hb hc hn => exact ⟨hb, hc, hn⟩
  | recurArg b s c ih =>
      calc
        betaFreeContext? (.recurArg b s c) = true ↔
            betaFree? b = true ∧ betaFree? s = true ∧ betaFreeContext? c = true := by
          simp [betaFreeContext?, Bool.and_eq_true, and_assoc]
        _ ↔ BetaFreeHOTerm b ∧ BetaFreeHOTerm s ∧ BetaFreeContext c := by
          simp [ih, betaFree_classifier_eq_true_iff]
        _ ↔ BetaFreeContext (.recurArg b s c) := by
          constructor
          · rintro ⟨hb, hs, hc⟩
            exact BetaFreeContext.recurArg hb hs hc
          · intro h
            cases h with
            | recurArg hb hs hc => exact ⟨hb, hs, hc⟩
  | shareLeft c r ih =>
      calc
        betaFreeContext? (.shareLeft c r) = true ↔
            betaFreeContext? c = true ∧ betaFree? r = true := by
          simp [betaFreeContext?, Bool.and_eq_true]
        _ ↔ BetaFreeContext c ∧ BetaFreeHOTerm r := by
          simp [ih, betaFree_classifier_eq_true_iff]
        _ ↔ BetaFreeContext (.shareLeft c r) := by
          constructor
          · rintro ⟨hc, hr⟩
            exact BetaFreeContext.shareLeft hc hr
          · intro h
            cases h with
            | shareLeft hc hr => exact ⟨hc, hr⟩
  | shareRight s c ih =>
      calc
        betaFreeContext? (.shareRight s c) = true ↔
            betaFree? s = true ∧ betaFreeContext? c = true := by
          simp [betaFreeContext?, Bool.and_eq_true]
        _ ↔ BetaFreeHOTerm s ∧ BetaFreeContext c := by
          simp [ih, betaFree_classifier_eq_true_iff]
        _ ↔ BetaFreeContext (.shareRight s c) := by
          constructor
          · rintro ⟨hs, hc⟩
            exact BetaFreeContext.shareRight hs hc
          · intro h
            cases h with
            | shareRight hs hc => exact ⟨hs, hc⟩

private def decidable_from_classifier
    (b : Bool) {p : Prop} (hiff : b = true ↔ p) : Decidable p := by
  by_cases hb : b = true
  · exact isTrue (hiff.mp hb)
  · exact isFalse (fun hp => hb (hiff.mpr hp))

instance decidableIsLam (t : HOTerm) : Decidable (IsLam t) :=
  decidable_from_classifier (isLam t) isLam_classifier_eq_true_iff

instance decidableBinderFreeHOTerm (t : HOTerm) : Decidable (BinderFreeHOTerm t) :=
  decidable_from_classifier (binderFree? t) binderFree_classifier_eq_true_iff

instance decidableShareFreeHOTerm (t : HOTerm) : Decidable (ShareFreeHOTerm t) :=
  decidable_from_classifier (shareFree? t) shareFree_classifier_eq_true_iff

instance decidableBetaFreeHOTerm (t : HOTerm) : Decidable (BetaFreeHOTerm t) :=
  decidable_from_classifier (betaFree? t) betaFree_classifier_eq_true_iff

instance decidableLinearHOTerm (t : HOTerm) : Decidable (LinearHOTerm t) :=
  decidable_from_classifier (linear? t) linear_classifier_eq_true_iff

instance decidableDAGSharedHOTerm (t : HOTerm) : Decidable (DAGSharedHOTerm t) :=
  decidable_from_classifier (dagShared? t) dagShared_classifier_eq_true_iff

instance decidableBinderFreeContext (c : Context) : Decidable (BinderFreeContext c) :=
  decidable_from_classifier (binderFreeContext? c) binderFreeContext_classifier_eq_true_iff

instance decidableBetaFreeContext (c : Context) : Decidable (BetaFreeContext c) :=
  decidable_from_classifier (betaFreeContext? c) betaFreeContext_classifier_eq_true_iff

/-- Closed fragments satisfy the executable beta-free classifier. -/
theorem closedFragment_implies_betaFree_classifier_true
    {t : HOTerm} (h : ClosedFragment t) :
    betaFree? t = true :=
  betaFree_classifier_eq_true_iff.mpr (closedFragment_betaFree h)

/-- Closed fragments satisfy the executable binder-free classifier. -/
theorem closedFragment_implies_binderFree_classifier_true
    {t : HOTerm} (h : ClosedFragment t) :
    binderFree? t = true :=
  binderFree_classifier_eq_true_iff.mpr (closedFragment_binderFree h)

/-- Share-free closed fragments satisfy the executable linear classifier. -/
theorem shareFree_closedFragment_implies_linear_classifier_true
    {t : HOTerm} (hClosed : ClosedFragment t) (hShare : ShareFreeHOTerm t) :
    linear? t = true :=
  linear_classifier_eq_true_iff.mpr (shareFree_closedFragment_linear hClosed hShare)

/-- Embedded shared terms satisfy the executable DAG/shared classifier. -/
theorem embedSharedTerm_implies_dagShared_classifier_true
    (t : SharedTerm) :
    dagShared? (embedSharedTerm t) = true :=
  dagShared_classifier_eq_true_iff.mpr (embedSharedTerm_dagShared t)

/-- A true binder-free context classifier recovers the plug-preservation theorem. -/
theorem binderFreeContext_classifier_true_implies_plug_preserves_binderFree
    {c : Context} {t : HOTerm}
    (hc : binderFreeContext? c = true) (ht : BinderFreeHOTerm t) :
    BinderFreeHOTerm (Context.plug c t) :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.BinderFreeContext.plug_binderFree
    (binderFreeContext_classifier_eq_true_iff.mp hc) ht

/-- A true beta-free context classifier recovers the plug-preservation theorem. -/
theorem betaFreeContext_classifier_true_implies_plug_preserves_betaFree
    {c : Context} {t : HOTerm}
    (hc : betaFreeContext? c = true) (ht : BetaFreeHOTerm t) :
    BetaFreeHOTerm (Context.plug c t) :=
  OperatorKO7.HigherOrderRewritingCaptureSubfamilies.BetaFreeContext.plug_betaFree
    (betaFreeContext_classifier_eq_true_iff.mp hc) ht

/-- Catalog for the executable higher-order classifiers and their Prop
bridges. -/
structure HigherOrderDecidableClassifierCatalog : Prop where
  isLamClassifierIff : ∀ {t : HOTerm}, isLam t = true ↔ IsLam t
  binderFreeClassifierIff : ∀ {t : HOTerm}, binderFree? t = true ↔ BinderFreeHOTerm t
  shareFreeClassifierIff : ∀ {t : HOTerm}, shareFree? t = true ↔ ShareFreeHOTerm t
  betaFreeClassifierIff : ∀ {t : HOTerm}, betaFree? t = true ↔ BetaFreeHOTerm t
  linearClassifierIff : ∀ {t : HOTerm}, linear? t = true ↔ LinearHOTerm t
  dagSharedClassifierIff : ∀ {t : HOTerm}, dagShared? t = true ↔ DAGSharedHOTerm t
  binderFreeContextClassifierIff :
    ∀ {c : Context}, binderFreeContext? c = true ↔ BinderFreeContext c
  betaFreeContextClassifierIff :
    ∀ {c : Context}, betaFreeContext? c = true ↔ BetaFreeContext c
  closedFragmentImpliesBetaFreeClassifierTrue :
    ∀ {t : HOTerm}, ClosedFragment t → betaFree? t = true
  closedFragmentImpliesBinderFreeClassifierTrue :
    ∀ {t : HOTerm}, ClosedFragment t → binderFree? t = true
  shareFreeClosedFragmentImpliesLinearClassifierTrue :
    ∀ {t : HOTerm}, ClosedFragment t → ShareFreeHOTerm t → linear? t = true
  embedSharedTermImpliesDagSharedClassifierTrue :
    ∀ t : SharedTerm, dagShared? (embedSharedTerm t) = true
  binderFreeContextClassifierTrueImpliesPlugPreservesBinderFree :
    ∀ {c : Context} {t : HOTerm},
      binderFreeContext? c = true → BinderFreeHOTerm t → BinderFreeHOTerm (Context.plug c t)
  betaFreeContextClassifierTrueImpliesPlugPreservesBetaFree :
    ∀ {c : Context} {t : HOTerm},
      betaFreeContext? c = true → BetaFreeHOTerm t → BetaFreeHOTerm (Context.plug c t)

/-- Canonical catalog value for the executable higher-order classifiers. -/
theorem higher_order_decidable_classifier_catalog :
    HigherOrderDecidableClassifierCatalog := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact isLam_classifier_eq_true_iff
  · intro t
    exact binderFree_classifier_eq_true_iff
  · intro t
    exact shareFree_classifier_eq_true_iff
  · intro t
    exact betaFree_classifier_eq_true_iff
  · intro t
    exact linear_classifier_eq_true_iff
  · intro t
    exact dagShared_classifier_eq_true_iff
  · intro c
    exact binderFreeContext_classifier_eq_true_iff
  · intro c
    exact betaFreeContext_classifier_eq_true_iff
  · intro t h
    exact closedFragment_implies_betaFree_classifier_true h
  · intro t h
    exact closedFragment_implies_binderFree_classifier_true h
  · intro t hClosed hShare
    exact shareFree_closedFragment_implies_linear_classifier_true hClosed hShare
  · intro t
    exact embedSharedTerm_implies_dagShared_classifier_true t
  · intro c t hc ht
    exact binderFreeContext_classifier_true_implies_plug_preserves_binderFree hc ht
  · intro c t hc ht
    exact betaFreeContext_classifier_true_implies_plug_preserves_betaFree hc ht

end OperatorKO7.HigherOrderRewritingDecidableClassifiers
