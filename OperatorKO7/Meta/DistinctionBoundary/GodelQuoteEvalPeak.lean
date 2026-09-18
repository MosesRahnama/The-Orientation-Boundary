import OperatorKO7.Meta.DistinctionBoundary.GodelPartial
import OperatorKO7.Meta.DistinctionBoundary.GodelPartialClosure

set_option autoImplicit false
set_option maxHeartbeats 400000

/-!
# Quote/eval peak and least freeze including quote congruence (ROADMAP-12 §10.1.2)

`BehaviorJoinAt` is explicit nonjoinability of the two quotations at the
kernel R5 pair. Quote/eval configurations close source reduction under
quotation together with evaluation. The two-reduction peak demanded by
manuscript `prob:freeze` does not join. The kernel `{eqW}` freeze does not
remove that peak. The least freeze of the extended relation includes the
quote-congruence rule.

NameGate: no `goedel_first`, no `incompleteness`, no `feferman_completeness`.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelPartial

open OperatorKO7
open OperatorKO7.EqGuardedConfluence
open OperatorKO7.Meta.DistinctionBoundary.FreezeSetForced

def BehaviorJoinAt (c d : PartialCode) (x : Trace) : Prop :=
  ∃ v, convergesTo c x v ∧ convergesTo d x v

theorem quote_merge_void_void_converges :
    convergesTo (quote (Trace.merge Trace.void Trace.void)) Trace.void
      Trace.void :=
  ⟨1, rfl⟩

theorem quote_void_diverges_at_void :
    diverges (quote Trace.void) Trace.void :=
  diverges_diverge Trace.void

theorem quote_diverge_blocks_join {c : PartialCode} {x v : Trace}
    (h : diverges c x) : ¬ convergesTo c x v := by
  rintro ⟨n, hn⟩
  have := h n
  rw [this] at hn
  cases hn

theorem not_BehaviorJoinAt_quote_R5 :
    ¬ BehaviorJoinAt (quote (Trace.merge Trace.void Trace.void))
        (quote Trace.void) Trace.void := by
  rintro ⟨v, hc, hd⟩
  exact quote_diverge_blocks_join quote_void_diverges_at_void hd

inductive QuoteEvalCfg : Type
  | evalQuoted : Trace → Trace → QuoteEvalCfg
  | value : Trace → QuoteEvalCfg
  | diverged : QuoteEvalCfg
deriving DecidableEq, Repr

/-- Extended reduction: source steps under quotation (`underQuote`) together
with evaluation of the quoted code. `allowQuoteCong` is the quote-congruence
slot, not a kernel `Ctor`. -/
inductive QuoteEvalStep (allowQuoteCong : Bool) :
    QuoteEvalCfg → QuoteEvalCfg → Prop
  | underQuote {t u y : Trace} (henabled : allowQuoteCong = true)
      (h : EqGuardedStep t u) :
      QuoteEvalStep allowQuoteCong (.evalQuoted t y) (.evalQuoted u y)
  | evalConverge {t y v : Trace} (h : convergesTo (quote t) y v) :
      QuoteEvalStep allowQuoteCong (.evalQuoted t y) (.value v)
  | evalDiverge {t y : Trace} (h : diverges (quote t) y) :
      QuoteEvalStep allowQuoteCong (.evalQuoted t y) .diverged

inductive QuoteEvalStar (allowQuoteCong : Bool) :
    QuoteEvalCfg → QuoteEvalCfg → Prop
  | refl (a : QuoteEvalCfg) : QuoteEvalStar allowQuoteCong a a
  | tail {a b c : QuoteEvalCfg} :
      QuoteEvalStep allowQuoteCong a b →
        QuoteEvalStar allowQuoteCong b c →
        QuoteEvalStar allowQuoteCong a c

def QuoteEvalJoin (allowQuoteCong : Bool) (b c : QuoteEvalCfg) : Prop :=
  ∃ d, QuoteEvalStar allowQuoteCong b d ∧ QuoteEvalStar allowQuoteCong c d

def freezePeakSource : QuoteEvalCfg :=
  .evalQuoted (Trace.merge Trace.void Trace.void) Trace.void

theorem freeze_peak_eval_converge :
    QuoteEvalStep true freezePeakSource (.value Trace.void) :=
  QuoteEvalStep.evalConverge quote_merge_void_void_converges

theorem freeze_peak_under_quote :
    QuoteEvalStep true freezePeakSource
      (.evalQuoted Trace.void Trace.void) :=
  QuoteEvalStep.underQuote rfl (EqGuardedStep.R_merge_void_left Trace.void)

theorem freeze_peak_eval_diverge :
    QuoteEvalStep true (.evalQuoted Trace.void Trace.void) .diverged :=
  QuoteEvalStep.evalDiverge quote_void_diverges_at_void

theorem freeze_peak_two_reductions :
    QuoteEvalStep true freezePeakSource (.value Trace.void) ∧
      QuoteEvalStar true freezePeakSource .diverged :=
  ⟨freeze_peak_eval_converge,
    QuoteEvalStar.tail freeze_peak_under_quote
      (QuoteEvalStar.tail freeze_peak_eval_diverge (QuoteEvalStar.refl _))⟩

theorem value_ne_diverged (v : Trace) :
    QuoteEvalCfg.value v ≠ .diverged := by
  intro h
  cases h

theorem no_step_from_value {allow : Bool} {v : Trace} {c : QuoteEvalCfg} :
    ¬ QuoteEvalStep allow (.value v) c := by
  intro h
  cases h

theorem no_step_from_diverged {allow : Bool} {c : QuoteEvalCfg} :
    ¬ QuoteEvalStep allow .diverged c := by
  intro h
  cases h

theorem star_from_value {allow : Bool} {v : Trace} {c : QuoteEvalCfg}
    (h : QuoteEvalStar allow (.value v) c) : c = .value v := by
  cases h with
  | refl => rfl
  | tail hstep _ => exact (no_step_from_value hstep).elim

theorem star_from_diverged {allow : Bool} {c : QuoteEvalCfg}
    (h : QuoteEvalStar allow .diverged c) : c = .diverged := by
  cases h with
  | refl => rfl
  | tail hstep _ => exact (no_step_from_diverged hstep).elim

theorem freeze_peak_does_not_join :
    ¬ QuoteEvalJoin true (.value Trace.void) .diverged := by
  rintro ⟨d, hd1, hd2⟩
  have h1 := star_from_value hd1
  have h2 := star_from_diverged hd2
  exact value_ne_diverged Trace.void (h1.symm.trans h2)

/-- Manuscript `prob:freeze`: the quoted R5 redex has two reductions that
do not join. -/
theorem quote_eval_nonjoinable_peak :
    QuoteEvalStep true freezePeakSource (.value Trace.void) ∧
      QuoteEvalStar true freezePeakSource .diverged ∧
      ¬ QuoteEvalJoin true (.value Trace.void) .diverged :=
  ⟨freeze_peak_eval_converge, freeze_peak_two_reductions.2,
    freeze_peak_does_not_join⟩

theorem freeze_peak_eval_converge_frozen :
    QuoteEvalStep false freezePeakSource (.value Trace.void) :=
  QuoteEvalStep.evalConverge quote_merge_void_void_converges

theorem no_underQuote_when_frozen {t u y : Trace} :
    ¬ QuoteEvalStep false (.evalQuoted t y) (.evalQuoted u y) := by
  intro h
  cases h with
  | underQuote henabled _ => cases henabled

/-- Freezing quote congruence removes the under-quote arm of the peak. -/
theorem quote_congruence_freeze_kills_underQuote_arm :
    QuoteEvalStep false freezePeakSource (.value Trace.void) ∧
      ¬ QuoteEvalStep false freezePeakSource
        (.evalQuoted Trace.void Trace.void) :=
  ⟨freeze_peak_eval_converge_frozen, no_underQuote_when_frozen⟩

theorem eqW_kernel_freeze_does_not_remove_quote_peak :
    ConfluentOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep ∧
      EqGuardedStep (Trace.merge Trace.void Trace.void) Trace.void ∧
      ¬ BehaviorJoinAt (quote (Trace.merge Trace.void Trace.void))
          (quote Trace.void) Trace.void :=
  ⟨fullMinusEqW_confluent, EqGuardedStep.R_merge_void_left Trace.void,
    not_BehaviorJoinAt_quote_R5⟩

/-! ## Extended critical pairs: quote of each kernel redex vs contractum -/

def QuotePairJoins (t u : Trace) : Prop :=
  BehaviorJoinAt (quote t) (quote u) Trace.void ∨
    (diverges (quote t) Trace.void ∧ diverges (quote u) Trace.void)

theorem quote_integrate_eq_diverge (t : Trace) :
    quote (Trace.integrate t) = .diverge :=
  rfl

theorem quote_eqW_eq_diverge (a b : Trace) :
    quote (Trace.eqW a b) = .diverge :=
  rfl

theorem quote_rec_eq_diverge (b s n : Trace) :
    quote (Trace.recΔ b s n) = .diverge :=
  rfl

theorem pair_both_diverge (t u : Trace)
    (ht : quote t = .diverge) (hu : quote u = .diverge) :
    QuotePairJoins t u :=
  Or.inr ⟨ht ▸ diverges_diverge Trace.void, hu ▸ diverges_diverge Trace.void⟩

inductive QuoteCriticalPair : Type
  | intDelta
  | mergeVoidLeft
  | mergeVoidRight
  | mergeCancel
  | recZero
  | recSucc
  | eqRefl
  | eqDiff
deriving DecidableEq, Repr

def QuoteCriticalPair.source : QuoteCriticalPair → Trace
  | .intDelta => Trace.integrate (Trace.delta Trace.void)
  | .mergeVoidLeft => Trace.merge Trace.void Trace.void
  | .mergeVoidRight => Trace.merge Trace.void Trace.void
  | .mergeCancel => Trace.merge Trace.void Trace.void
  | .recZero => Trace.recΔ Trace.void Trace.void Trace.void
  | .recSucc => Trace.recΔ Trace.void Trace.void (Trace.delta Trace.void)
  | .eqRefl => Trace.eqW Trace.void Trace.void
  | .eqDiff => Trace.eqW Trace.void (Trace.delta Trace.void)

def QuoteCriticalPair.target : QuoteCriticalPair → Trace
  | .intDelta => Trace.void
  | .mergeVoidLeft => Trace.void
  | .mergeVoidRight => Trace.void
  | .mergeCancel => Trace.void
  | .recZero => Trace.void
  | .recSucc => Trace.app Trace.void (Trace.recΔ Trace.void Trace.void Trace.void)
  | .eqRefl => Trace.void
  | .eqDiff => Trace.integrate (Trace.merge Trace.void (Trace.delta Trace.void))

def QuoteCriticalPair.kernelStep : QuoteCriticalPair → Prop
  | .intDelta => EqGuardedStep (Trace.integrate (Trace.delta Trace.void)) Trace.void
  | .mergeVoidLeft =>
      EqGuardedStep (Trace.merge Trace.void Trace.void) Trace.void
  | .mergeVoidRight =>
      EqGuardedStep (Trace.merge Trace.void Trace.void) Trace.void
  | .mergeCancel =>
      EqGuardedStep (Trace.merge Trace.void Trace.void) Trace.void
  | .recZero =>
      EqGuardedStep (Trace.recΔ Trace.void Trace.void Trace.void) Trace.void
  | .recSucc =>
      EqGuardedStep
        (Trace.recΔ Trace.void Trace.void (Trace.delta Trace.void))
        (Trace.app Trace.void (Trace.recΔ Trace.void Trace.void Trace.void))
  | .eqRefl => EqGuardedStep (Trace.eqW Trace.void Trace.void) Trace.void
  | .eqDiff =>
      EqGuardedStep (Trace.eqW Trace.void (Trace.delta Trace.void))
        (Trace.integrate (Trace.merge Trace.void (Trace.delta Trace.void)))

theorem QuoteCriticalPair.kernelStep_holds (p : QuoteCriticalPair) :
    p.kernelStep := by
  cases p with
  | intDelta => exact EqGuardedStep.R_int_delta Trace.void
  | mergeVoidLeft => exact EqGuardedStep.R_merge_void_left Trace.void
  | mergeVoidRight => exact EqGuardedStep.R_merge_void_right Trace.void
  | mergeCancel => exact EqGuardedStep.R_merge_cancel Trace.void
  | recZero => exact EqGuardedStep.R_rec_zero Trace.void Trace.void
  | recSucc =>
      exact EqGuardedStep.R_rec_succ Trace.void Trace.void Trace.void
  | eqRefl => exact EqGuardedStep.R_eq_refl Trace.void
  | eqDiff =>
      exact EqGuardedStep.R_eq_diff Trace.void (Trace.delta Trace.void)
        (fun h => Trace.noConfusion h)

def QuoteCriticalPair.quoteJoins : QuoteCriticalPair → Prop
  | .mergeVoidLeft => False
  | .mergeVoidRight => False
  | .mergeCancel => False
  | .intDelta => True
  | .recZero => True
  | .recSucc => True
  | .eqRefl => True
  | .eqDiff => True

theorem quote_app_void_rec_eq_diverge :
    quote (Trace.app Trace.void
        (Trace.recΔ Trace.void Trace.void Trace.void)) = .diverge :=
  rfl

theorem QuoteCriticalPair.quoteJoins_correct (p : QuoteCriticalPair) :
    p.quoteJoins ↔ QuotePairJoins p.source p.target := by
  cases p with
  | mergeVoidLeft =>
    constructor
    · intro h
      exact False.elim h
    · intro h
      cases h with
      | inl hj => exact (not_BehaviorJoinAt_quote_R5 hj).elim
      | inr hd =>
        exact quote_diverge_blocks_join hd.1 quote_merge_void_void_converges
  | mergeVoidRight =>
    constructor
    · intro h
      exact False.elim h
    · intro h
      cases h with
      | inl hj => exact (not_BehaviorJoinAt_quote_R5 hj).elim
      | inr hd =>
        exact quote_diverge_blocks_join hd.1 quote_merge_void_void_converges
  | mergeCancel =>
    constructor
    · intro h
      exact False.elim h
    · intro h
      cases h with
      | inl hj => exact (not_BehaviorJoinAt_quote_R5 hj).elim
      | inr hd =>
        exact quote_diverge_blocks_join hd.1 quote_merge_void_void_converges
  | intDelta =>
    constructor
    · intro _
      exact pair_both_diverge _ _ rfl quote_void_eq_diverge
    · intro _
      trivial
  | recZero =>
    constructor
    · intro _
      exact pair_both_diverge _ _ rfl quote_void_eq_diverge
    · intro _
      trivial
  | recSucc =>
    constructor
    · intro _
      exact pair_both_diverge _ _ rfl quote_app_void_rec_eq_diverge
    · intro _
      trivial
  | eqRefl =>
    constructor
    · intro _
      exact pair_both_diverge _ _ rfl quote_void_eq_diverge
    · intro _
      trivial
  | eqDiff =>
    constructor
    · intro _
      exact pair_both_diverge _ _
        (quote_eqW_eq_diverge Trace.void (Trace.delta Trace.void))
        (quote_integrate_eq_diverge _)
    · intro _
      trivial

/-- Least freeze of the extended relation: quote congruence must be frozen.
The kernel `{eqW}` freeze is not enough. -/
theorem least_freeze_includes_quote_congruence :
    ¬ QuoteEvalJoin true (.value Trace.void) .diverged ∧
      QuoteEvalStep false freezePeakSource (.value Trace.void) ∧
      ¬ QuoteEvalStep false freezePeakSource
        (.evalQuoted Trace.void Trace.void) ∧
      ConfluentOn (fun c : Ctor => c ≠ Ctor.eqW) EqGuardedStep ∧
      ¬ BehaviorJoinAt (quote (Trace.merge Trace.void Trace.void))
          (quote Trace.void) Trace.void :=
  ⟨freeze_peak_does_not_join, freeze_peak_eval_converge_frozen,
    no_underQuote_when_frozen, fullMinusEqW_confluent,
    not_BehaviorJoinAt_quote_R5⟩

end OperatorKO7.Meta.DistinctionBoundary.GodelPartial
