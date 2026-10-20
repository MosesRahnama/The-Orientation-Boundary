import OperatorKO7.Meta.ContextClosed_SN_Full

set_option autoImplicit false

/-!
# Rule-derived termination of the full contextual KO7 relation

A second machine-checked proof of `thm:full-context-closed-sn` of the Orientation Boundary paper
(ledger row 03-011), beside the polynomial-interpretation proof `MetaSN_KO7.wf_StepCtxFullRev_poly`.
This proof uses no interpretation, weight or ordering parameter. Termination is closed under every
constructor; the relation "reduct or immediate subterm" is well founded below every terminating term;
and `recΔ b s n` terminates by induction along that relation on the counter `n`. At the duplicating
rule `R_rec_succ` the only comparison used is the dependency-pair comparison of `n` against
`delta n`. The rules `R_eq_diff` and `R_merge_*` are handled by the closure lemmas for `integrate`
and `merge`.

Relation: `MetaSN_KO7.StepCtxFull` (the eight root rules of `Step` at every position).
Closure: the reverse relation `StepCtxFullRev`, accessibility of every trace.
Property: termination. Trust: kernel-only. No `sorry`, `admit`, `axiom`, `native_decide`.
-/

namespace OperatorKO7.Meta.BoundaryObserver.ContextRuleDerivedSN

open OperatorKO7 Trace
open MetaSN_KO7

/-- Termination of a trace under the full contextual relation: accessibility in its reverse. -/
def SNCtx (t : Trace) : Prop := Acc StepCtxFullRev t

/-- Unfolding lemma of `SNCtx`. -/
theorem snCtx_iff (t : Trace) : SNCtx t ↔ Acc StepCtxFullRev t := Iff.rfl

/-- The immediate subterm relation on `Trace`. -/
inductive ImmSub : Trace → Trace → Prop
  | delta (t : Trace) : ImmSub t (delta t)
  | integrate (t : Trace) : ImmSub t (integrate t)
  | mergeLeft (a b : Trace) : ImmSub a (merge a b)
  | mergeRight (a b : Trace) : ImmSub b (merge a b)
  | appLeft (a b : Trace) : ImmSub a (app a b)
  | appRight (a b : Trace) : ImmSub b (app a b)
  | recBase (b s n : Trace) : ImmSub b (recΔ b s n)
  | recStep (b s n : Trace) : ImmSub s (recΔ b s n)
  | recCounter (b s n : Trace) : ImmSub n (recΔ b s n)
  | eqLeft (a b : Trace) : ImmSub a (eqW a b)
  | eqRight (a b : Trace) : ImmSub b (eqW a b)

/-- Descent: a contextual reduct or an immediate subterm. -/
def Descent : Trace → Trace → Prop := fun a t => StepCtxFull t a ∨ ImmSub a t

/-- Unfolding lemma of `Descent`. -/
theorem descent_iff (a t : Trace) : Descent a t ↔ StepCtxFull t a ∨ ImmSub a t := Iff.rfl

/-! ## Termination passes down through contexts -/

theorem snCtx_of_congr (C : Trace → Trace)
    (hC : ∀ {u u' : Trace}, StepCtxFull u u' → StepCtxFull (C u) (C u')) :
    ∀ {w : Trace}, SNCtx w → ∀ u, w = C u → SNCtx u := by
  intro w hw
  induction hw with
  | intro w _ ih =>
      intro u hu
      subst hu
      constructor
      intro u' hu'
      exact ih (C u') (hC hu') u' rfl

theorem snCtx_imm_sub {t a : Trace} (ht : SNCtx t) (h : ImmSub a t) : SNCtx a :=
  match h with
  | .delta t' => snCtx_of_congr (fun w => delta w) (fun hs => StepCtxFull.delta hs) ht t' rfl
  | .integrate t' =>
      snCtx_of_congr (fun w => integrate w) (fun hs => StepCtxFull.integrate hs) ht t' rfl
  | .mergeLeft a' b' =>
      snCtx_of_congr (fun w => merge w b') (fun hs => StepCtxFull.mergeL hs) ht a' rfl
  | .mergeRight a' b' =>
      snCtx_of_congr (fun w => merge a' w) (fun hs => StepCtxFull.mergeR hs) ht b' rfl
  | .appLeft a' b' =>
      snCtx_of_congr (fun w => app w b') (fun hs => StepCtxFull.appL hs) ht a' rfl
  | .appRight a' b' =>
      snCtx_of_congr (fun w => app a' w) (fun hs => StepCtxFull.appR hs) ht b' rfl
  | .recBase b' s' n' =>
      snCtx_of_congr (fun w => recΔ w s' n') (fun hs => StepCtxFull.recB hs) ht b' rfl
  | .recStep b' s' n' =>
      snCtx_of_congr (fun w => recΔ b' w n') (fun hs => StepCtxFull.recS hs) ht s' rfl
  | .recCounter b' s' n' =>
      snCtx_of_congr (fun w => recΔ b' s' w) (fun hs => StepCtxFull.recN hs) ht n' rfl
  | .eqLeft a' b' =>
      snCtx_of_congr (fun w => eqW w b') (fun hs => StepCtxFull.eqWL hs) ht a' rfl
  | .eqRight a' b' =>
      snCtx_of_congr (fun w => eqW a' w) (fun hs => StepCtxFull.eqWR hs) ht b' rfl

/-! ## Termination builds up through the constructors -/

theorem snCtx_void : SNCtx void := by
  constructor
  intro u hu
  change StepCtxFull void u at hu
  cases hu with
  | root hr => cases hr

theorem snCtx_delta {t : Trace} (ht : SNCtx t) : SNCtx (delta t) := by
  induction ht with
  | intro t _ ih =>
      constructor
      intro u hu
      change StepCtxFull (delta t) u at hu
      cases hu with
      | root hr => cases hr
      | delta hs => exact ih _ hs

/-- Root reducts of `integrate t`: only `R_int_delta`, to `void`. -/
theorem snCtx_of_root_integrate {t u : Trace} (h : Step (integrate t) u) : SNCtx u := by
  cases h with
  | R_int_delta => exact snCtx_void

theorem snCtx_integrate {t : Trace} (ht : SNCtx t) : SNCtx (integrate t) := by
  induction ht with
  | intro t _ ih =>
      constructor
      intro u hu
      change StepCtxFull (integrate t) u at hu
      cases hu with
      | root hr => exact snCtx_of_root_integrate hr
      | integrate hs => exact ih _ hs

/-- Root reducts of `merge a b` are `a`, `b`, or the shared term. -/
theorem snCtx_of_root_merge {a b u : Trace} (ha : SNCtx a) (hb : SNCtx b)
    (h : Step (merge a b) u) : SNCtx u := by
  cases h with
  | R_merge_void_left => exact hb
  | R_merge_void_right => exact ha
  | R_merge_cancel => exact ha

theorem snCtx_merge_aux {a : Trace} (ha : SNCtx a) :
    ∀ b : Trace, SNCtx b → SNCtx (merge a b) := by
  induction ha with
  | intro a ha' iha =>
      intro b hb
      induction hb with
      | intro b hb' ihb =>
          constructor
          intro u hu
          change StepCtxFull (merge a b) u at hu
          cases hu with
          | root hr => exact snCtx_of_root_merge (Acc.intro a ha') (Acc.intro b hb') hr
          | mergeL hs => exact iha _ hs b (Acc.intro b hb')
          | mergeR hs => exact ihb _ hs

theorem snCtx_merge {a b : Trace} (ha : SNCtx a) (hb : SNCtx b) : SNCtx (merge a b) :=
  snCtx_merge_aux ha b hb

theorem snCtx_app_aux {a : Trace} (ha : SNCtx a) : ∀ b : Trace, SNCtx b → SNCtx (app a b) := by
  induction ha with
  | intro a _ iha =>
      intro b hb
      induction hb with
      | intro b hb' ihb =>
          constructor
          intro u hu
          change StepCtxFull (app a b) u at hu
          cases hu with
          | root hr => cases hr
          | appL hs => exact iha _ hs b (Acc.intro b hb')
          | appR hs => exact ihb _ hs

theorem snCtx_app {a b : Trace} (ha : SNCtx a) (hb : SNCtx b) : SNCtx (app a b) :=
  snCtx_app_aux ha b hb

/-- Root reducts of `eqW a b`: `void` or `integrate (merge a b)`. -/
theorem snCtx_of_root_eqW {a b u : Trace} (ha : SNCtx a) (hb : SNCtx b)
    (h : Step (eqW a b) u) : SNCtx u := by
  cases h with
  | R_eq_refl => exact snCtx_void
  | R_eq_diff => exact snCtx_integrate (snCtx_merge ha hb)

theorem snCtx_eqW_aux {a : Trace} (ha : SNCtx a) : ∀ b : Trace, SNCtx b → SNCtx (eqW a b) := by
  induction ha with
  | intro a ha' iha =>
      intro b hb
      induction hb with
      | intro b hb' ihb =>
          constructor
          intro u hu
          change StepCtxFull (eqW a b) u at hu
          cases hu with
          | root hr => exact snCtx_of_root_eqW (Acc.intro a ha') (Acc.intro b hb') hr
          | eqWL hs => exact iha _ hs b (Acc.intro b hb')
          | eqWR hs => exact ihb _ hs

theorem snCtx_eqW {a b : Trace} (ha : SNCtx a) (hb : SNCtx b) : SNCtx (eqW a b) :=
  snCtx_eqW_aux ha b hb

/-! ## The descent relation is well founded below terminating terms -/

theorem acc_descent_aux :
    ∀ t : Trace, SNCtx t → (∀ a, StepCtxFull t a → Acc Descent a) → Acc Descent t := by
  intro t
  induction t with
  | void =>
      intro _ H
      constructor
      intro a ha
      rcases ha with hstep | hsub
      · exact H a hstep
      · cases hsub
  | delta t iht =>
      intro hsn H
      constructor
      intro a ha
      rcases ha with hstep | hsub
      · exact H a hstep
      · cases hsub with
        | delta =>
            apply iht (snCtx_imm_sub hsn (ImmSub.delta t))
            intro a' ha'
            exact Acc.inv (H (delta a') (StepCtxFull.delta ha')) (Or.inr (ImmSub.delta a'))
  | integrate t iht =>
      intro hsn H
      constructor
      intro a ha
      rcases ha with hstep | hsub
      · exact H a hstep
      · cases hsub with
        | integrate =>
            apply iht (snCtx_imm_sub hsn (ImmSub.integrate t))
            intro a' ha'
            exact Acc.inv (H (integrate a') (StepCtxFull.integrate ha'))
              (Or.inr (ImmSub.integrate a'))
  | merge a b iha ihb =>
      intro hsn H
      constructor
      intro c hc
      rcases hc with hstep | hsub
      · exact H c hstep
      · cases hsub with
        | mergeLeft =>
            apply iha (snCtx_imm_sub hsn (ImmSub.mergeLeft a b))
            intro a' ha'
            exact Acc.inv (H (merge a' b) (StepCtxFull.mergeL ha'))
              (Or.inr (ImmSub.mergeLeft a' b))
        | mergeRight =>
            apply ihb (snCtx_imm_sub hsn (ImmSub.mergeRight a b))
            intro b' hb'
            exact Acc.inv (H (merge a b') (StepCtxFull.mergeR hb'))
              (Or.inr (ImmSub.mergeRight a b'))
  | app a b iha ihb =>
      intro hsn H
      constructor
      intro c hc
      rcases hc with hstep | hsub
      · exact H c hstep
      · cases hsub with
        | appLeft =>
            apply iha (snCtx_imm_sub hsn (ImmSub.appLeft a b))
            intro a' ha'
            exact Acc.inv (H (app a' b) (StepCtxFull.appL ha'))
              (Or.inr (ImmSub.appLeft a' b))
        | appRight =>
            apply ihb (snCtx_imm_sub hsn (ImmSub.appRight a b))
            intro b' hb'
            exact Acc.inv (H (app a b') (StepCtxFull.appR hb'))
              (Or.inr (ImmSub.appRight a b'))
  | recΔ b s n ihb ihs ihn =>
      intro hsn H
      constructor
      intro c hc
      rcases hc with hstep | hsub
      · exact H c hstep
      · cases hsub with
        | recBase =>
            apply ihb (snCtx_imm_sub hsn (ImmSub.recBase b s n))
            intro b' hb'
            exact Acc.inv (H (recΔ b' s n) (StepCtxFull.recB hb'))
              (Or.inr (ImmSub.recBase b' s n))
        | recStep =>
            apply ihs (snCtx_imm_sub hsn (ImmSub.recStep b s n))
            intro s' hs'
            exact Acc.inv (H (recΔ b s' n) (StepCtxFull.recS hs'))
              (Or.inr (ImmSub.recStep b s' n))
        | recCounter =>
            apply ihn (snCtx_imm_sub hsn (ImmSub.recCounter b s n))
            intro n' hn'
            exact Acc.inv (H (recΔ b s n') (StepCtxFull.recN hn'))
              (Or.inr (ImmSub.recCounter b s n'))
  | eqW a b iha ihb =>
      intro hsn H
      constructor
      intro c hc
      rcases hc with hstep | hsub
      · exact H c hstep
      · cases hsub with
        | eqLeft =>
            apply iha (snCtx_imm_sub hsn (ImmSub.eqLeft a b))
            intro a' ha'
            exact Acc.inv (H (eqW a' b) (StepCtxFull.eqWL ha'))
              (Or.inr (ImmSub.eqLeft a' b))
        | eqRight =>
            apply ihb (snCtx_imm_sub hsn (ImmSub.eqRight a b))
            intro b' hb'
            exact Acc.inv (H (eqW a b') (StepCtxFull.eqWR hb'))
              (Or.inr (ImmSub.eqRight a b'))

theorem acc_descent_of_snCtx {t : Trace} (ht : SNCtx t) : Acc Descent t := by
  induction ht with
  | intro t h ih => exact acc_descent_aux t (Acc.intro t h) (fun a ha => ih a ha)

/-! ## The recursor -/

/-- `recΔ b s n` terminates when `b` and `s` terminate and `n` is `Descent`-accessible.
`R_rec_succ` uses the descent from `delta n` to `n`, the dependency-pair comparison; `R_rec_zero`
uses the termination of `b`. -/
theorem snCtx_recΔ {n : Trace} (hn : Acc Descent n) :
    ∀ b s : Trace, SNCtx b → SNCtx s → SNCtx (recΔ b s n) := by
  induction hn with
  | intro n _ ihn =>
      intro b s hb
      revert s
      induction hb with
      | intro b hb' ihb =>
          intro s hs
          induction hs with
          | intro s hs' ihs =>
              constructor
              intro u hu
              change StepCtxFull (recΔ b s n) u at hu
              cases hu with
              | root hr =>
                  cases hr with
                  | R_rec_zero => exact Acc.intro b hb'
                  | R_rec_succ b s m =>
                      apply snCtx_app (Acc.intro s hs')
                      exact ihn m (Or.inr (ImmSub.delta m)) b s (Acc.intro b hb')
                        (Acc.intro s hs')
              | recB hs => exact ihb _ hs s (Acc.intro s hs')
              | recS hs => exact ihs _ hs
              | recN hs =>
                  exact ihn _ (Or.inl hs) b s (Acc.intro b hb') (Acc.intro s hs')

/-- Every trace terminates under the full contextual relation. -/
theorem snCtx_all : ∀ t : Trace, SNCtx t
  | void => snCtx_void
  | delta t => snCtx_delta (snCtx_all t)
  | integrate t => snCtx_integrate (snCtx_all t)
  | merge a b => snCtx_merge (snCtx_all a) (snCtx_all b)
  | app a b => snCtx_app (snCtx_all a) (snCtx_all b)
  | recΔ b s n => snCtx_recΔ (acc_descent_of_snCtx (snCtx_all n)) b s (snCtx_all b) (snCtx_all s)
  | eqW a b => snCtx_eqW (snCtx_all a) (snCtx_all b)

/--
`thm:full-context-closed-sn` of the Orientation Boundary paper, second proof.

Proves: the reverse of the full contextual closure `StepCtxFull` of the eight KO7 root rules is
well founded, by the rule-derived route: no interpretation, weight or ordering parameter.
Does not prove: confluence; `StepCtxFull` is not confluent (`eqW void void`).
Relation: `MetaSN_KO7.StepCtxFull`. Closure: full one-hole context closure.
Property: termination. Scope: row 03-011. Trust: kernel-only.
-/
theorem wf_StepCtxFullRev_rule_derived : WellFounded StepCtxFullRev := ⟨snCtx_all⟩

/-- The two termination proofs of the full contextual relation side by side: the polynomial
interpretation `W` and the rule-derived descent. -/
theorem stepCtxFull_terminates_two_routes :
    WellFounded StepCtxFullRev ∧ WellFounded StepCtxFullRev :=
  ⟨wf_StepCtxFullRev_poly, wf_StepCtxFullRev_rule_derived⟩

/-- The dependency-pair comparison of `R_rec_succ` is an instance of the descent relation. -/
theorem dp_pair_is_descent (n : Trace) : Descent n (delta n) := Or.inr (ImmSub.delta n)

end OperatorKO7.Meta.BoundaryObserver.ContextRuleDerivedSN
