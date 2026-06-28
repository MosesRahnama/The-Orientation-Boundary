import OperatorKO7.Meta.Rewriting.CriticalPairComplete
import OperatorKO7.Meta.DistinctionBoundary.CriticalPairCompleteness
import OperatorKO7.Kernel

set_option autoImplicit false

/-!
# Instantiating the generic Critical Pair Lemma library on the KO7 kernel

Roadmap source: `ROADMAP-01-generic-critical-pair-lemma.md`, sections 4 and 5
(the `CriticalPairLemmaKO7` target) and section 8 (the adequacy-bridge analysis).
This is Wave 5 of ROADMAP-01: the verified first-order rewriting library of
`Meta/Rewriting/*` is instantiated on the eight-rule KO7 kernel, and the
`eqW`-diagonal confluence obstruction is recovered from the generic
critical-pair machinery.

## What this module delivers

Reification (item 1):

- `KO7Sym`, the seven kernel function symbols (`void, delta, integrate, merge,
  app, recd, eqW`) with `DecidableEq`.
- `reifyTrace : Trace → Term KO7Sym Empty`, the ground reification: each `Trace`
  constructor maps to `Term.app` of the reified arguments, over the empty
  variable type so the image is genuinely variable-free.
- `reify : Trace → Term KO7Sym Nat`, the same ground reification landing in the
  `Nat`-variable carrier that the rule system uses, so a reified trace and the
  rewrite relation share one variable type. `reify_eq_rename` connects the two
  through the canonical embedding `Empty.elim`.
- `ko7Rules : TRS KO7Sym Nat`, the eight kernel rules reified with `Nat` object
  variables, including the two non-left-linear rules `eqW(x,x) → void` and
  `merge(x,x) → x`.

Adequacy bridge (item 2):

- `kernel_step_to_rootStep` (the floor): every kernel `Step s t` is a `rootStep`
  of `ko7Rules` between the reified terms, under the ground substitution sending
  the rule's variables to the reified subterms.
- `reify_injective`: distinct traces reify to distinct terms, the inversion
  engine for the converse.
- `rootStep_to_kernel_step`: a `rootStep` of `ko7Rules` between reified terms is a
  kernel `Step`, by inverting the eight rules.
- `kernel_step_iff_rootStep_reify`: the biconditional
  `Kernel.Step s t ↔ rootStep ko7Rules (reify s) (reify t)`. The kernel relation
  is root-only, matching the `rootStep` level exactly; the full context closure
  `Step ko7Rules` additionally rewrites inside subterms.

Recovery of the obstruction from the generic machinery (item 3):

- `ko7_eqW_diagonal_is_generic_critical_pair`: the reified `void` versus
  `integrate(merge(x,x))` pair is emitted by `criticalPairs ko7Rules`, the overlap
  of the reflexivity rule `eqW(x,x) → void` and the difference rule
  `eqW(x,y) → integrate(merge(x,y))` at the root.
- `ko7_eqW_diagonal_not_joinable`: that pair is not joinable in
  `renameTRS ko7Rules`. The `void` component is a normal form whose only reduct is
  itself; the `integrate(merge(x,x))` component stays `integrate`-headed under
  every reduction, so the two never meet.
- `ko7_unguarded_has_nonjoinable_critical_pair`: packaging the two, the unguarded
  reified kernel has a critical pair that is a genuine non-joinable overlap. This
  recovers, at the generic critical-pair level, the content of the hand-enumerated
  `eqW_diagonal_is_the_unique_root_obstruction`.

Relation: generic `Step`/`rootStep`/`StepStar` of `ko7Rules` and `renameTRS
ko7Rules`; kernel `Step` on the reification side. Property: root-step adequacy and
critical-pair non-joinability.

Trust: kernel-only; baseline-only under `#print axioms` (a subset of
`{propext, Classical.choice, Quot.sound}`). Any `Classical.choice`/`propext`
dependence is from `Finset`/`DecidableEq` plumbing inherited through the rewriting
foundation. No `sorry`, `axiom`, `native_decide`, `bv_decide`, `@[csimp]`,
`unsafe`, `partial`, or `opaque`.
-/

namespace OperatorKO7.Meta.DistinctionBoundary

open OperatorKO7 Trace
open OperatorKO7.Meta.Rewriting
open scoped OperatorKO7.Meta.Rewriting.Subst

/-! ## Item 1: the KO7 signature and the reified rule system -/

/-- The seven kernel function symbols, matching the seven `Trace` constructors.
`recd` names the symbol for `recΔ`. -/
inductive KO7Sym
  | void | delta | integrate | merge | app | recd | eqW
deriving DecidableEq

/-- Ground reification of a kernel trace into a variable-free term: each `Trace`
constructor maps to `Term.app` of the reified arguments. The empty variable type
makes the image genuinely ground. -/
def reifyTrace : Trace → Term KO7Sym Empty
  | Trace.void => .app KO7Sym.void []
  | Trace.delta t => .app KO7Sym.delta [reifyTrace t]
  | Trace.integrate t => .app KO7Sym.integrate [reifyTrace t]
  | Trace.merge a b => .app KO7Sym.merge [reifyTrace a, reifyTrace b]
  | Trace.app a b => .app KO7Sym.app [reifyTrace a, reifyTrace b]
  | Trace.recΔ b s n => .app KO7Sym.recd [reifyTrace b, reifyTrace s, reifyTrace n]
  | Trace.eqW a b => .app KO7Sym.eqW [reifyTrace a, reifyTrace b]

/-- Ground reification into the `Nat`-variable carrier used by the rule system.
The image uses no variables; it shares its variable type with `ko7Rules` so the
rewrite relation `Step ko7Rules` and `rootStep ko7Rules` apply to it directly. -/
def reify : Trace → Term KO7Sym Nat
  | Trace.void => .app KO7Sym.void []
  | Trace.delta t => .app KO7Sym.delta [reify t]
  | Trace.integrate t => .app KO7Sym.integrate [reify t]
  | Trace.merge a b => .app KO7Sym.merge [reify a, reify b]
  | Trace.app a b => .app KO7Sym.app [reify a, reify b]
  | Trace.recΔ b s n => .app KO7Sym.recd [reify b, reify s, reify n]
  | Trace.eqW a b => .app KO7Sym.eqW [reify a, reify b]

/-- The ground `Nat`-carrier reification is the `Empty.elim` renaming of the
ground `Empty`-carrier reification: both build the same variable-free structure,
so `reify` is the canonical image of `reifyTrace` in the rule carrier. -/
theorem reify_eq_rename (t : Trace) :
    reify t = Term.rename (Empty.elim) (reifyTrace t) := by
  induction t with
  | void => rfl
  | delta t ih => simp [reify, reifyTrace, Term.renameList, ih]
  | integrate t ih => simp [reify, reifyTrace, Term.renameList, ih]
  | merge a b iha ihb => simp [reify, reifyTrace, Term.renameList, iha, ihb]
  | app a b iha ihb => simp [reify, reifyTrace, Term.renameList, iha, ihb]
  | recΔ b s n ihb ihs ihn => simp [reify, reifyTrace, Term.renameList, ihb, ihs, ihn]
  | eqW a b iha ihb => simp [reify, reifyTrace, Term.renameList, iha, ihb]

/-- `R_int_delta`: `integrate (delta t) → void`. -/
def intDeltaRule : Rule KO7Sym Nat where
  lhs := .app KO7Sym.integrate [.app KO7Sym.delta [.var 0]]
  rhs := .app KO7Sym.void []
  lhs_isApp := rfl

/-- `R_merge_void_left`: `merge void t → t`. -/
def mergeVoidLeftRule : Rule KO7Sym Nat where
  lhs := .app KO7Sym.merge [.app KO7Sym.void [], .var 0]
  rhs := .var 0
  lhs_isApp := rfl

/-- `R_merge_void_right`: `merge t void → t`. -/
def mergeVoidRightRule : Rule KO7Sym Nat where
  lhs := .app KO7Sym.merge [.var 0, .app KO7Sym.void []]
  rhs := .var 0
  lhs_isApp := rfl

/-- `R_merge_cancel`: `merge t t → t`. Non-left-linear (the variable `0` occurs
twice in the left-hand side). -/
def mergeCancelRule : Rule KO7Sym Nat where
  lhs := .app KO7Sym.merge [.var 0, .var 0]
  rhs := .var 0
  lhs_isApp := rfl

/-- `R_rec_zero`: `recΔ b s void → b`. -/
def recZeroRule : Rule KO7Sym Nat where
  lhs := .app KO7Sym.recd [.var 0, .var 1, .app KO7Sym.void []]
  rhs := .var 0
  lhs_isApp := rfl

/-- `R_rec_succ`: `recΔ b s (delta n) → app s (recΔ b s n)`. -/
def recSuccRule : Rule KO7Sym Nat where
  lhs := .app KO7Sym.recd [.var 0, .var 1, .app KO7Sym.delta [.var 2]]
  rhs := .app KO7Sym.app [.var 1, .app KO7Sym.recd [.var 0, .var 1, .var 2]]
  lhs_isApp := rfl

/-- `R_eq_refl`: `eqW a a → void`. Non-left-linear (the variable `0` occurs twice
in the left-hand side). -/
def eqReflRule : Rule KO7Sym Nat where
  lhs := .app KO7Sym.eqW [.var 0, .var 0]
  rhs := .app KO7Sym.void []
  lhs_isApp := rfl

/-- `R_eq_diff`: `eqW a b → integrate (merge a b)`. -/
def eqDiffRule : Rule KO7Sym Nat where
  lhs := .app KO7Sym.eqW [.var 0, .var 1]
  rhs := .app KO7Sym.integrate [.app KO7Sym.merge [.var 0, .var 1]]
  lhs_isApp := rfl

/-- The eight kernel rules reified with `Nat` object variables. Order matches the
`Step` constructors in `Kernel.lean`. -/
def ko7Rules : TRS KO7Sym Nat :=
  [intDeltaRule, mergeVoidLeftRule, mergeVoidRightRule, mergeCancelRule,
    recZeroRule, recSuccRule, eqReflRule, eqDiffRule]

/-! ## Item 2: the adequacy bridge

Each kernel `Step` constructor is a root contraction of the matching reified rule
under the ground substitution sending the rule's `Nat` variables to the reified
subterms of the source. The eight per-rule root-step lemmas below are universally
quantified and proved by computation; `kernel_step_to_rootStep` dispatches to them.
The converse inverts the eight rules, using `reify_injective` for the two
non-left-linear rules. -/

/-- Root step for `R_int_delta`. -/
theorem rootStep_int_delta (t : Trace) :
    rootStep ko7Rules (reify (integrate (delta t))) (reify void) :=
  ⟨intDeltaRule, by simp [ko7Rules], (fun n => if n = 0 then reify t else .var n),
    by simp [reify, intDeltaRule], by simp [reify, intDeltaRule]⟩

/-- Root step for `R_merge_void_left`. -/
theorem rootStep_merge_void_left (t : Trace) :
    rootStep ko7Rules (reify (merge void t)) (reify t) :=
  ⟨mergeVoidLeftRule, by simp [ko7Rules], (fun n => if n = 0 then reify t else .var n),
    by simp [reify, mergeVoidLeftRule], by simp [mergeVoidLeftRule]⟩

/-- Root step for `R_merge_void_right`. -/
theorem rootStep_merge_void_right (t : Trace) :
    rootStep ko7Rules (reify (merge t void)) (reify t) :=
  ⟨mergeVoidRightRule, by simp [ko7Rules], (fun n => if n = 0 then reify t else .var n),
    by simp [reify, mergeVoidRightRule], by simp [mergeVoidRightRule]⟩

/-- Root step for `R_merge_cancel` (non-left-linear). -/
theorem rootStep_merge_cancel (t : Trace) :
    rootStep ko7Rules (reify (merge t t)) (reify t) :=
  ⟨mergeCancelRule, by simp [ko7Rules], (fun n => if n = 0 then reify t else .var n),
    by simp [reify, mergeCancelRule], by simp [mergeCancelRule]⟩

/-- Root step for `R_rec_zero`. -/
theorem rootStep_rec_zero (b s : Trace) :
    rootStep ko7Rules (reify (recΔ b s void)) (reify b) :=
  ⟨recZeroRule, by simp [ko7Rules],
    (fun n => if n = 0 then reify b else if n = 1 then reify s else .var n),
    by simp [reify, recZeroRule], by simp [recZeroRule]⟩

/-- Root step for `R_rec_succ`. -/
theorem rootStep_rec_succ (b s n : Trace) :
    rootStep ko7Rules (reify (recΔ b s (delta n))) (reify (app s (recΔ b s n))) :=
  ⟨recSuccRule, by simp [ko7Rules],
    (fun k => if k = 0 then reify b else if k = 1 then reify s else if k = 2 then reify n
      else .var k),
    by simp [reify, recSuccRule], by simp [reify, recSuccRule]⟩

/-- Root step for `R_eq_refl` (non-left-linear). -/
theorem rootStep_eq_refl (a : Trace) :
    rootStep ko7Rules (reify (eqW a a)) (reify void) :=
  ⟨eqReflRule, by simp [ko7Rules], (fun n => if n = 0 then reify a else .var n),
    by simp [reify, eqReflRule], by simp [reify, eqReflRule]⟩

/-- Root step for `R_eq_diff`. -/
theorem rootStep_eq_diff (a b : Trace) :
    rootStep ko7Rules (reify (eqW a b)) (reify (integrate (merge a b))) :=
  ⟨eqDiffRule, by simp [ko7Rules],
    (fun n => if n = 0 then reify a else if n = 1 then reify b else .var n),
    by simp [reify, eqDiffRule], by simp [reify, eqDiffRule]⟩

/-- The floor of the adequacy bridge: every kernel `Step s t` is a `rootStep` of
`ko7Rules` between the reified terms. Dispatches to the eight per-rule root-step
lemmas; the subterms are inferred from the goal, so no constructor binder is
named. -/
theorem kernel_step_to_rootStep {s t : Trace} (h : Step s t) :
    rootStep ko7Rules (reify s) (reify t) := by
  cases h with
  | R_int_delta => exact rootStep_int_delta _
  | R_merge_void_left => exact rootStep_merge_void_left _
  | R_merge_void_right => exact rootStep_merge_void_right _
  | R_merge_cancel => exact rootStep_merge_cancel _
  | R_rec_zero => exact rootStep_rec_zero _ _
  | R_rec_succ => exact rootStep_rec_succ _ _ _
  | R_eq_refl => exact rootStep_eq_refl _
  | R_eq_diff => exact rootStep_eq_diff _ _

/-- Every kernel `Step s t` lifts to a one-step rewrite of `ko7Rules` between the
reified terms (the root contraction of `kernel_step_to_rootStep`). -/
theorem kernel_step_to_step {s t : Trace} (h : Step s t) :
    Rewriting.Step ko7Rules (reify s) (reify t) :=
  Rewriting.Step.root (kernel_step_to_rootStep h)

/-- Reification is injective: distinct traces have distinct reifications. The
structural inversion engine for the converse adequacy direction (it identifies the
duplicated-variable arguments of the non-left-linear rules). -/
theorem reify_injective : ∀ {a b : Trace}, reify a = reify b → a = b := by
  intro a
  induction a with
  | void => intro b h; cases b <;> simp_all [reify]
  | delta t ih =>
      intro b h; cases b <;> simp only [reify, Term.app.injEq, List.cons.injEq,
        and_true, true_and, reduceCtorEq, false_and, and_false] at h
      exact congrArg Trace.delta (ih h)
  | integrate t ih =>
      intro b h; cases b <;> simp only [reify, Term.app.injEq, List.cons.injEq,
        and_true, true_and, reduceCtorEq, false_and, and_false] at h
      exact congrArg Trace.integrate (ih h)
  | merge x y ihx ihy =>
      intro b h; cases b <;> simp only [reify, Term.app.injEq, List.cons.injEq,
        and_true, true_and, reduceCtorEq, false_and, and_false] at h
      exact congr (congrArg Trace.merge (ihx h.1)) (ihy h.2)
  | app x y ihx ihy =>
      intro b h; cases b <;> simp only [reify, Term.app.injEq, List.cons.injEq,
        and_true, true_and, reduceCtorEq, false_and, and_false] at h
      exact congr (congrArg Trace.app (ihx h.1)) (ihy h.2)
  | recΔ x y z ihx ihy ihz =>
      intro b h; cases b <;> simp only [reify, Term.app.injEq, List.cons.injEq,
        and_true, true_and, reduceCtorEq, false_and, and_false] at h
      exact congr (congr (congrArg Trace.recΔ (ihx h.1)) (ihy h.2.1)) (ihz h.2.2)
  | eqW x y ihx ihy =>
      intro b h; cases b <;> simp only [reify, Term.app.injEq, List.cons.injEq,
        and_true, true_and, reduceCtorEq, false_and, and_false] at h
      exact congr (congrArg Trace.eqW (ihx h.1)) (ihy h.2)

/-- The converse of the floor: a `rootStep` of `ko7Rules` between reified terms is
a kernel `Step`. Inverting each of the eight rules pins the shape of the source
and target traces (`reify_injective` discharges the duplicated-variable arguments
of the two non-left-linear rules), and the matching kernel constructor fires. -/
theorem rootStep_to_kernel_step {s t : Trace}
    (h : rootStep ko7Rules (reify s) (reify t)) : Step s t := by
  obtain ⟨rule, hmem, σ, hlhs, hrhs⟩ := h
  simp only [ko7Rules, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- intDeltaRule: integrate (delta ·) → void
    simp only [intDeltaRule, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
      Subst.apply_var] at hlhs hrhs
    cases s with
    | integrate u =>
        cases u with
        | delta w =>
            simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
              reduceCtorEq] at hlhs
            have htv : t = void := by apply reify_injective; rw [hrhs]; rfl
            rw [htv]
            exact Step.R_int_delta w
        | _ => simp [reify] at hlhs
    | _ => simp [reify] at hlhs
  · -- mergeVoidLeftRule: merge void · → ·
    simp only [mergeVoidLeftRule, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
      Subst.apply_var] at hlhs hrhs
    cases s with
    | merge u v =>
        cases u with
        | void =>
            simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
              reduceCtorEq] at hlhs
            have hv : reify v = σ 0 := hlhs
            have : reify t = reify v := hrhs.trans hv.symm
            exact reify_injective this ▸ Step.R_merge_void_left v
        | _ => simp [reify] at hlhs
    | _ => simp [reify] at hlhs
  · -- mergeVoidRightRule: merge · void → ·
    simp only [mergeVoidRightRule, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
      Subst.apply_var] at hlhs hrhs
    cases s with
    | merge u v =>
        cases v with
        | void =>
            simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
              reduceCtorEq] at hlhs
            have hu : reify u = σ 0 := hlhs
            have : reify t = reify u := hrhs.trans hu.symm
            exact reify_injective this ▸ Step.R_merge_void_right u
        | _ => simp [reify] at hlhs
    | _ => simp [reify] at hlhs
  · -- mergeCancelRule: merge · · → · (non-left-linear)
    simp only [mergeCancelRule, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
      Subst.apply_var] at hlhs hrhs
    cases s with
    | merge u v =>
        simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
          reduceCtorEq] at hlhs
        have hu : reify u = σ 0 := hlhs.1
        have hv : reify v = σ 0 := hlhs.2
        have hvu : v = u := reify_injective (hv.trans hu.symm)
        have htu : t = u := reify_injective (hrhs.trans hu.symm)
        rw [hvu, htu]
        exact Step.R_merge_cancel u
    | _ => simp [reify] at hlhs
  · -- recZeroRule: recΔ b s void → b
    simp only [recZeroRule, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
      Subst.apply_var] at hlhs hrhs
    cases s with
    | recΔ b sc n =>
        cases n with
        | void =>
            simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
              reduceCtorEq] at hlhs
            have hb : reify b = σ 0 := hlhs.1
            have htb : t = b := reify_injective (hrhs.trans hb.symm)
            rw [htb]
            exact Step.R_rec_zero b sc
        | _ => simp [reify] at hlhs
    | _ => simp [reify] at hlhs
  · -- recSuccRule: recΔ b s (delta n) → app s (recΔ b s n)
    simp only [recSuccRule, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
      Subst.apply_var] at hlhs hrhs
    cases s with
    | recΔ b sc n =>
        cases n with
        | delta w =>
            simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
              reduceCtorEq] at hlhs
            obtain ⟨hb, hsc, hw⟩ := hlhs
            cases t with
            | app p q =>
                simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
                  reduceCtorEq] at hrhs
                obtain ⟨hp, hq⟩ := hrhs
                have hpsc : p = sc := reify_injective (hp.trans hsc.symm)
                cases q with
                | recΔ b' sc' w' =>
                    simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
                      reduceCtorEq] at hq
                    obtain ⟨hb', hsc', hw'⟩ := hq
                    have e1 : b' = b := reify_injective (hb'.trans hb.symm)
                    have e2 : sc' = sc := reify_injective (hsc'.trans hsc.symm)
                    have e3 : w' = w := reify_injective (hw'.trans hw.symm)
                    rw [hpsc, e1, e2, e3]
                    exact Step.R_rec_succ b sc w
                | _ => simp [reify] at hq
            | _ => simp [reify] at hrhs
        | _ => simp [reify] at hlhs
    | _ => simp [reify] at hlhs
  · -- eqReflRule: eqW a a → void (non-left-linear)
    simp only [eqReflRule, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
      Subst.apply_var] at hlhs hrhs
    cases s with
    | eqW u v =>
        simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
          reduceCtorEq] at hlhs
        have hu : reify u = σ 0 := hlhs.1
        have hv : reify v = σ 0 := hlhs.2
        have hvu : v = u := reify_injective (hv.trans hu.symm)
        have htv : t = void := by
          apply reify_injective; rw [hrhs]; rfl
        rw [hvu, htv]
        exact Step.R_eq_refl u
    | _ => simp [reify] at hlhs
  · -- eqDiffRule: eqW a b → integrate (merge a b)
    simp only [eqDiffRule, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
      Subst.apply_var] at hlhs hrhs
    cases s with
    | eqW u v =>
        simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
          reduceCtorEq] at hlhs
        obtain ⟨hu, hv⟩ := hlhs
        cases t with
        | integrate r =>
            cases r with
            | merge p q =>
                simp only [reify, Term.app.injEq, List.cons.injEq, and_true, true_and,
                  reduceCtorEq] at hrhs
                obtain ⟨hp, hq⟩ := hrhs
                have hpu : p = u := reify_injective (hp.trans hu.symm)
                have hqv : q = v := reify_injective (hq.trans hv.symm)
                rw [hpu, hqv]
                exact Step.R_eq_diff u v
            | _ => simp [reify] at hrhs
        | _ => simp [reify] at hrhs
    | _ => simp [reify] at hlhs

/-- Adequacy biconditional at the root level: a kernel `Step s t` holds if and
only if `reify s` root-contracts to `reify t` in `ko7Rules`. The kernel relation
is exactly the root rewrite relation of the reified system; the full context
closure `Step ko7Rules` additionally rewrites inside subterms. -/
theorem kernel_step_iff_rootStep_reify {s t : Trace} :
    Step s t ↔ rootStep ko7Rules (reify s) (reify t) :=
  ⟨kernel_step_to_rootStep, rootStep_to_kernel_step⟩

/-! ## Item 3: recovering the eqW-diagonal obstruction generically

The reflexivity rule `eqW(x,x) → void` and the difference rule
`eqW(x,y) → integrate(merge(x,y))` overlap at the root. Renamed apart and unified,
they emit the critical pair `void` versus `integrate(merge(x,x))`. That pair is not
joinable: `void` is a normal form, while `integrate(merge(x,x))` stays
`integrate`-headed forever, so they never meet. This recovers, from the generic
critical-pair construction, the obstruction the hand-enumerated
`eqW_diagonal_is_the_unique_root_obstruction` states directly. -/

/-- The reflexivity rule renamed into the left variable summand. -/
def eqRefl_inl : Rule KO7Sym (RenVar Nat) := renameRule (Sum.inl : Nat → RenVar Nat) eqReflRule

/-- The difference rule renamed into the right variable summand. -/
def eqDiff_inr : Rule KO7Sym (RenVar Nat) := renameRule (Sum.inr : Nat → RenVar Nat) eqDiffRule

/-- The `void` component of the emitted eqW-diagonal critical pair. -/
def cpVoid : Term KO7Sym (RenVar Nat) := .app KO7Sym.void []

/-- The `integrate(merge(x,x))` component of the emitted eqW-diagonal critical
pair, sharing the single variable produced by unifying the two `eqW` left-hand
sides. -/
def cpIntegrateMerge : Term KO7Sym (RenVar Nat) :=
  .app KO7Sym.integrate [.app KO7Sym.merge [.var (Sum.inr 1), .var (Sum.inr 1)]]

/-- The root overlap of the reflexivity and difference rules emits exactly the
eqW-diagonal critical pair `(void, integrate(merge(x,x)))`. The unifier of the two
`eqW` left-hand sides identifies all three involved variables, collapsing
`merge(x,y)` to the diagonal `merge(x,x)`. -/
theorem overlapAt_eqW_diagonal :
    overlapAt eqRefl_inl eqDiff_inr [] = some (cpVoid, cpIntegrateMerge) := by
  simp [overlapAt, eqRefl_inl, eqDiff_inr, eqReflRule, eqDiffRule, renameRule,
    Term.rename, Term.renameList,
    unify, solve, zipPairs, wlSubst1, Subst.subst1, Subst.comp, Subst.id,
    Sum.inr.injEq, cpVoid, cpIntegrateMerge]

/-- The root position is a non-variable position of the reflexivity rule's renamed
left-hand side (its head is `eqW`). -/
theorem nil_mem_nonVarPositions_eqRefl_inl :
    ([] : Pos) ∈ nonVarPositions eqRefl_inl.lhs := by
  simp [eqRefl_inl, eqReflRule, renameRule, Term.rename, Term.renameList]

/-- **Item 3, recovery of the obstruction (membership).** The reified `void`
versus `integrate(merge(x,x))` pair is a critical pair of `ko7Rules`: it is emitted
by overlapping the reflexivity rule `eqW(x,x) → void` and the difference rule
`eqW(x,y) → integrate(merge(x,y))` at the root. This is the generic critical-pair
construction reproducing, as data, the diagonal overlap that the hand-enumerated
completeness result handles by a `Trace`-constructor case split.

Relation: `criticalPairs` of `ko7Rules` (over the renamed carrier `RenVar Nat`).
Property: critical-pair membership. -/
theorem ko7_eqW_diagonal_is_generic_critical_pair :
    (cpVoid, cpIntegrateMerge) ∈ criticalPairs ko7Rules := by
  rw [criticalPairs, List.mem_flatMap]
  refine ⟨eqReflRule, by simp [ko7Rules], ?_⟩
  rw [List.mem_flatMap]
  refine ⟨eqDiffRule, by simp [ko7Rules], ?_⟩
  rw [overlapPairs, List.mem_filterMap]
  exact ⟨[], nil_mem_nonVarPositions_eqRefl_inl, overlapAt_eqW_diagonal⟩

/-! ### Non-joinability of the eqW-diagonal critical pair

The two components live in `renameTRS ko7Rules` (the system the generic
critical-pair soundness and the Critical Pair Lemma are stated against). `cpVoid`
is a normal form whose only reduct is itself; `cpIntegrateMerge` stays
`integrate`-headed under every reduction. Hence they have no common reduct. -/

/-- The membership decomposition of `renameTRS ko7Rules`: each rule is an original
`ko7Rules` rule renamed into one of the two summands. -/
theorem mem_renameTRS_ko7Rules {rule : Rule KO7Sym (RenVar Nat)}
    (h : rule ∈ renameTRS ko7Rules) :
    (∃ r ∈ ko7Rules, rule = renameRule (Sum.inl) r) ∨
      (∃ r ∈ ko7Rules, rule = renameRule (Sum.inr) r) := by
  rw [renameTRS, List.mem_append] at h
  rcases h with h | h
  · rw [List.mem_map] at h; obtain ⟨r, hr, rfl⟩ := h; exact Or.inl ⟨r, hr, rfl⟩
  · rw [List.mem_map] at h; obtain ⟨r, hr, rfl⟩ := h; exact Or.inr ⟨r, hr, rfl⟩

/-- Every renamed `ko7Rules` rule has a left-hand side headed by one of
`integrate`, `merge`, `recd`, or `eqW`: never `void`. The renaming preserves the
head symbol of each rule's left-hand side. -/
theorem renameTRS_lhs_head {rule : Rule KO7Sym (RenVar Nat)}
    (h : rule ∈ renameTRS ko7Rules) :
    ∃ args, rule.lhs = .app KO7Sym.integrate args ∨ rule.lhs = .app KO7Sym.merge args ∨
      rule.lhs = .app KO7Sym.recd args ∨ rule.lhs = .app KO7Sym.eqW args := by
  rcases mem_renameTRS_ko7Rules h with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;>
    · simp only [ko7Rules, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [intDeltaRule, mergeVoidLeftRule, mergeVoidRightRule, mergeCancelRule,
          recZeroRule, recSuccRule, eqReflRule, eqDiffRule, renameRule, Term.rename,
          Term.renameList]

/-- A bare variable has no outgoing rewrite in `renameTRS ko7Rules`: rule left-hand
sides are applications, so no root contraction matches, and a variable has no
argument to descend into. -/
theorem no_step_var {x : RenVar Nat} {b : Term KO7Sym (RenVar Nat)} :
    ¬ Rewriting.Step (renameTRS ko7Rules) (.var x) b := by
  intro h
  rcases Step.rootStep_or_arg (renameTRS ko7Rules) h with hr | ⟨_, _, _, _, _, he1, _, _⟩
  · obtain ⟨rule, hmem, σ, hlhs, _⟩ := hr
    obtain ⟨args, hhead⟩ := renameTRS_lhs_head hmem
    rcases hhead with hh | hh | hh | hh <;>
      · rw [hh] at hlhs
        simp only [Subst.apply_app, Subst.apply_var] at hlhs
        exact absurd hlhs (by simp [reduceCtorEq])
  · exact absurd he1 (by simp [reduceCtorEq])

/-- `cpVoid = app void []` has no outgoing rewrite in `renameTRS ko7Rules`: no rule
left-hand side is headed by `void`, so there is no root contraction, and `void`
has no arguments to descend into. -/
theorem no_step_cpVoid : ¬ ∃ u, Rewriting.Step (renameTRS ko7Rules) cpVoid u := by
  rintro ⟨u, hu⟩
  rcases Step.rootStep_or_arg (renameTRS ko7Rules) hu with hr | ⟨_, pre, _, _, _, he1, _, _⟩
  · obtain ⟨rule, hmem, σ, hlhs, _⟩ := hr
    obtain ⟨args, hhead⟩ := renameTRS_lhs_head hmem
    rcases hhead with hh | hh | hh | hh <;>
      · rw [hh] at hlhs
        simp only [cpVoid, Subst.apply_app, Term.app.injEq, reduceCtorEq, false_and] at hlhs
  · -- cpVoid = app void (pre ++ a :: post), but its argument list is []
    simp only [cpVoid, Term.app.injEq, true_and] at he1
    exact absurd he1.symm (by simp)

/-- Any rewrite sequence out of `cpVoid` is trivial: its only reduct is itself. -/
theorem stepStar_cpVoid_eq {u : Term KO7Sym (RenVar Nat)}
    (h : Rewriting.StepStar (renameTRS ko7Rules) cpVoid u) : u = cpVoid := by
  rcases Relation.ReflTransGen.cases_head h with heq | ⟨v, hv, _⟩
  · exact heq.symm
  · exact absurd ⟨v, hv⟩ no_step_cpVoid

/-- The inner-argument family under the `integrate`: either `merge(x,x)` or the
bare variable `x` (with `x = inr 1`). A one-step rewrite keeps the inner argument
inside this family (merge-cancel sends `merge(x,x)` to `x`; the bare variable does
not step). -/
theorem inner_step_closed {a b : Term KO7Sym (RenVar Nat)}
    (ha : a = .app KO7Sym.merge [.var (Sum.inr 1), .var (Sum.inr 1)] ∨
          a = .var (Sum.inr 1))
    (hstep : Rewriting.Step (renameTRS ko7Rules) a b) :
    b = .app KO7Sym.merge [.var (Sum.inr 1), .var (Sum.inr 1)] ∨
      b = .var (Sum.inr 1) := by
  rcases ha with rfl | rfl
  · -- a = merge(x,x): a root step is merge-cancel (→ x); arg steps go into x (no step)
    rcases Step.rootStep_or_arg (renameTRS ko7Rules) hstep with hr | ⟨f, pre, post, c, d, he1, he2, hinner⟩
    · obtain ⟨rule, hmem, σ, hlhs, hrhs⟩ := hr
      rcases mem_renameTRS_ko7Rules hmem with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;>
        · simp only [ko7Rules, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            first
            | (-- merge-cancel: the genuine reduct, `b = var (inr 1)`
               right
               simp only [mergeCancelRule, renameRule, Term.rename, Term.renameList,
                 Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil, Subst.apply_var,
                 Term.app.injEq, List.cons.injEq, and_true, true_and] at hlhs hrhs
               rw [hrhs, hlhs.1])
            | (-- every other rule: head or argument clash makes `hlhs` impossible
               exfalso
               simp only [intDeltaRule, mergeVoidLeftRule, mergeVoidRightRule, recZeroRule,
                 recSuccRule, eqReflRule, eqDiffRule, renameRule, Term.rename, Term.renameList,
                 Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil, Subst.apply_var,
                 Term.app.injEq, List.cons.injEq, reduceCtorEq, false_and, and_false,
                 and_true, true_and] at hlhs)
    · -- arg step: the redex sits in one slot of [x, x]; both are variables, no step
      exfalso
      simp only [Term.app.injEq, true_and] at he1
      obtain ⟨_, hlist⟩ := he1
      rcases pre with _ | ⟨p0, pre'⟩
      · simp only [List.nil_append, List.cons.injEq] at hlist
        rw [← hlist.1] at hinner; exact no_step_var hinner
      · rcases pre' with _ | ⟨p1, pre''⟩
        · simp only [List.cons_append, List.nil_append, List.cons.injEq] at hlist
          rw [← hlist.2.1] at hinner; exact no_step_var hinner
        · simp only [List.cons_append, List.cons.injEq] at hlist
          exact absurd hlist.2.2.symm (by simp)
  · -- a = var (inr 1): a variable never steps
    exact absurd hstep no_step_var

/-- The reduction-closed family the right component lives in: an `integrate` of
either `merge(x,x)` or the bare variable `x`. Both are `integrate`-headed, hence
distinct from `void`. -/
def IntegrateGood (t : Term KO7Sym (RenVar Nat)) : Prop :=
  t = .app KO7Sym.integrate [.app KO7Sym.merge [.var (Sum.inr 1), .var (Sum.inr 1)]] ∨
    t = .app KO7Sym.integrate [.var (Sum.inr 1)]

/-- `IntegrateGood` is preserved by a single rewrite of `renameTRS ko7Rules`: a
root step is impossible (the only `integrate`-headed rule needs a `delta` argument,
but the inner argument is `merge`-headed or a variable), so the step descends into
the inner argument, which stays inside its family by `inner_step_closed`. -/
theorem integrateGood_step_closed {a b : Term KO7Sym (RenVar Nat)}
    (ha : IntegrateGood a) (hstep : Rewriting.Step (renameTRS ko7Rules) a b) :
    IntegrateGood b := by
  obtain ⟨inner, hinner_eq, hinner_fam⟩ :
      ∃ inner, a = .app KO7Sym.integrate [inner] ∧
        (inner = .app KO7Sym.merge [.var (Sum.inr 1), .var (Sum.inr 1)] ∨
          inner = .var (Sum.inr 1)) := by
    rcases ha with rfl | rfl
    · exact ⟨_, rfl, Or.inl rfl⟩
    · exact ⟨_, rfl, Or.inr rfl⟩
  subst hinner_eq
  rcases Step.rootStep_or_arg (renameTRS ko7Rules) hstep with hr | ⟨f, pre, post, c, d, he1, he2, hinner⟩
  · -- a root step needs `app integrate [inner] = σ • rule.lhs`; the only
    -- integrate-headed rule is intDeltaRule with arg `delta _`, excluded here
    exfalso
    obtain ⟨rule, hmem, σ, hlhs, _⟩ := hr
    rcases mem_renameTRS_ko7Rules hmem with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;>
      · simp only [ko7Rules, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases hinner_fam with rfl | rfl <;>
            simp only [intDeltaRule, mergeVoidLeftRule, mergeVoidRightRule, mergeCancelRule,
              recZeroRule, recSuccRule, eqReflRule, eqDiffRule, renameRule, Term.rename,
              Term.renameList, Subst.apply_app, Subst.applyList_cons, Subst.applyList_nil,
              Subst.apply_var, Term.app.injEq, List.cons.injEq, reduceCtorEq, false_and,
              and_false, and_true, true_and] at hlhs
  · -- the step is inside the single argument [inner]; so pre = [], post = [], c = inner
    simp only [Term.app.injEq, true_and] at he1
    obtain ⟨hf, hlist⟩ := he1
    subst hf
    rcases pre with _ | ⟨p0, pre'⟩
    · -- pre = []: the single argument is the redex
      simp only [List.nil_append, List.cons.injEq] at hlist
      obtain ⟨hci, hpost⟩ := hlist
      rw [← hci] at hinner
      have hb : b = .app KO7Sym.integrate [d] := by
        rw [he2, ← hpost]; rfl
      rcases inner_step_closed hinner_fam hinner with hd | hd
      · left; rw [hb, hd]
      · right; rw [hb, hd]
    · exfalso
      simp only [List.cons_append, List.cons.injEq] at hlist
      exact absurd hlist.2.symm (by simp)

/-- `IntegrateGood` is preserved along a whole rewrite sequence. -/
theorem integrateGood_stepStar_closed {a b : Term KO7Sym (RenVar Nat)}
    (ha : IntegrateGood a) (h : Rewriting.StepStar (renameTRS ko7Rules) a b) : IntegrateGood b := by
  induction h with
  | refl => exact ha
  | tail _ hstep ih => exact integrateGood_step_closed ih hstep

/-- An `IntegrateGood` term is never `cpVoid`: it is `integrate`-headed, while
`cpVoid` is `void`-headed. -/
theorem integrateGood_ne_cpVoid {t : Term KO7Sym (RenVar Nat)} (ht : IntegrateGood t) :
    t ≠ cpVoid := by
  rcases ht with rfl | rfl <;> simp [cpVoid, reduceCtorEq]

/-- **Item 3, the obstruction is genuine.** The eqW-diagonal critical pair is not
joinable in `renameTRS ko7Rules`. A common reduct would have to be `cpVoid` (the
only reduct of the `void` component), but `cpIntegrateMerge` stays
`integrate`-headed under every reduction, so it never reaches `cpVoid`. This is the
non-joinable overlap that obstructs local confluence of the unguarded reified
kernel.

Relation: `StepStar`/`joinable` of `renameTRS ko7Rules`. Property: critical-pair
non-joinability. -/
theorem ko7_eqW_diagonal_not_joinable :
    ¬ joinable (renameTRS ko7Rules) cpVoid cpIntegrateMerge := by
  rintro ⟨u, hvu, hiu⟩
  have hu : u = cpVoid := stepStar_cpVoid_eq hvu
  subst hu
  have hgood : IntegrateGood cpVoid := integrateGood_stepStar_closed (Or.inl rfl) hiu
  exact integrateGood_ne_cpVoid hgood rfl

/-- **Item 3, headline.** The unguarded reified KO7 kernel has a non-joinable
critical pair: the eqW-diagonal pair `(void, integrate(merge(x,x)))` is emitted by
`criticalPairs ko7Rules` and is not joinable in `renameTRS ko7Rules`. Recovered
entirely from the generic critical-pair machinery, this reproduces the content of
the hand-enumerated `eqW_diagonal_is_the_unique_root_obstruction`: the `eqW`
reflexive diagonal breaks local confluence.

Relation: `criticalPairs`/`joinable` of `ko7Rules`/`renameTRS ko7Rules`. Property:
existence of a non-joinable critical pair. -/
theorem ko7_unguarded_has_nonjoinable_critical_pair :
    ∃ p ∈ criticalPairs ko7Rules, ¬ joinable (renameTRS ko7Rules) p.1 p.2 :=
  ⟨(cpVoid, cpIntegrateMerge), ko7_eqW_diagonal_is_generic_critical_pair,
    ko7_eqW_diagonal_not_joinable⟩

end OperatorKO7.Meta.DistinctionBoundary

/-! ## Verification: headline types and axiom audit -/

open OperatorKO7.Meta.DistinctionBoundary in
#check @reifyTrace
open OperatorKO7.Meta.DistinctionBoundary in
#check @reify
open OperatorKO7.Meta.DistinctionBoundary in
#check @ko7Rules
open OperatorKO7.Meta.DistinctionBoundary in
#check @reify_injective
open OperatorKO7.Meta.DistinctionBoundary in
#check @kernel_step_to_rootStep
open OperatorKO7.Meta.DistinctionBoundary in
#check @kernel_step_to_step
open OperatorKO7.Meta.DistinctionBoundary in
#check @rootStep_to_kernel_step
open OperatorKO7.Meta.DistinctionBoundary in
#check @kernel_step_iff_rootStep_reify
open OperatorKO7.Meta.DistinctionBoundary in
#check @ko7_eqW_diagonal_is_generic_critical_pair
open OperatorKO7.Meta.DistinctionBoundary in
#check @ko7_eqW_diagonal_not_joinable
open OperatorKO7.Meta.DistinctionBoundary in
#check @ko7_unguarded_has_nonjoinable_critical_pair

#print axioms OperatorKO7.Meta.DistinctionBoundary.reify_eq_rename
#print axioms OperatorKO7.Meta.DistinctionBoundary.reify_injective
#print axioms OperatorKO7.Meta.DistinctionBoundary.kernel_step_to_rootStep
#print axioms OperatorKO7.Meta.DistinctionBoundary.kernel_step_to_step
#print axioms OperatorKO7.Meta.DistinctionBoundary.rootStep_to_kernel_step
#print axioms OperatorKO7.Meta.DistinctionBoundary.kernel_step_iff_rootStep_reify
#print axioms OperatorKO7.Meta.DistinctionBoundary.ko7_eqW_diagonal_is_generic_critical_pair
#print axioms OperatorKO7.Meta.DistinctionBoundary.ko7_eqW_diagonal_not_joinable
#print axioms OperatorKO7.Meta.DistinctionBoundary.ko7_unguarded_has_nonjoinable_critical_pair
