import OperatorKO7.Meta.EqGuardedConfluence
import OperatorKO7.Meta.DistinctionBoundary.ContextualClassification

set_option autoImplicit false

/-!
# The surgical repair under context: a guard that does not lift

Manuscript anchors: `thm:eqguarded-ctx-fails`, `thm:guard-instability`,
`cor:safestep-guards-earn-context`, `thm:ctx-classifier` of
`Rahnama_The_Distinction_Boundary`. Roadmap: `ROADMAP-08` follow-on, sprint
S4R.

## The result

`EqGuardedStep` is the unique greatest admissible repair at the root, and it is
root confluent. This module proves that its full context closure is **not**
confluent, and isolates the reason.

The reason is that a disequality guard is not stable under reduction. The rule
`R_eq_diff` fires at `eqW a b` when `a` and `b` are syntactically distinct, but
a distinct pair can become identical after a step inside an argument. At that
point the root has already committed to the difference verdict while the
context is still free to reach the reflexive verdict, and the two verdicts do
not join.

The witness is the smallest one available:

```
eqW (merge void void) void
```

Its two arguments are distinct, so the difference branch is licensed at the
root. Its first argument reduces to `void`, after which the reflexive branch is
licensed instead. The first route reaches `integrate void` and the second
reaches `void`, and both are normal forms of the guarded contextual relation.

## What this buys

The extra guards carried by `SafeStep` are not redundant decoration on the
disequality guard: they are what makes the guarded relation survive context
closure, which the minimal root repair does not. Root minimality and contextual
confluence are therefore in tension, and the development needs both relations
for different jobs. This corrects the reading, natural after the root results
alone, on which `SafeStep` looked like a strictly heavier relation with no
compensating gain.

Relation: `EqGuardedStepCtx` (full context closure of the surgical repair) and
`StepCtxFull`. Closure: `Relation.ReflTransGen`. Trust: kernel only, Mathlib
baseline.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.ContextualConfluence

open OperatorKO7 Trace
open OperatorKO7.EqGuardedConfluence
open MetaSN_KO7
open OperatorKO7.Meta.DistinctionBoundary.ContextualDiagonalScope
open OperatorKO7.Meta.DistinctionBoundary.ContextualClassification

/-! ## The full context closure of the surgical repair -/

/-- Full congruence closure of `EqGuardedStep`: the guarded root rules may fire
at every position. -/
inductive EqGuardedStepCtx : Trace → Trace → Prop
| root {a b : Trace} : EqGuardedStep a b → EqGuardedStepCtx a b
| delta {t u : Trace} : EqGuardedStepCtx t u → EqGuardedStepCtx (delta t) (delta u)
| integrate {t u : Trace} : EqGuardedStepCtx t u → EqGuardedStepCtx (integrate t) (integrate u)
| mergeL {a a' b : Trace} : EqGuardedStepCtx a a' → EqGuardedStepCtx (merge a b) (merge a' b)
| mergeR {a b b' : Trace} : EqGuardedStepCtx b b' → EqGuardedStepCtx (merge a b) (merge a b')
| appL {a a' b : Trace} : EqGuardedStepCtx a a' → EqGuardedStepCtx (app a b) (app a' b)
| appR {a b b' : Trace} : EqGuardedStepCtx b b' → EqGuardedStepCtx (app a b) (app a b')
| recB {b b' s n : Trace} : EqGuardedStepCtx b b' → EqGuardedStepCtx (recΔ b s n) (recΔ b' s n)
| recS {b s s' n : Trace} : EqGuardedStepCtx s s' → EqGuardedStepCtx (recΔ b s n) (recΔ b s' n)
| recN {b s n n' : Trace} : EqGuardedStepCtx n n' → EqGuardedStepCtx (recΔ b s n) (recΔ b s n')
| eqWL {a a' b : Trace} : EqGuardedStepCtx a a' → EqGuardedStepCtx (eqW a b) (eqW a' b)
| eqWR {a b b' : Trace} : EqGuardedStepCtx b b' → EqGuardedStepCtx (eqW a b) (eqW a b')

/-- Reflexive-transitive closure of the guarded contextual relation. -/
abbrev EqGuardedCtxStar : Trace → Trace → Prop := Relation.ReflTransGen EqGuardedStepCtx

/-- Confluence of the guarded contextual relation. -/
def ConfluentEqGuardedCtx : Prop :=
  ∀ a b c, EqGuardedCtxStar a b → EqGuardedCtxStar a c →
    ∃ d, EqGuardedCtxStar b d ∧ EqGuardedCtxStar c d

/-- The guarded contextual relation is inside the unguarded one. -/
theorem eqGuardedCtx_sub_stepCtxFull {s t : Trace} (h : EqGuardedStepCtx s t) :
    StepCtxFull s t := by
  induction h with
  | root hr => exact StepCtxFull.root (eqGuarded_sub_step hr)
  | delta _ ih => exact StepCtxFull.delta ih
  | integrate _ ih => exact StepCtxFull.integrate ih
  | mergeL _ ih => exact StepCtxFull.mergeL ih
  | mergeR _ ih => exact StepCtxFull.mergeR ih
  | appL _ ih => exact StepCtxFull.appL ih
  | appR _ ih => exact StepCtxFull.appR ih
  | recB _ ih => exact StepCtxFull.recB ih
  | recS _ ih => exact StepCtxFull.recS ih
  | recN _ ih => exact StepCtxFull.recN ih
  | eqWL _ ih => exact StepCtxFull.eqWL ih
  | eqWR _ ih => exact StepCtxFull.eqWR ih

/-! ## Normal forms of the witness -/

/-- `void` has no guarded contextual step: it is neither a root redex nor a
compound term with a reducible argument. -/
theorem no_step_from_void (u : Trace) : ¬ EqGuardedStepCtx void u := by
  intro h
  cases h with
  | root hr => cases hr

/-- `integrate void` has no guarded contextual step. The root rule for an
`integrate` head needs a `delta`-headed argument, and the argument `void` is
itself irreducible. -/
theorem no_step_from_integrate_void (u : Trace) :
    ¬ EqGuardedStepCtx (integrate void) u := by
  intro h
  cases h with
  | root hr => cases hr
  | integrate hinner => exact no_step_from_void _ hinner

/-- A source with no outgoing step reaches only itself. -/
theorem star_eq_of_no_step {x : Trace} (hx : ∀ u, ¬ EqGuardedStepCtx x u)
    {d : Trace} (h : EqGuardedCtxStar x d) : d = x := by
  induction h with
  | refl => rfl
  | tail _ hlast ih =>
      rw [ih] at hlast
      exact absurd hlast (hx _)

/-! ## The witness and its two routes -/

/-- The witness term: a diagonal that is not yet diagonal. -/
def witness : Trace := eqW (merge void void) void

/-- The two arguments of the witness are distinct, so the difference branch is
licensed at the root. -/
theorem witness_args_distinct : (merge void void) ≠ void := by
  intro h
  exact Trace.noConfusion h

/-- Route one: the root commits to the difference verdict, and the result
normalises to `integrate void`. -/
theorem witness_to_integrate_void :
    EqGuardedCtxStar witness (integrate void) := by
  have s1 : EqGuardedStepCtx witness (integrate (merge (merge void void) void)) :=
    EqGuardedStepCtx.root (EqGuardedStep.R_eq_diff _ _ witness_args_distinct)
  have s2 : EqGuardedStepCtx (integrate (merge (merge void void) void))
      (integrate (merge void void)) :=
    EqGuardedStepCtx.integrate
      (EqGuardedStepCtx.root (EqGuardedStep.R_merge_void_right (merge void void)))
  have s3 : EqGuardedStepCtx (integrate (merge void void)) (integrate void) :=
    EqGuardedStepCtx.integrate
      (EqGuardedStepCtx.root (EqGuardedStep.R_merge_void_left void))
  exact ((Relation.ReflTransGen.single s1).tail s2).tail s3

/-- Route two: the context makes the pair diagonal first, and the reflexive
verdict then fires. -/
theorem witness_to_void : EqGuardedCtxStar witness void := by
  have s1 : EqGuardedStepCtx witness (eqW void void) :=
    EqGuardedStepCtx.eqWL
      (EqGuardedStepCtx.root (EqGuardedStep.R_merge_void_left void))
  have s2 : EqGuardedStepCtx (eqW void void) void :=
    EqGuardedStepCtx.root (EqGuardedStep.R_eq_refl void)
  exact (Relation.ReflTransGen.single s1).tail s2

/-! ## The theorem -/

/-- **The surgical repair fails under context.** The full context closure of
`EqGuardedStep` is not confluent. The witness reaches two distinct normal
forms: `void` by making the pair diagonal before the verdict is read, and
`integrate void` by reading the difference verdict first. -/
theorem eqGuardedStepCtx_not_confluent : ¬ ConfluentEqGuardedCtx := by
  intro hconf
  obtain ⟨d, hd1, hd2⟩ := hconf witness void (integrate void)
    witness_to_void witness_to_integrate_void
  have h1 : d = void := star_eq_of_no_step no_step_from_void hd1
  have h2 : d = integrate void :=
    star_eq_of_no_step no_step_from_integrate_void hd2
  rw [h1] at h2
  exact Trace.noConfusion h2

/-- **The mechanism, isolated.** A disequality guard is not stable under
reduction: a licensed difference pair can become a diagonal pair after a step
inside an argument. The witness exhibits it. -/
theorem guard_not_stable_under_reduction :
    ∃ a b : Trace, a ≠ b ∧ EqGuardedStepCtx (eqW a b) (eqW b b) := by
  refine ⟨merge void void, void, witness_args_distinct, ?_⟩
  exact EqGuardedStepCtx.eqWL
    (EqGuardedStepCtx.root (EqGuardedStep.R_merge_void_left void))

/-- **Root confluence does not lift.** The surgical repair is confluent at the
root and not confluent under full context closure. Both halves are stated
together so the manuscript can cite one anchor for the tension. -/
theorem root_confluent_but_ctx_not :
    ConfluentEqGuarded ∧ ¬ ConfluentEqGuardedCtx :=
  ⟨confluentEqGuarded, eqGuardedStepCtx_not_confluent⟩

/-- The two routes end at normal forms that do not join, stated directly. -/
theorem witness_normal_forms_not_joinable :
    ¬ ∃ d, EqGuardedCtxStar (integrate void) d ∧ EqGuardedCtxStar void d := by
  rintro ⟨d, hd1, hd2⟩
  have h1 : d = integrate void :=
    star_eq_of_no_step no_step_from_integrate_void hd1
  have h2 : d = void := star_eq_of_no_step no_step_from_void hd2
  rw [h1] at h2
  exact Trace.noConfusion h2

/-- **The compensating reading.** There is a pair that is off the diagonal when
the difference verdict is read and on the diagonal one step later, and its two
verdicts reach normal forms that do not join. Any repair restoring contextual
confluence must therefore constrain more than the root diagonal, which is what
the payload guards of `SafeStep` do; the positive contextual statement for that
relation is the separate `SafeStepCtx` confluence development. -/
theorem contextual_repair_needs_more_than_root_guard :
    ∃ a b : Trace,
      a ≠ b ∧
      EqGuardedStepCtx (eqW a b) (integrate (merge a b)) ∧
      EqGuardedStepCtx (eqW a b) (eqW b b) ∧
      EqGuardedCtxStar (integrate (merge a b)) (integrate void) ∧
      EqGuardedCtxStar (eqW b b) void ∧
      ¬ ∃ d, EqGuardedCtxStar (integrate void) d ∧ EqGuardedCtxStar void d := by
  refine ⟨merge void void, void, witness_args_distinct, ?_, ?_, ?_, ?_,
    witness_normal_forms_not_joinable⟩
  · exact EqGuardedStepCtx.root (EqGuardedStep.R_eq_diff _ _ witness_args_distinct)
  · exact EqGuardedStepCtx.eqWL
      (EqGuardedStepCtx.root (EqGuardedStep.R_merge_void_left void))
  · have s2 : EqGuardedStepCtx (integrate (merge (merge void void) void))
        (integrate (merge void void)) :=
      EqGuardedStepCtx.integrate
        (EqGuardedStepCtx.root (EqGuardedStep.R_merge_void_right (merge void void)))
    have s3 : EqGuardedStepCtx (integrate (merge void void)) (integrate void) :=
      EqGuardedStepCtx.integrate
        (EqGuardedStepCtx.root (EqGuardedStep.R_merge_void_left void))
    exact (Relation.ReflTransGen.single s2).tail s3
  · exact Relation.ReflTransGen.single
      (EqGuardedStepCtx.root (EqGuardedStep.R_eq_refl void))

/-! ## The raw contextual classifier lives elsewhere

The equivalence between joinability of the raw contextual diagonal peak and
reachability of a `delta`-headed term is
`ContextualClassification.diagonal_ctx_joins_iff_reaches_delta`, proved there
through its own cone invariants. It is not restated here; this module is about
the guarded relation, and the two results answer different questions. The raw
classifier says which diagonals dissolve under the unguarded relation; the
theorems above say that the minimal guarded repair does not survive context
closure at all. -/

end OperatorKO7.Meta.DistinctionBoundary.ContextualConfluence
