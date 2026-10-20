import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Yamada Tuple-Interpretation Barrier: Additive-Sum Fragment (Schema Layer)

Yamada's tuple interpretations (bibliographic anchor `YamadaTuple22` in
Paper A) order tuples of naturals by componentwise weak decrease together with
a strict decrease of the coordinate sum. This module records the schema-level
barrier for the additive-sum fragment: a tuple-valued, constructor-monotone
interpretation whose coordinate sum is tracked by an `AdditiveMeasure` of the
step-duplicating schema cannot orient the duplicating step, because any
successful orientation strictly decreases the coordinate sum and would thereby
induce an additive-measure orientation, which the Tier-1 barrier
`no_additive_orients_dup_step` already forbids.

Scope honesty: this is not a barrier against tuple interpretations as a whole.
Tuple interpretations whose coordinate sum is not additive-compositional (for
example max-plus or matrix-style aggregations) belong, if at all, to their own
barrier classes. Paper A classifies general tuple interpretations as outside
the direct barrier; this module certifies exactly the named fragment above.

## Porting note (Rule W17)

```text
source system / paper: A. Yamada, "Tuple Interpretations for Termination of
  Term Rewriting", 2022 (YamadaTuple22)
source theorem name: tuple-interpretation termination criterion (strict order
  on Nat^d: componentwise weak decrease and strict sum decrease)
Lean theorem name: no_yamadaTupleAdditiveSum_orients_dup_step
source logic and equality: classical first-order TRS semantics
Lean logic and equality: Lean 4 / CIC, propositional equality
object language: first-order terms over a signature
metatheory: schema-level measure barriers
embedding: shallow (tuple order as a Prop-valued comparison)
classical axioms used: none beyond the project baseline
choice/extensionality/quotient assumptions: none beyond the project baseline
termination/productivity assumptions: none
relation and strategy translation: orientation of the duplicating schema step
  recur b s (succ n) -> wrap s (recur b s n), root step, no strategy
  restriction
known semantic gaps: the coordinate-sum additivity hypothesis restricts the
  fragment; arbitrary Yamada tuple interpretations are not claimed
```

## Audit slots

```text
Relation:  schema duplicating step (root), via GlobalOrients for the global
           lift; not a context-closed relation.
Closure:   root step only.
Strategy:  not applicable (no strategy restriction).
Trust:     kernel-only. No sorry, no new axioms, no native computation.
Scope:     additive-sum Yamada fragment over any step-duplicating schema and
           any tuple dimension.
```
-/

set_option autoImplicit false

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

open scoped BigOperators

/-- Componentwise weak comparison on tuple values. -/
def TupleLe {d : Nat} (x y : Fin d → Nat) : Prop :=
  ∀ i, x i ≤ y i

/-- Yamada strict comparison on tuple values: weak decrease on every
coordinate together with a strict decrease of the coordinate sum. -/
def TupleLt {d : Nat} (x y : Fin d → Nat) : Prop :=
  TupleLe x y ∧ (∑ i, x i) < (∑ i, y i)

/-- A Yamada-fragment tuple interpretation of a step-duplicating schema: a
tuple-valued interpretation, monotone in each constructor argument under the
componentwise weak tuple order, whose coordinate sum is tracked by an additive
compositional measure `summed`. The strict Yamada comparison `TupleLt` strictly
decreases the coordinate sum, so `summed` inherits every strict orientation. -/
structure YamadaTupleMeasure (S : StepDuplicatingSchema) (d : Nat) where
  eval : S.T → Fin d → Nat
  summed : AdditiveMeasure S
  eval_sum : ∀ t, summed.eval t = ∑ i, eval t i
  mono_succ :
    ∀ {t u : S.T},
      TupleLe (eval t) (eval u) → TupleLe (eval (S.succ t)) (eval (S.succ u))
  mono_wrap :
    ∀ {x x' y y' : S.T},
      TupleLe (eval x) (eval x') → TupleLe (eval y) (eval y') →
        TupleLe (eval (S.wrap x y)) (eval (S.wrap x' y'))
  mono_recur :
    ∀ {b b' s s' n n' : S.T},
      TupleLe (eval b) (eval b') → TupleLe (eval s) (eval s') →
        TupleLe (eval n) (eval n') →
          TupleLe (eval (S.recur b s n)) (eval (S.recur b' s' n'))

/--
Proves: no additive-sum Yamada tuple interpretation orients the duplicating
schema step at the root.
Does not prove: anything about tuple interpretations whose coordinate sum is
not additive-compositional.
Relation: schema duplicating step `recur b s (succ n) -> wrap s (recur b s n)`.
Closure: root step.
Strategy: not applicable.
Trust: kernel-only.
Scope: any step-duplicating schema, any tuple dimension.
-/
theorem no_yamadaTupleAdditiveSum_orients_dup_step
    {S : StepDuplicatingSchema} {d : Nat} (M : YamadaTupleMeasure S d) :
    ¬ (∀ (b s n : S.T),
      TupleLt (M.eval (S.wrap s (S.recur b s n))) (M.eval (S.recur b s (S.succ n)))) := by
  intro h
  apply no_additive_orients_dup_step (S := S) M.summed
  intro b s n
  rw [M.eval_sum, M.eval_sum]
  exact (h b s n).2

/--
Proves: the additive-sum Yamada barrier lifts to global root orientation over
any rewrite system whose signature contains the duplicating step.
Does not prove: termination or nontermination of any concrete system.
Relation: the system's `Step`, restricted to the duplicating step family.
Closure: root step.
Strategy: not applicable.
Trust: kernel-only.
Scope: any step-duplicating system, any tuple dimension.
-/
theorem no_global_orients_yamadaTupleAdditiveSum
    {Sys : StepDuplicatingSystem} {d : Nat}
    (M : YamadaTupleMeasure Sys.toStepDuplicatingSchema d) :
    ¬ GlobalOrients Sys M.eval TupleLt := by
  intro h
  apply no_yamadaTupleAdditiveSum_orients_dup_step
    (S := Sys.toStepDuplicatingSchema) (M := M)
  intro b s n
  exact h (Sys.dup_step b s n)

/--
Proves: the weak tuple order pulled back along the interpretation is a
precongruence over the schema constructors: reflexive, transitive, and closed
under `succ`, `wrap`, and `recur`. This is the load-bearing use of the
monotonicity fields; the barrier theorem itself consumes only `eval_sum`.
Does not prove: compatibility of the strict sum comparison with contexts.
Relation: not a rewriting relation; a property of the tuple order.
Closure: constructor contexts of the schema.
Strategy: not applicable.
Trust: kernel-only.
Scope: any step-duplicating schema, any tuple dimension.
-/
theorem yamadaTupleAdditiveSum_weakOrder_precongruence
    {S : StepDuplicatingSchema} {d : Nat} (M : YamadaTupleMeasure S d) :
    (∀ t : S.T, TupleLe (M.eval t) (M.eval t)) ∧
      (∀ {t u v : S.T},
        TupleLe (M.eval t) (M.eval u) → TupleLe (M.eval u) (M.eval v) →
          TupleLe (M.eval t) (M.eval v)) ∧
      (∀ {t u : S.T},
        TupleLe (M.eval t) (M.eval u) →
          TupleLe (M.eval (S.succ t)) (M.eval (S.succ u))) ∧
      (∀ {x x' y y' : S.T},
        TupleLe (M.eval x) (M.eval x') → TupleLe (M.eval y) (M.eval y') →
          TupleLe (M.eval (S.wrap x y)) (M.eval (S.wrap x' y'))) ∧
      (∀ {b b' s s' n n' : S.T},
        TupleLe (M.eval b) (M.eval b') → TupleLe (M.eval s) (M.eval s') →
          TupleLe (M.eval n) (M.eval n') →
            TupleLe (M.eval (S.recur b s n)) (M.eval (S.recur b' s' n'))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t i
    exact le_refl _
  · intro t u v htu huv i
    exact le_trans (htu i) (huv i)
  · intro t u h
    exact M.mono_succ h
  · intro x x' y y' hx hy
    exact M.mono_wrap hx hy
  · intro b b' s s' n n' hb hs hn
    exact M.mono_recur hb hs hn

/-- Any additive measure lifts to a one-dimensional Yamada-fragment tuple
interpretation, so the barrier class is inhabited (non-vacuity witness for the
structure). -/
def yamadaTupleOfAdditive {S : StepDuplicatingSchema} (M : AdditiveMeasure S) :
    YamadaTupleMeasure S 1 where
  eval := fun t _ => M.eval t
  summed := M
  eval_sum := fun t => (Fin.sum_univ_one (fun _ => M.eval t)).symm
  mono_succ := by
    intro t u h i
    show M.eval (S.succ t) ≤ M.eval (S.succ u)
    rw [M.eval_succ, M.eval_succ]
    exact Nat.add_le_add_left (h 0) _
  mono_wrap := by
    intro x x' y y' hx hy i
    show M.eval (S.wrap x y) ≤ M.eval (S.wrap x' y')
    rw [M.eval_wrap, M.eval_wrap]
    exact Nat.add_le_add (Nat.add_le_add_left (hx 0) _) (hy 0)
  mono_recur := by
    intro b b' s s' n n' hb hs hn i
    show M.eval (S.recur b s n) ≤ M.eval (S.recur b' s' n')
    rw [M.eval_recur, M.eval_recur]
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (hb 0) _) (hs 0)) (hn 0)

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating
