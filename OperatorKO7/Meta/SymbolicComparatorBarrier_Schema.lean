/-!
# Symbolic Variable-Condition Barrier: Schema Layer

Schema-generic symbolic obstruction behind direct KBO-style comparators.

This file isolates the variable-count argument on the primitive duplicating
schema terms themselves. KO7-specific trace instantiation lives in
`Meta/SymbolicComparatorBarrier.lean`.
-/

namespace OperatorKO7.SymbolicComparatorBarrier

inductive SchemaVar where
  | b
  | s
  | n
deriving DecidableEq, Repr

inductive STerm where
  | var : SchemaVar → STerm
  | base : STerm
  | succ : STerm → STerm
  | wrap : STerm → STerm → STerm
  | recur : STerm → STerm → STerm → STerm
deriving DecidableEq, Repr

open SchemaVar

def countVar (v : SchemaVar) : STerm → Nat
  | STerm.var w => if v = w then 1 else 0
  | STerm.base => 0
  | STerm.succ t => countVar v t
  | STerm.wrap x y => countVar v x + countVar v y
  | STerm.recur bT sT nT => countVar v bT + countVar v sT + countVar v nT

def dupSrc : STerm :=
  STerm.recur (STerm.var b) (STerm.var s) (STerm.succ (STerm.var n))

def dupTgt : STerm :=
  STerm.wrap (STerm.var s) (STerm.recur (STerm.var b) (STerm.var s) (STerm.var n))

theorem countVar_dupSrc_b : countVar b dupSrc = 1 := by
  simp [dupSrc, countVar]

theorem countVar_dupSrc_s : countVar s dupSrc = 1 := by
  simp [dupSrc, countVar]

theorem countVar_dupSrc_n : countVar n dupSrc = 1 := by
  simp [dupSrc, countVar]

theorem countVar_dupTgt_b : countVar b dupTgt = 1 := by
  simp [dupTgt, countVar]

theorem countVar_dupTgt_s : countVar s dupTgt = 2 := by
  simp [dupTgt, countVar]

theorem countVar_dupTgt_n : countVar n dupTgt = 1 := by
  simp [dupTgt, countVar]

structure VariableConditionOrder where
  gt : STerm → STerm → Prop
  variable_condition :
    ∀ {x y : STerm} {v : SchemaVar}, gt x y → countVar v y ≤ countVar v x

theorem not_orients_dup_rule (O : VariableConditionOrder) :
    ¬ O.gt dupSrc dupTgt := by
  intro h
  have hs : countVar s dupTgt ≤ countVar s dupSrc := O.variable_condition h
  simp [countVar_dupSrc_s, countVar_dupTgt_s] at hs

theorem no_symbolic_variable_condition_orients_dup_step :
    ¬ ∃ O : VariableConditionOrder, O.gt dupSrc dupTgt := by
  rintro ⟨O, h⟩
  exact not_orients_dup_rule O h

/-! ## A well-founded inhabitant

Gate R5 witness for `VariableConditionOrder`. The comparison `x > y` holds when every schema
variable occurs in `y` at most as often as in `x` and `y` has strictly smaller size: a
Knuth-Bendix-style order with unit weights and an empty precedence. It is well founded, it orients
the zero rule `recur b s base → b` of the recursor and the successor peel `succ n → n`, and it
rejects the duplicating rule as `not_orients_dup_rule` requires. -/

/-- Number of constructor and variable occurrences in a schema term.
Proves: nothing; a definition.
Scope: the schema syntax `STerm`. -/
def STerm.size : STerm → Nat
  | STerm.var _ => 1
  | STerm.base => 1
  | STerm.succ t => STerm.size t + 1
  | STerm.wrap x y => STerm.size x + STerm.size y + 1
  | STerm.recur bT sT nT => STerm.size bT + STerm.size sT + STerm.size nT + 1

/-- Inhabitant of `VariableConditionOrder`: variable-count dominance together with strict size
decrease.
Proves: the class of the variable-condition barrier is inhabited by a comparison with positive
instances.
Does not prove: orientation of the duplicating rule; `sizeVariableConditionOrder_rejects_dup_rule`
excludes it.
Relation: the comparison `gt` on schema terms.
Closure: not applicable; a comparison of two terms. Strategy: not applicable.
Trust: kernel only.
Scope: the schema syntax `STerm` with the three schema variables. -/
def sizeVariableConditionOrder : VariableConditionOrder where
  gt x y := (∀ v : SchemaVar, countVar v y ≤ countVar v x) ∧ STerm.size y < STerm.size x
  variable_condition := fun h => h.1 _

/-- Proves: `sizeVariableConditionOrder` orients the successor peel `succ n → n`.
Does not prove: orientation of any duplicating rule.
Relation: the comparison `gt` of `sizeVariableConditionOrder`.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: the closed instance with the schema variable `n`. -/
theorem sizeVariableConditionOrder_orients_succ_peel :
    sizeVariableConditionOrder.gt (STerm.succ (STerm.var n)) (STerm.var n) :=
  ⟨fun _ => Nat.le_refl _, by decide⟩

/-- Proves: `sizeVariableConditionOrder` orients the zero rule `recur b s base → b`, a rule that
duplicates no variable.
Does not prove: orientation of the duplicating successor rule.
Relation: the comparison `gt` of `sizeVariableConditionOrder`.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: the rule instance with the schema variables `b` and `s`. -/
theorem sizeVariableConditionOrder_orients_zero_rule :
    sizeVariableConditionOrder.gt (STerm.recur (STerm.var b) (STerm.var s) STerm.base)
      (STerm.var b) :=
  ⟨fun v => by cases v <;> decide, by decide⟩

/-- Proves: the reverse of `sizeVariableConditionOrder.gt` is well founded, through strict
decrease of `STerm.size`.
Does not prove: monotonicity under contexts.
Relation: the comparison `gt` of `sizeVariableConditionOrder`, read from larger to smaller.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: every schema term. -/
theorem sizeVariableConditionOrder_wellFounded :
    WellFounded (fun y x : STerm => sizeVariableConditionOrder.gt x y) :=
  Subrelation.wf (fun {_ _} h => h.2) (InvImage.wf STerm.size Nat.lt_wfRel.wf)

/-- Proves: `sizeVariableConditionOrder` rejects the duplicating rule, as an instance of
`not_orients_dup_rule`.
Does not prove: rejection by orders without the variable condition.
Relation: the comparison `gt` at the rule `dupSrc → dupTgt`.
Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: the inhabitant `sizeVariableConditionOrder`. -/
theorem sizeVariableConditionOrder_rejects_dup_rule :
    ¬ sizeVariableConditionOrder.gt dupSrc dupTgt :=
  not_orients_dup_rule sizeVariableConditionOrder

/-- Proves: `VariableConditionOrder` is inhabited.
Does not prove: anything about the inhabitant beyond the class membership.
Relation: none. Closure: not applicable. Strategy: not applicable.
Trust: kernel only.
Scope: the class `VariableConditionOrder`. -/
theorem variableConditionOrder_nonempty : Nonempty VariableConditionOrder :=
  ⟨sizeVariableConditionOrder⟩

end OperatorKO7.SymbolicComparatorBarrier
