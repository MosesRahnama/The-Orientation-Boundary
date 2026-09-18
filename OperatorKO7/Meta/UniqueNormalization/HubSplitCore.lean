import OperatorKO7.Meta.UniqueNormalization.HubFreshEncoding

/-!
# RTA #79 route R2: stateful hub occurrence splitter

For each original variable, the first left-to-right occurrence is retained as the
fixed hub variable. Every later occurrence is renamed to a collision-free fresh
code `hubFresh base x k` and emits the equality condition
`x = hubFresh base x k`.

This is the exact shape required by `LinearizesRule`: both endpoints of every
condition occur in the transformed left-hand side, the hub endpoint is fixed by
collapse, and every fresh endpoint collapses to the hub. A global occurrence
counter supplies unique fresh indices across the entire term.

Trust: kernel checked. No external certificate or new axiom.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniqueNormalization

open OperatorKO7.Meta.Rewriting

universe u

variable {sigma : Type u}

/-- Result of splitting one term. -/
structure HubSplitResult (sigma : Type u) where
  term : Term sigma Nat
  next : Nat
  seen : List Nat
  conds : List (Term sigma Nat × Term sigma Nat)

/-- Result of splitting an argument list. -/
structure HubSplitListResult (sigma : Type u) where
  terms : List (Term sigma Nat)
  next : Nat
  seen : List Nat
  conds : List (Term sigma Nat × Term sigma Nat)

mutual
/-- Split repeated variable occurrences, threading the global occurrence counter
and the set of variables already represented by a hub occurrence. -/
def hubSplitTermAux (base next : Nat) (seen : List Nat) :
    Term sigma Nat → HubSplitResult sigma
  | .var x =>
      if x ∈ seen then
        let fresh := hubFresh base x next
        { term := .var fresh
          next := next + 1
          seen := seen
          conds := [(.var x, .var fresh)] }
      else
        { term := .var x
          next := next + 1
          seen := x :: seen
          conds := [] }
  | .app f args =>
      let r := hubSplitListAux base next seen args
      { term := .app f r.terms
        next := r.next
        seen := r.seen
        conds := r.conds }
/-- Sequential split across an argument list. -/
def hubSplitListAux (base next : Nat) (seen : List Nat) :
    List (Term sigma Nat) → HubSplitListResult sigma
  | [] => { terms := [], next := next, seen := seen, conds := [] }
  | t :: ts =>
      let rt := hubSplitTermAux base next seen t
      let rs := hubSplitListAux base rt.next rt.seen ts
      { terms := rt.term :: rs.terms
        next := rs.next
        seen := rs.seen
        conds := rt.conds ++ rs.conds }
end

/-- Split a term from an empty seen set and occurrence index zero. -/
def hubSplitTerm (base : Nat) (t : Term sigma Nat) : Term sigma Nat :=
  (hubSplitTermAux base 0 [] t).term

/-- Equality conditions emitted by the zero-based split. -/
def hubSplitConditions (base : Nat) (t : Term sigma Nat) :
    List (Term sigma Nat × Term sigma Nat) :=
  (hubSplitTermAux base 0 [] t).conds

/-- Every source occurrence lies below a chosen fresh base. -/
def VarOccurrencesBelow (base : Nat) (t : Term sigma Nat) : Prop :=
  ∀ x, VarOccurs x t → x < base

mutual
/-- Collapse reconstructs a split term exactly whenever every original variable
lies below the reserved fresh tail. -/
theorem hubSplitTermAux_collapse (base next : Nat) (seen : List Nat) :
    ∀ t : Term sigma Nat,
      VarOccurrencesBelow base t →
      Term.mapVar (hubCollapse base) (hubSplitTermAux base next seen t).term = t
  | .var x, hbelow => by
      by_cases hx : x ∈ seen
      · simp [hubSplitTermAux, hx]
      · simp [hubSplitTermAux, hx, hubCollapse_of_lt (hbelow x VarOccurs.here)]
  | .app f args, hbelow => by
      simp only [hubSplitTermAux, Term.mapVar_app]
      congr 1
      exact hubSplitListAux_collapse base next seen args
        (fun a ha x hx => hbelow x (VarOccurs.arg ha hx))
/-- List-level collapse theorem. -/
theorem hubSplitListAux_collapse (base next : Nat) (seen : List Nat) :
    ∀ args : List (Term sigma Nat),
      (∀ a ∈ args, VarOccurrencesBelow base a) →
      Term.mapVarList (hubCollapse base)
          (hubSplitListAux base next seen args).terms = args
  | [], _ => by simp [hubSplitListAux]
  | t :: ts, hbelow => by
      simp only [hubSplitListAux, Term.mapVarList_cons]
      rw [hubSplitTermAux_collapse base next seen t
        (hbelow t (List.mem_cons_self ..))]
      exact congrArg (List.cons t)
        (hubSplitListAux_collapse base
          (hubSplitTermAux base next seen t).next
          (hubSplitTermAux base next seen t).seen ts
          (fun a ha => hbelow a (List.mem_cons_of_mem _ ha)))
end

/-- Rule LHS variables satisfy the fresh-base condition. -/
theorem rule_lhs_varOccurrencesBelow {rule : Rule sigma Nat} :
    VarOccurrencesBelow (ruleFreshBase rule) rule.lhs := by
  intro x hx
  exact lhs_occ_lt_ruleFreshBase hx.mem_varOccurrences

/-- Zero-based split of a rule LHS followed by its rule-specific collapse is the
identity. -/
theorem hubSplitRuleLhs_collapse (rule : Rule sigma Nat) :
    Term.mapVar (hubCollapse (ruleFreshBase rule))
      (hubSplitTerm (ruleFreshBase rule) rule.lhs) = rule.lhs := by
  exact hubSplitTermAux_collapse (ruleFreshBase rule) 0 [] rule.lhs
    rule_lhs_varOccurrencesBelow

mutual
/-- The threaded occurrence counter advances by exactly the source occurrence
count. -/
theorem hubSplitTermAux_next (base next : Nat) (seen : List Nat) :
    ∀ t : Term sigma Nat,
      (hubSplitTermAux base next seen t).next =
        next + (Term.varOccurrences t).length
  | .var x => by
      by_cases hx : x ∈ seen <;> simp [hubSplitTermAux, hx, Term.varOccurrences]
  | .app f args => by
      simp only [hubSplitTermAux, Term.varOccurrences]
      exact hubSplitListAux_next base next seen args
/-- List-level counter invariant. -/
theorem hubSplitListAux_next (base next : Nat) (seen : List Nat) :
    ∀ args : List (Term sigma Nat),
      (hubSplitListAux base next seen args).next =
        next + (args.flatMap Term.varOccurrences).length
  | [] => by simp [hubSplitListAux]
  | t :: ts => by
      simp only [hubSplitListAux, List.flatMap_cons, List.length_append]
      rw [hubSplitListAux_next, hubSplitTermAux_next]
      omega
end

mutual
/-- At most one condition is emitted per source occurrence. -/
theorem hubSplitTermAux_conds_length_le (base next : Nat) (seen : List Nat) :
    ∀ t : Term sigma Nat,
      (hubSplitTermAux base next seen t).conds.length ≤
        (Term.varOccurrences t).length
  | .var x => by
      by_cases hx : x ∈ seen <;> simp [hubSplitTermAux, hx, Term.varOccurrences]
  | .app f args => by
      simp only [hubSplitTermAux, Term.varOccurrences]
      exact hubSplitListAux_conds_length_le base next seen args
/-- List-level condition-count bound. -/
theorem hubSplitListAux_conds_length_le (base next : Nat) (seen : List Nat) :
    ∀ args : List (Term sigma Nat),
      (hubSplitListAux base next seen args).conds.length ≤
        (args.flatMap Term.varOccurrences).length
  | [] => by simp [hubSplitListAux]
  | t :: ts => by
      simp only [hubSplitListAux, List.length_append, List.flatMap_cons]
      exact Nat.add_le_add
        (hubSplitTermAux_conds_length_le base next seen t)
        (hubSplitListAux_conds_length_le base
          (hubSplitTermAux base next seen t).next
          (hubSplitTermAux base next seen t).seen ts)
end

/-- Zero-based condition-count bound. -/
theorem hubSplitConditions_length_le (base : Nat) (t : Term sigma Nat) :
    (hubSplitConditions base t).length ≤ (Term.varOccurrences t).length :=
  hubSplitTermAux_conds_length_le base 0 [] t

end OperatorKO7.Meta.UniqueNormalization

#check @OperatorKO7.Meta.UniqueNormalization.HubSplitResult
#check @OperatorKO7.Meta.UniqueNormalization.HubSplitListResult
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitListAux
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTerm
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitConditions
#check @OperatorKO7.Meta.UniqueNormalization.VarOccurrencesBelow
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_collapse
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_collapse
#check @OperatorKO7.Meta.UniqueNormalization.rule_lhs_varOccurrencesBelow
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitRuleLhs_collapse
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_next
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_next
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_conds_length_le
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_conds_length_le
#check @OperatorKO7.Meta.UniqueNormalization.hubSplitConditions_length_le

#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_collapse
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_collapse
#print axioms OperatorKO7.Meta.UniqueNormalization.rule_lhs_varOccurrencesBelow
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitRuleLhs_collapse
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_next
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_next
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitTermAux_conds_length_le
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitListAux_conds_length_le
#print axioms OperatorKO7.Meta.UniqueNormalization.hubSplitConditions_length_le
