import OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure

/-!
# Universal Boundary Calculus: the carrier-level pump barrier

The scalar-grammar closure (the no-cap dichotomy `eval_section_const_or_unbounded`, the semantic converse
`orients_implies_payload_blind`, the `payload_reading_measure_blocked` headline, and the sound checker
bridge `payloadEffective?_not_payloadBlind`) is owned by the Orientation Boundary module
`BoundaryGeneral.DirectMeasureGrammarClosure`, so the orientation-boundary paper cites one self-contained
module for "a direct grammar measure orients the duplicating step if and only if it is payload-blind".

This module keeps only the genuinely domain-general half: the pump barrier stated with no reference to the
grammar syntax at all. The matrix and tracked-vector families of the orientation-boundary work are
different syntaxes over the same `(counter, payload)` mass carrier, and the pump needs only payload
monotonicity and an unbounded payload section, so one theorem blocks all of them. That is universal-layer
content, not scalar-grammar content, which is why it lives here.

## Audit slots

```
Relation: not a rewriting relation; the syntax-free form of the blocked side.
Closure:  not applicable; the statement quantifies over arbitrary payload-monotone measures.
Trust:    baseline; one monotone pump argument reusing the orientation-boundary definitions.
Scope:    any payload-monotone measure with an unbounded payload section; the grammar converse and the
          exact characterization are owned by BoundaryGeneral.DirectMeasureGrammarClosure.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.GrammarClosure

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure

/-- **Grammar-free pump barrier.** Any payload-monotone measure whose payload section is unbounded at some
counter cannot orient the duplicating step. The matrix and tracked-vector families reduce to a
payload-monotone mass measure, so this single theorem blocks all of them without reconstructing their
syntax: a fixed left-hand value at counter `c` cannot dominate the unbounded right-hand family the pump
produces at the same counter. -/
theorem monotone_unbounded_section_not_orients (m : Nat → Nat → Nat)
    (hmono : PayloadMonotone m) (c : Nat)
    (hunb : ∀ N, ∃ p, N ≤ m c p) : ¬ OrientsDupStep m := by
  intro h
  obtain ⟨q, hq⟩ := hunb (m (c + 1) 0 + 1)
  have ho := h c 0 (q + 1) (Nat.succ_le_succ (Nat.zero_le q))
  have hge : m c q ≤ m c (0 + (q + 1)) := hmono c q (0 + (q + 1)) (by omega)
  omega

/-- The scalar grammar is one instance of the carrier-level barrier: a grammar measure with an unbounded
payload section at some counter is blocked, by `eval_payloadMonotone`. This ties the orientation-boundary
grammar closure to the syntax-free form without re-deriving the converse. -/
theorem grammar_unbounded_section_not_orients (e : MeasureExpr) (c : Nat)
    (hunb : ∀ N, ∃ p, N ≤ e.eval c p) : ¬ OrientsDupStep e.eval :=
  monotone_unbounded_section_not_orients e.eval (eval_payloadMonotone e) c hunb

#print axioms monotone_unbounded_section_not_orients
#print axioms grammar_unbounded_section_not_orients

end OperatorKO7.Meta.UniversalBoundary.GrammarClosure
