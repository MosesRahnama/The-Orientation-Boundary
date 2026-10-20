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
different syntaxes over the same `(counter, payload)` mass carrier, and the pump needs only an unbounded
payload section at one counter, so one theorem blocks all of them. Payload monotonicity is not a premise:
`unbounded_section_not_orients` holds for every measure `Nat → Nat → Nat`, and
`evenPayloadMeasure_not_orients` applies it to a measure that is not payload-monotone (ledger row 01-009).

## Audit slots

```
Relation: not a rewriting relation; the syntax-free form of the blocked side.
Closure:  not applicable; the statement quantifies over arbitrary measures Nat → Nat → Nat.
Trust:    baseline; one pump argument reusing the orientation-boundary definitions.
Scope:    any measure with an unbounded payload section at one counter; the grammar converse and the
          exact characterization are owned by BoundaryGeneral.DirectMeasureGrammarClosure.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.UniversalBoundary.GrammarClosure

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure

/-- **Premise-free pump barrier** (OB Thm 4.9 `thm:grammar-closure-barrier`, syntax-free form;
submission Section 6.8; ledger row 01-009). Every measure whose payload section at one counter `c`
is unbounded fails to orient the duplicating step.
Proves: `¬ OrientsDupStep m` from `∀ N, ∃ p, N ≤ m c p`, for every `m : Nat → Nat → Nat`.
Does not prove: anything about a measure whose payload sections are bounded at every counter.
Relation: the abstract duplicating step on the carrier `Nat × Nat`, from `(c + 1, p)` to `(c, p + L)`
with `1 ≤ L`, through `OrientsDupStep`.
Closure: one step, uniform over the counter, the payload and the step length.
Strategy: not applicable.
Trust: kernel only; the arithmetic closes by `omega`.
Scope: every measure and every counter. The witness payload `q` satisfies
`max (m (c + 1) 0) (m c 0) < m c q`; the bound against `m c 0` forces `1 ≤ q`, so `L = q` is an
admissible step length at `(c, 0)`, and orientation there contradicts the bound against
`m (c + 1) 0`. No payload monotonicity enters the proof. -/
theorem unbounded_section_not_orients (m : Nat → Nat → Nat) (c : Nat)
    (hunb : ∀ N, ∃ p, N ≤ m c p) : ¬ OrientsDupStep m := by
  intro h
  obtain ⟨q, hq⟩ := hunb (max (m (c + 1) 0) (m c 0) + 1)
  have hleft : m (c + 1) 0 ≤ max (m (c + 1) 0) (m c 0) := le_max_left _ _
  have hright : m c 0 ≤ max (m (c + 1) 0) (m c 0) := le_max_right _ _
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · subst hq0
      omega
    · exact hq0
  have ho : m c (0 + q) < m (c + 1) 0 := h c 0 q hq1
  rw [Nat.zero_add] at ho
  omega

/-- **Grammar-free pump barrier, payload-monotone form.** Any payload-monotone measure whose payload
section is unbounded at some counter cannot orient the duplicating step.
Proves: `¬ OrientsDupStep m` for a payload-monotone `m` with an unbounded section at `c`.
Does not prove: anything beyond `unbounded_section_not_orients`; the premise `_hmono` is not
load-bearing, since the proof calls the premise-free theorem (ledger row 01-009). The statement is
kept unchanged because the published claim indexes cite this name.
Relation: as in `unbounded_section_not_orients`.
Closure: one step.
Strategy: not applicable.
Trust: kernel only.
Scope: every payload-monotone measure and every counter. -/
theorem monotone_unbounded_section_not_orients (m : Nat → Nat → Nat)
    (_hmono : PayloadMonotone m) (c : Nat)
    (hunb : ∀ N, ∃ p, N ≤ m c p) : ¬ OrientsDupStep m :=
  unbounded_section_not_orients m c hunb

/-- The scalar grammar is one instance of the carrier-level barrier: a grammar measure with an
unbounded payload section at some counter is blocked. The proof calls the premise-free barrier
`unbounded_section_not_orients` directly; `eval_payloadMonotone` is no longer on its path. -/
theorem grammar_unbounded_section_not_orients (e : MeasureExpr) (c : Nat)
    (hunb : ∀ N, ∃ p, N ≤ e.eval c p) : ¬ OrientsDupStep e.eval :=
  unbounded_section_not_orients e.eval c hunb

/-! ## A measure outside the payload-monotone class -/

/-- The payload on even payloads and zero on odd payloads, at every counter. -/
def evenPayloadMeasure (_c p : Nat) : Nat := if p % 2 = 0 then p else 0

/-- Proves: `evenPayloadMeasure` takes the value of `p` on even payloads.
Does not prove: a value on odd payloads beyond the definition.
Relation: equality of `Nat`. Closure: not applicable. Strategy: not applicable.
Trust: kernel only. Scope: every counter and every even payload. -/
theorem evenPayloadMeasure_even (c k : Nat) : evenPayloadMeasure c (2 * k) = 2 * k := by
  unfold evenPayloadMeasure
  rw [if_pos (Nat.mul_mod_right 2 k)]

/-- Proves: `evenPayloadMeasure` is not payload-monotone: the payload `2` reads `2` and the payload
`3` reads `0` at counter `0`.
Does not prove: anything about orientation by itself.
Relation: `PayloadMonotone`. Closure: not applicable. Strategy: not applicable.
Trust: kernel only, by `decide` on closed values. Scope: the measure `evenPayloadMeasure`. -/
theorem evenPayloadMeasure_not_payloadMonotone : ¬ PayloadMonotone evenPayloadMeasure :=
  fun h => absurd (h 0 2 3 (by decide)) (by decide)

/-- Proves: the payload section of `evenPayloadMeasure` at counter `0` is unbounded; the payload
`2 * N` reads `2 * N`.
Does not prove: monotonicity.
Relation: the section `fun p => evenPayloadMeasure 0 p`. Closure: not applicable.
Strategy: not applicable. Trust: kernel only. Scope: every bound `N`. -/
theorem evenPayloadMeasure_unbounded_section :
    ∀ N, ∃ p, N ≤ evenPayloadMeasure 0 p := by
  intro N
  refine ⟨2 * N, ?_⟩
  rw [evenPayloadMeasure_even]
  omega

/-- **The premise-free barrier reaches a measure outside the monotone class.** `evenPayloadMeasure`
is not payload-monotone, so `monotone_unbounded_section_not_orients` does not apply to it, and
`unbounded_section_not_orients` blocks it.
Proves: `evenPayloadMeasure` does not orient the duplicating step, and it is not payload-monotone.
Does not prove: anything about other measures.
Relation: `OrientsDupStep`. Closure: one step. Strategy: not applicable.
Trust: kernel only. Scope: the measure `evenPayloadMeasure` (ledger row 01-009, non-vacuity). -/
theorem evenPayloadMeasure_not_orients :
    ¬ OrientsDupStep evenPayloadMeasure ∧ ¬ PayloadMonotone evenPayloadMeasure :=
  ⟨unbounded_section_not_orients evenPayloadMeasure 0 evenPayloadMeasure_unbounded_section,
    evenPayloadMeasure_not_payloadMonotone⟩

#print axioms unbounded_section_not_orients
#print axioms monotone_unbounded_section_not_orients
#print axioms grammar_unbounded_section_not_orients
#print axioms evenPayloadMeasure_not_orients

end OperatorKO7.Meta.UniversalBoundary.GrammarClosure
