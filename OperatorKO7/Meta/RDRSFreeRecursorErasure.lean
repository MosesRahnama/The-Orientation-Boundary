import OperatorKO7.Meta.RDRSSemanticArbitraryClassifier
import OperatorKO7.Meta.Methods.OrientationClosure.SchemaCore

set_option autoImplicit false

/-!
# Payload erasure on free-recursor syntax

The free recursor rewrites `recur b s (succ n)` to `wrap s (recur b s n)` at the root
(`OperatorKO7.Methods.OrientationClosure.SchemaCore.RootStep.recurSucc`). Reading the
base, step and counter arguments as the base, payload and counter coordinates, this rule
is the RDRS step `freeRecursorSuccStep ν`. Its instances are exactly the root steps of the
free recursor from a recursor call with a successor counter
(`freeRecursorSuccStep_instance_iff`).

The map `freeRecursorErase` replaces the step argument by `zero`, the base constant of the
free schema (`SchemaCore.freeSchema`), on both sides of the rule: `recur b s n` goes to
`recur b zero n`, and `wrap s (recur b s' n)` goes to `wrap zero (recur b zero n)`. Every
other term is fixed. The map is a payload erasure of the successor step with neutral
payload `zero` (`freeRecursorPayloadErasure`). The generic erasure theorems of
`OperatorKO7.Meta.RDRSSemanticArbitraryClassifier` then hold on free-recursor syntax: for
every orienting semantic measure on `FreeTerm ν` the erased measure is payload-independent
on both sides of the rule and orients every instance, every orienting semantic measure is
counter-dominated, and no semantic measure is decisively payload-sensitive.

The measure `freeCounterPayloadMeasure` adds the successor depth of the payload to the
successor depth of the counter. It orients the successor rule and reads the payload, so the
erasure theorem applies to a measure that is not itself payload-blind.

## Formal scope

```text
Relation: SchemaCore.RootStep restricted to the successor rule recurSucc, presented as
          freeRecursorSuccStep ν : RDRSStep (FreeTerm ν) (FreeTerm ν) (FreeTerm ν) (FreeTerm ν).
Closure: root single-step orientation only.
Strategy: not applicable.
Trust: kernel-only.
Scope: every variable type ν : Type (the universe of RDRSStep). The zero rule recurZero
       has no successor counter and is not an instance of the RDRS step.
```
-/

namespace OperatorKO7.RDRSFreeRecursorErasure

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticArbitraryClassifier
open OperatorKO7.Methods.OrientationClosure.SchemaCore

/-! ## 1. The successor rule as an RDRS step -/

/--
Proves: the root successor rule of the free recursor as an RDRS step on `FreeTerm ν`,
with left-hand side `recur b s (succ n)` and right-hand side `wrap s (recur b s n)` at
base `b`, payload `s` and counter `n`.
Does not prove: any orientation or termination property; the definition fixes the step.
Relation: `SchemaCore.RootStep`, rule `recurSucc`.
Closure: root single step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type`.
-/
def freeRecursorSuccStep (ν : Type) :
    RDRSStep (FreeTerm ν) (FreeTerm ν) (FreeTerm ν) (FreeTerm ν) where
  lhs b s n := .recur b s (.succ n)
  rhs b s n := .wrap s (.recur b s n)

/--
Proves: a pair `(t, u)` of free terms is an instance of `freeRecursorSuccStep ν` if and
only if `t` rewrites to `u` by a root step of the free recursor and `t` is a recursor call
with a successor counter.
Does not prove: anything about the zero rule `recurZero` beyond its exclusion, or about
contextual steps.
Relation: `SchemaCore.RootStep`, rule `recurSucc`.
Closure: root single step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type` and every pair of free terms.
-/
theorem freeRecursorSuccStep_instance_iff {ν : Type} (t u : FreeTerm ν) :
    (∃ b s n, t = (freeRecursorSuccStep ν).lhs b s n ∧
        u = (freeRecursorSuccStep ν).rhs b s n) ↔
      RootStep t u ∧ ∃ b s n : FreeTerm ν, t = .recur b s (.succ n) := by
  constructor
  · rintro ⟨b, s, n, rfl, rfl⟩
    exact ⟨RootStep.recurSucc b s n, b, s, n, rfl⟩
  · rintro ⟨h, b, s, n, rfl⟩
    cases h
    exact ⟨_, _, _, rfl, rfl⟩

/-! ## 2. The erasure map -/

/--
Proves: the erasure map of the free recursor. It sends `recur b s n` to
`recur b zero n` and `wrap s (recur b s' n)` to `wrap zero (recur b zero n)`, and fixes
every other term.
Does not prove: any property of the map; `freeRecursorPayloadErasure` records its two
erasure equations.
Relation: function on free terms; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type`.
-/
def freeRecursorErase {ν : Type} : FreeTerm ν → FreeTerm ν
  | .recur b _ n => .recur b .zero n
  | .wrap _ (.recur b _ n) => .wrap .zero (.recur b .zero n)
  | t => t

/--
Proves: `freeRecursorErase` with neutral payload `zero` is a payload erasure of the
successor rule: `recur b s (succ n)` goes to `recur b zero (succ n)` and
`wrap s (recur b s n)` goes to `wrap zero (recur b zero n)`, for all `b`, `s`, `n`.
Does not prove: an erasure for the zero rule, or a context-closed erasure.
Relation: `freeRecursorSuccStep ν`.
Closure: root single-step shape equations.
Strategy: not applicable.
Trust: kernel-only; both equations hold by reduction of the definitions.
Scope: every `ν : Type`.
-/
def freeRecursorPayloadErasure (ν : Type) : PayloadErasure (freeRecursorSuccStep ν) where
  erase := freeRecursorErase
  neutralPayload := .zero
  lhs_erase := fun _ _ _ => rfl
  rhs_erase := fun _ _ _ => rfl

/-! ## 3. The erasure theorems on free-recursor syntax -/

/--
Proves: for every semantic measure `M` on `FreeTerm ν` that orients the successor rule,
the erased measure `fun t => M.μ (freeRecursorErase t)` takes one value on the sources
`recur b s (succ n)` for all payloads `s`, takes one value on the targets
`wrap s (recur b s n)` for all payloads `s`, and orients every instance of the rule.
Does not prove: that `M.μ` itself is payload-independent; contextual or zero-rule
orientation; termination.
Relation: `freeRecursorSuccStep ν`.
Closure: root single step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type` and every `SemanticMeasureData (FreeTerm ν)`.
-/
theorem freeRecursor_erased_measure_orients {ν : Type}
    (M : SemanticMeasureData (FreeTerm ν))
    (hOrient : Orients (freeRecursorSuccStep ν) M.μ M.ltA) :
    (∀ b s s' n : FreeTerm ν,
        M.μ (freeRecursorErase (.recur b s (.succ n))) =
          M.μ (freeRecursorErase (.recur b s' (.succ n)))) ∧
      (∀ b s s' n : FreeTerm ν,
        M.μ (freeRecursorErase (.wrap s (.recur b s n))) =
          M.μ (freeRecursorErase (.wrap s' (.recur b s' n)))) ∧
      Orients (freeRecursorSuccStep ν) (fun t => M.μ (freeRecursorErase t)) M.ltA :=
  orienting_measure_erased_measure_orients (freeRecursorPayloadErasure ν) M hOrient

/--
Proves: every semantic measure on `FreeTerm ν` that orients the successor rule is
counter-dominated; the witness is the erased measure of
`freeRecursor_erased_measure_orients`.
Does not prove: termination or contextual orientation.
Relation: `freeRecursorSuccStep ν`.
Closure: root single step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type` and every `SemanticMeasureData (FreeTerm ν)`.
-/
theorem freeRecursor_orienting_measure_counter_dominated {ν : Type}
    (M : SemanticMeasureData (FreeTerm ν))
    (hOrient : Orients (freeRecursorSuccStep ν) M.μ M.ltA) :
    CounterDominated (freeRecursorSuccStep ν) M :=
  orienting_measure_counter_dominated_of_payload_erasure
    (freeRecursorPayloadErasure ν) M hOrient

/--
Proves: no semantic measure on `FreeTerm ν` is decisively payload-sensitive on the
successor rule.
Does not prove: that payload-reading measures fail to orient; such a measure can orient,
and it is then counter-dominated.
Relation: `freeRecursorSuccStep ν`.
Closure: root single step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type` and every `SemanticMeasureData (FreeTerm ν)`.
-/
theorem freeRecursor_no_decisive_payload_sensitive {ν : Type}
    (M : SemanticMeasureData (FreeTerm ν)) :
    ¬ PayloadSensitiveDecisive (freeRecursorSuccStep ν) M :=
  no_decisive_payload_sensitive_of_payload_erasure (freeRecursorPayloadErasure ν) M

/--
Proves: no certified semantic direct measure on `FreeTerm ν` is decisively
payload-sensitive on the successor rule.
Does not prove: source inspection of the measure body.
Relation: `freeRecursorSuccStep ν`.
Closure: root single step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type` and every `SemanticDirectMeasure (FreeTerm ν)`.
-/
theorem freeRecursor_no_direct_decisive_payload_sensitive {ν : Type}
    (M : SemanticDirectMeasure (FreeTerm ν)) :
    ¬ PayloadSensitiveDecisive (freeRecursorSuccStep ν) M.data :=
  no_direct_decisive_payload_sensitive_of_payload_erasure (freeRecursorPayloadErasure ν) M

/-! ## 4. A payload-reading orienting measure -/

/--
Proves: the successor depth of a free term, the number of leading `succ` constructors.
Does not prove: any orientation property.
Relation: function on free terms; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; structural recursion.
Scope: every `ν : Type`.
-/
def freeSuccDepth {ν : Type} : FreeTerm ν → Nat
  | .succ t => freeSuccDepth t + 1
  | _ => 0

/--
Proves: the weight `freeSuccDepth n + freeSuccDepth s` of a recursor call `recur b s n`,
read through the right argument of `wrap`, and `0` on every other term.
Does not prove: any orientation property; `freeCounterPayloadMeasure_orients` states it.
Relation: function on free terms; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only; structural recursion.
Scope: every `ν : Type`.
-/
def freeCounterPayloadWeight {ν : Type} : FreeTerm ν → Nat
  | .recur _ s n => freeSuccDepth n + freeSuccDepth s
  | .wrap _ t => freeCounterPayloadWeight t
  | _ => 0

/--
Proves: the semantic measure on `FreeTerm ν` with values `freeCounterPayloadWeight` in
`Nat` under the strict order `<`.
Does not prove: orientation (`freeCounterPayloadMeasure_orients`) or payload reading
(`freeCounterPayloadMeasure_payloadSensitiveRaw`).
Relation: measure data; not a rewriting relation.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type`.
-/
def freeCounterPayloadMeasure (ν : Type) : SemanticMeasureData (FreeTerm ν) where
  A := Nat
  ltA := fun a b => a < b
  wf_ltA := Nat.lt_wfRel.wf
  μ := freeCounterPayloadWeight

/--
Proves: `freeCounterPayloadMeasure ν` orients every instance of the successor rule: the
target weight `freeSuccDepth n + freeSuccDepth s` is below the source weight
`(freeSuccDepth n + 1) + freeSuccDepth s`.
Does not prove: contextual orientation or termination of the free recursor.
Relation: `freeRecursorSuccStep ν`.
Closure: root single step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type`.
-/
theorem freeCounterPayloadMeasure_orients (ν : Type) :
    Orients (freeRecursorSuccStep ν) (freeCounterPayloadMeasure ν).μ
      (freeCounterPayloadMeasure ν).ltA := by
  intro b s n
  show freeSuccDepth n + freeSuccDepth s < freeSuccDepth n + 1 + freeSuccDepth s
  exact Nat.add_lt_add_right (Nat.lt_succ_self _) _

/--
Proves: `freeCounterPayloadMeasure ν` reads the payload: at base `zero`, counter `zero`
and payloads `zero` and `succ zero`, its values on the source `recur b s (succ n)` are
`1` and `2`.
Does not prove: decisive payload sensitivity; `freeRecursor_no_decisive_payload_sensitive`
excludes it.
Relation: `freeRecursorSuccStep ν`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type`; the witness terms contain no variable.
-/
theorem freeCounterPayloadMeasure_payloadSensitiveRaw (ν : Type) :
    PayloadSensitiveRaw (freeRecursorSuccStep ν) (freeCounterPayloadMeasure ν) :=
  ⟨.zero, .zero, .succ .zero, .zero, by
    show (1 : Nat) ≠ 2
    decide⟩

/--
Proves: `freeCounterPayloadMeasure ν`, an orienting measure that reads the payload, is
counter-dominated. The hypothesis of `freeRecursor_orienting_measure_counter_dominated`
is inhabited at the carrier `FreeTerm ν` by a measure that is not payload-blind.
Does not prove: that the measure itself is payload-blind
(`freeCounterPayloadMeasure_payloadSensitiveRaw` refutes that).
Relation: `freeRecursorSuccStep ν`.
Closure: root single step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `ν : Type`.
-/
theorem freeCounterPayloadMeasure_counter_dominated (ν : Type) :
    CounterDominated (freeRecursorSuccStep ν) (freeCounterPayloadMeasure ν) :=
  freeRecursor_orienting_measure_counter_dominated (freeCounterPayloadMeasure ν)
    (freeCounterPayloadMeasure_orients ν)

end OperatorKO7.RDRSFreeRecursorErasure
