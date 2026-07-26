import OperatorKO7.Meta.RDRSSemanticArbitraryClassifier

/-!
# Sharpness of the payload-erasure hypothesis (Informational Incompleteness, boundary-as-theorem)

`RecursorPayloadErasure.iiRecursor_orienting_measure_counter_dominated` proves
that on the recursor (which HAS a payload erasure) every orienting semantic
measure is counter-dominated. This module proves that hypothesis is exactly
NECESSARY: it mechanizes a concrete RDRS step with NO payload erasure on which a
payload measure orients but is NOT counter-dominated. So the erasure-free version
of the counter-domination theorem is FALSE in general, and the boundary between
"counter-dominated" (recursor) and "decisively payload-sensitive" (this step) is
itself a proved object, not prose.

The step keeps the counter fixed and strictly decreases the PAYLOAD
(`lhs (n, s) := (n, s+1)`, `rhs := (n, s)`). The payload projection `μ = .2`
orients it; but any counter/base-only (payload-blind) measure is constant on
this step, so none can orient it.

## Audit slots

```
Relation: concrete `RDRSStep Unit Nat Nat (Nat × Nat)` (root single-step).
Closure:  root single-step orientation.
Trust:    kernel-only.
Scope:    the single payload-decreasing counterexample step.
```
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.InformationalIncompleteness.SharpnessCounterexample

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity

/-- A payload-decreasing RDRS step on `Nat × Nat`: the counter (first coordinate)
is fixed and the payload (second coordinate) strictly decreases. This step has NO
payload erasure: the payload carries the descent. -/
def payloadDecreasingStep : RDRSStep Unit Nat Nat (Nat × Nat) where
  lhs _ s n := (n, s + 1)
  rhs _ s n := (n, s)

/-- The payload-projection measure (`μ (c, p) = p`) with the standard well-founded
`<` on `Nat`. -/
def payloadDecreasingMeasure : SemanticMeasureData (Nat × Nat) where
  A := Nat
  ltA := (· < ·)
  wf_ltA := Nat.lt_wfRel.wf
  μ := fun p => p.2

/--
Proves: the payload-projection measure orients the payload-decreasing step
  (`s < s + 1` on every step).
Does not prove: anything about the recursor.
Relation: `payloadDecreasingStep` root single-step.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: this step.
-/
theorem payloadDecreasing_orients :
    Orients payloadDecreasingStep payloadDecreasingMeasure.μ payloadDecreasingMeasure.ltA :=
  fun _ s _ => Nat.lt_succ_self s

/--
Proves: the payload-projection measure on the payload-decreasing step is NOT
  counter-dominated: no counter/base-only (payload-blind) measure orients this
  step, because such a measure is constant across the payload and the counter is
  fixed, so it cannot strictly decrease.
Does not prove: that no measure whatsoever orients it (the payload measure does);
  only that no PAYLOAD-BLIND one does.
Relation: `payloadDecreasingStep` root single-step.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: this step.
-/
theorem payloadDecreasing_not_counter_dominated :
    ¬ CounterDominated payloadDecreasingStep payloadDecreasingMeasure := by
  rintro ⟨μc, _hL, hR, hO⟩
  -- payload-blindness collapses `μc (lhs)` and `μc (rhs)` on this step
  have hcollapse : μc (payloadDecreasingStep.lhs () 0 0)
      = μc (payloadDecreasingStep.rhs () 0 0) := by
    have e1 : payloadDecreasingStep.lhs () 0 0
        = payloadDecreasingStep.rhs () 1 0 := rfl
    rw [e1]
    exact hR () 1 0 0
  have ho := hO () 0 0
  rw [hcollapse] at ho
  exact absurd ho (Nat.lt_irrefl _)

/--
Proves: the SHARPNESS theorem (boundary-as-theorem). There is an RDRS step and a
  semantic measure that orients it but is NOT counter-dominated. Hence the
  `PayloadErasure` hypothesis of
  `RDRSSemanticArbitraryClassifier.orienting_measure_counter_dominated_of_payload_erasure`
  is necessary: dropping it makes the counter-domination conclusion false. The
  recursor sits on the counter-dominated side; this step on the decisive side.
Does not prove: a classification of which steps have erasures; one witness suffices.
Relation: `payloadDecreasingStep` root single-step.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: existence of one counterexample step + measure.
-/
theorem payloadErasure_hypothesis_necessary :
    ∃ (R : RDRSStep Unit Nat Nat (Nat × Nat)) (M : SemanticMeasureData (Nat × Nat)),
      Orients R M.μ M.ltA ∧ ¬ CounterDominated R M :=
  ⟨payloadDecreasingStep, payloadDecreasingMeasure,
    payloadDecreasing_orients, payloadDecreasing_not_counter_dominated⟩

/-- Audit anchor for the sharpness counterexample. -/
def sharpness_counterexample_anchor : String :=
  "OperatorKO7.Meta.InformationalIncompleteness.SharpnessCounterexample.payloadErasure_hypothesis_necessary"

end OperatorKO7.Meta.InformationalIncompleteness.SharpnessCounterexample
