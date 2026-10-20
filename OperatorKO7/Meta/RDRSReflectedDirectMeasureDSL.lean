import OperatorKO7.Meta.RDRSSemanticArbitraryClassifier

set_option autoImplicit false

/-!
# Reflected Direct-Measure DSL For RDRS

Computable classifier over an owned syntax for direct additive
measures on the canonical counter/payload carrier.

This is the theorem-safe substitute for "source-code inspection of
arbitrary Lean functions": classify reflected syntax, interpret it,
and prove soundness for the interpreted semantic measure.

## Audit slots

```text
Relation: counterFirstLexRaw_R on Nat x Nat.
Closure: root single-step orientation only.
Strategy: not applicable.
Trust: kernel plus whitelisted Lean foundations inventoried by `#print axioms`.
Scope: reflected additive Nat expressions generated below. This does
       not inspect arbitrary Lean function bodies.
```
-/

namespace OperatorKO7.RDRSReflectedDirectMeasureDSL

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticLensPump
open OperatorKO7.RDRSSemanticNormalizedRawSyntax
open OperatorKO7.RDRSSemanticArbitraryClassifier

/-! ## Reflected syntax -/

/--
Proves: reflected additive direct-measure syntax over the canonical
counter/payload carrier.
Does not prove: coverage of arbitrary Lean functions.
Relation: syntax only.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel plus whitelisted Lean foundations inventoried by `#print axioms`.
Scope: constants, counter, payload, and addition.
-/
inductive NatMeasureExpr where
  | const (k : Nat)
  | counter
  | payload
  | add (x y : NatMeasureExpr)
  deriving DecidableEq, Repr

/-- Counter coefficient of a reflected additive expression. -/
def NatMeasureExpr.counterCoeff : NatMeasureExpr → Nat
  | .const _ => 0
  | .counter => 1
  | .payload => 0
  | .add x y => x.counterCoeff + y.counterCoeff

/-- Payload coefficient of a reflected additive expression. -/
def NatMeasureExpr.payloadCoeff : NatMeasureExpr → Nat
  | .const _ => 0
  | .counter => 0
  | .payload => 1
  | .add x y => x.payloadCoeff + y.payloadCoeff

/-- Constant coefficient of a reflected additive expression. -/
def NatMeasureExpr.constCoeff : NatMeasureExpr → Nat
  | .const k => k
  | .counter => 0
  | .payload => 0
  | .add x y => x.constCoeff + y.constCoeff

/--
Interprets reflected syntax as its coefficient-normalized Nat-valued
function on `(counter, payload)`.
-/
def NatMeasureExpr.eval (e : NatMeasureExpr) (p : Nat × Nat) : Nat :=
  e.counterCoeff * p.fst + e.payloadCoeff * p.snd + e.constCoeff

/--
Proves: the interpreter is exactly the linear form determined by the
three computable coefficients.
Does not prove: anything for expressions outside this DSL.
Relation: evaluation identity on `Nat x Nat`.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel plus whitelisted Lean foundations inventoried by `#print axioms`.
Scope: every reflected expression.
-/
theorem NatMeasureExpr.eval_eq_linear (e : NatMeasureExpr)
    (p : Nat × Nat) :
    e.eval p =
      e.counterCoeff * p.fst + e.payloadCoeff * p.snd + e.constCoeff := by
  rfl

/-! ## Semantic measure and computable labels -/

/-- Semantic measure data interpreted from reflected syntax. -/
def reflectedMeasureData (e : NatMeasureExpr) :
    SemanticMeasureData (Nat × Nat) where
  A := Nat
  ltA := fun a b => a < b
  wf_ltA := Nat.lt_wfRel.wf
  μ := e.eval

/-- Productive labels for the computable reflected classifier. -/
inductive ReflectedMeasureLabel where
  | counterDominatedOrientation
  | payloadSensitiveBlocked
  | payloadBlindNotOrienting
  deriving DecidableEq, Repr

/--
Computable classifier over reflected syntax.

`counterCoeff > 0` gives counter-dominated orientation; zero counter
coefficient gives no orientation. The payload coefficient separates
payload-sensitive blocked from payload-blind non-orientation.
-/
def reflectedClassify (e : NatMeasureExpr) : ReflectedMeasureLabel :=
  if e.counterCoeff = 0 then
    if e.payloadCoeff = 0 then
      .payloadBlindNotOrienting
    else
      .payloadSensitiveBlocked
  else
    .counterDominatedOrientation

/-! ## Soundness helpers -/

theorem reflected_eval_payload_blind_of_payloadCoeff_zero
    (e : NatMeasureExpr) (hPayload : e.payloadCoeff = 0)
    (c p p' : Nat) :
    e.eval (c, p) = e.eval (c, p') := by
  rw [e.eval_eq_linear (c, p), e.eval_eq_linear (c, p')]
  rw [hPayload]
  simp

theorem reflected_eval_step_equal_of_counterCoeff_zero
    (e : NatMeasureExpr) (hCounter : e.counterCoeff = 0)
    (s n : Nat) :
    e.eval (counterFirstLexRaw_R.rhs () s n) =
      e.eval (counterFirstLexRaw_R.lhs () s n) := by
  rw [e.eval_eq_linear (counterFirstLexRaw_R.rhs () s n),
    e.eval_eq_linear (counterFirstLexRaw_R.lhs () s n)]
  rw [hCounter]
  simp [counterFirstLexRaw_R]

theorem reflected_payload_sensitive_of_payloadCoeff_pos
    (e : NatMeasureExpr) (hPayload : e.payloadCoeff ≠ 0) :
    PayloadSensitiveRaw counterFirstLexRaw_R (reflectedMeasureData e) := by
  refine ⟨(), 0, 1, 0, ?_⟩
  intro h
  have hEq : e.eval (counterFirstLexRaw_R.lhs () 0 0) =
      e.eval (counterFirstLexRaw_R.lhs () 1 0) := h
  rw [e.eval_eq_linear (counterFirstLexRaw_R.lhs () 0 0),
    e.eval_eq_linear (counterFirstLexRaw_R.lhs () 1 0)] at hEq
  simp [counterFirstLexRaw_R, Nat.add_assoc] at hEq
  exact hPayload hEq

theorem reflected_payload_blind_of_payloadCoeff_zero
    (e : NatMeasureExpr) (hPayload : e.payloadCoeff = 0) :
    ¬ PayloadSensitiveRaw counterFirstLexRaw_R (reflectedMeasureData e) := by
  rintro ⟨_, s, s', n, h⟩
  exact h (reflected_eval_payload_blind_of_payloadCoeff_zero e hPayload
    (n + 1) s s')

theorem reflected_no_orients_of_counterCoeff_zero
    (e : NatMeasureExpr) (hCounter : e.counterCoeff = 0) :
    ¬ Orients counterFirstLexRaw_R (reflectedMeasureData e).μ
        (reflectedMeasureData e).ltA := by
  intro hOrient
  have hEq := reflected_eval_step_equal_of_counterCoeff_zero e hCounter 0 0
  have hLt := hOrient () 0 0
  change e.eval (counterFirstLexRaw_R.rhs () 0 0) <
    e.eval (counterFirstLexRaw_R.lhs () 0 0) at hLt
  rw [hEq] at hLt
  exact Nat.lt_irrefl _ hLt

theorem reflected_lens_pump_of_counterCoeff_zero
    (e : NatMeasureExpr) (hCounter : e.counterCoeff = 0) :
    SemanticLensPumpWitness counterFirstLexRaw_R (reflectedMeasureData e) := by
  refine ⟨(), 0, 0, ?_⟩
  intro hLt
  have hEq := reflected_eval_step_equal_of_counterCoeff_zero e hCounter 0 0
  change e.eval (counterFirstLexRaw_R.rhs () 0 0) <
    e.eval (counterFirstLexRaw_R.lhs () 0 0) at hLt
  rw [hEq] at hLt
  exact Nat.lt_irrefl _ hLt

theorem reflected_orients_of_counterCoeff_pos
    (e : NatMeasureExpr) (hCounter : e.counterCoeff ≠ 0) :
    Orients counterFirstLexRaw_R (reflectedMeasureData e).μ
    (reflectedMeasureData e).ltA := by
  intro b s n
  cases b
  change e.eval (counterFirstLexRaw_R.rhs () s n) <
    e.eval (counterFirstLexRaw_R.lhs () s n)
  rw [e.eval_eq_linear (counterFirstLexRaw_R.rhs () s n),
    e.eval_eq_linear (counterFirstLexRaw_R.lhs () s n)]
  simp [counterFirstLexRaw_R]
  have hPos : 0 < e.counterCoeff := Nat.pos_of_ne_zero hCounter
  have hMul : e.counterCoeff * n <
      e.counterCoeff * (n + 1) :=
    Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self n) hPos
  exact hMul

theorem reflected_counter_dominated_of_counterCoeff_pos
    (e : NatMeasureExpr) (hCounter : e.counterCoeff ≠ 0) :
    CounterDominated counterFirstLexRaw_R (reflectedMeasureData e) :=
  orienting_measure_counter_dominated_of_payload_erasure
    counterFirstLexPayloadErasure (reflectedMeasureData e)
    (reflected_orients_of_counterCoeff_pos e hCounter)

/-! ## Classifier soundness -/

/--
Proves: every expression classified as counter-dominated really
orients and is counter-dominated.
Does not prove: anything outside the reflected DSL.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel plus whitelisted Lean foundations inventoried by `#print axioms`.
Scope: reflected additive expressions.
-/
theorem reflectedClassify_counter_sound
    (e : NatMeasureExpr)
    (h : reflectedClassify e =
      ReflectedMeasureLabel.counterDominatedOrientation) :
    Orients counterFirstLexRaw_R (reflectedMeasureData e).μ
        (reflectedMeasureData e).ltA ∧
      CounterDominated counterFirstLexRaw_R (reflectedMeasureData e) := by
  unfold reflectedClassify at h
  by_cases hCounter : e.counterCoeff = 0
  · by_cases hPayload : e.payloadCoeff = 0
    · simp [hCounter, hPayload] at h
    · simp [hCounter, hPayload] at h
  · exact ⟨reflected_orients_of_counterCoeff_pos e hCounter,
      reflected_counter_dominated_of_counterCoeff_pos e hCounter⟩

/--
Proves: every expression classified as payload-sensitive blocked is
payload-sensitive and cannot orient.
Does not prove: anything outside the reflected DSL.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel plus whitelisted Lean foundations inventoried by `#print axioms`.
Scope: reflected additive expressions.
-/
theorem reflectedClassify_payload_blocked_sound
    (e : NatMeasureExpr)
    (h : reflectedClassify e =
      ReflectedMeasureLabel.payloadSensitiveBlocked) :
    PayloadSensitiveRaw counterFirstLexRaw_R (reflectedMeasureData e) ∧
      ¬ Orients counterFirstLexRaw_R (reflectedMeasureData e).μ
        (reflectedMeasureData e).ltA := by
  unfold reflectedClassify at h
  by_cases hCounter : e.counterCoeff = 0
  · by_cases hPayload : e.payloadCoeff = 0
    · simp [hCounter, hPayload] at h
    · exact ⟨reflected_payload_sensitive_of_payloadCoeff_pos e hPayload,
        reflected_no_orients_of_counterCoeff_zero e hCounter⟩
  · simp [hCounter] at h

/--
Proves: every expression classified as payload-blind not-orienting is
payload-blind and cannot orient.
Does not prove: anything outside the reflected DSL.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel plus whitelisted Lean foundations inventoried by `#print axioms`.
Scope: reflected additive expressions.
-/
theorem reflectedClassify_payload_blind_sound
    (e : NatMeasureExpr)
    (h : reflectedClassify e =
      ReflectedMeasureLabel.payloadBlindNotOrienting) :
    ¬ PayloadSensitiveRaw counterFirstLexRaw_R (reflectedMeasureData e) ∧
      ¬ Orients counterFirstLexRaw_R (reflectedMeasureData e).μ
        (reflectedMeasureData e).ltA := by
  unfold reflectedClassify at h
  by_cases hCounter : e.counterCoeff = 0
  · by_cases hPayload : e.payloadCoeff = 0
    · exact ⟨reflected_payload_blind_of_payloadCoeff_zero e hPayload,
        reflected_no_orients_of_counterCoeff_zero e hCounter⟩
    · simp [hCounter, hPayload] at h
  · simp [hCounter] at h

/--
Proves: the reflected classifier is total over the closed DSL labels.
Does not prove: source-code inspection of arbitrary Lean functions.
Relation: reflected syntax.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel plus whitelisted Lean foundations inventoried by `#print axioms`.
Scope: every reflected expression.
-/
theorem reflectedClassify_total (e : NatMeasureExpr) :
    reflectedClassify e = ReflectedMeasureLabel.counterDominatedOrientation ∨
      reflectedClassify e = ReflectedMeasureLabel.payloadSensitiveBlocked ∨
        reflectedClassify e = ReflectedMeasureLabel.payloadBlindNotOrienting := by
  unfold reflectedClassify
  by_cases hCounter : e.counterCoeff = 0
  · by_cases hPayload : e.payloadCoeff = 0
    · exact Or.inr (Or.inr (by simp [hCounter, hPayload]))
    · exact Or.inr (Or.inl (by simp [hCounter, hPayload]))
  · exact Or.inl (by simp [hCounter])

/-- Audit anchor for the reflected DSL classifier. -/
def rdrs_reflected_direct_measure_dsl_anchor : String :=
  "OperatorKO7.RDRSReflectedDirectMeasureDSL.reflectedClassify_total"

end OperatorKO7.RDRSReflectedDirectMeasureDSL
