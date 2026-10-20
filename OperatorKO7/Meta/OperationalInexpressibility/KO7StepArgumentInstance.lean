import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
import OperatorKO7.Meta.SchemaOperationalIncompleteness

/-!
# The KO7 operational boundary at the step-argument dimension

This module instantiates the schema-generic `OperationallyIncomplete`
predicate on the reflected direct-measure grammar.  The chosen dimension is
the payload coordinate, which is the numerical image of the recursor's step
argument `pi_y`.  The target is genuine global orientation of the complete
fixed-carrier step relation.  That relation consists of every positive
payload-duplicating counter drop, so global orientation is proved equivalent
to the earlier root-obstruction predicate `OrientsDupStep` rather than being
silently replaced by it.

Every grammar expression is admitted by a recursively constructed indexed
derivation tree.  Derivability is therefore proof-bearing rather than the
constant proposition `True`.  The two semantic predicates are not stipulated
constants:

* `UsesPayload` detects dependence on the step-argument coordinate;
* `AdequateForDupOrientation` is strict orientation of the duplicating step.

The payload projection witnesses dimension use without orientation, while the
counter projection witnesses orientation without dimension use.  Hence the
operational-incompleteness theorem is non-vacuous on both sides.

Relation: all steps of `fixedDuplicatingCarrierSystem.Step`, definitionally
  `FixedDuplicatingCarrierStep`.
Closure: global orientation of the complete root relation.
Strategy: not applicable.
Trust: targeted kernel elaboration and explicit axiom audit passed on
  2026-08-02; the dated Tier-17B receipt records the exact trust surface.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.KO7StepArgumentInstance

open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-! ## Exact carrier, dimension, and duplicating relation -/

/-- The numerical step-argument projection `pi_y` on the canonical
`(counter, payload)` carrier. -/
def stepArgumentProjection (state : Nat × Nat) : Nat :=
  state.2

/-- The fixed root duplicating transition: the counter decreases by one while
a positive copy of the step-argument payload is added. -/
def FixedDuplicatingCarrierStep
    (before after : Nat × Nat) : Prop :=
  exists counter payload copiedPayload,
    1 ≤ copiedPayload ∧
      before = (counter + 1, payload) ∧
      after = (counter, payload + copiedPayload)

/-- Evaluation of a reflected direct measure on the canonical carrier. -/
def evalOnCarrier (e : MeasureExpr) (state : Nat × Nat) : Nat :=
  e.eval state.1 state.2

/-- Schema operations on the canonical `(counter, payload)` carrier.  The
wrapper copies a strictly positive payload amount, `payloadState.2 + 1`, into
the recursive result. -/
def fixedDuplicatingCarrierSchema : StepDuplicatingSchema where
  T := Nat × Nat
  base := (0, 0)
  succ := fun state => (state.1 + 1, state.2)
  wrap := fun payloadState recursiveState =>
    (recursiveState.1, recursiveState.2 + (payloadState.2 + 1))
  recur := fun _baseState _payloadState counterState => counterState

/-- The complete fixed-carrier system.  Its global relation is not a singled
out edge: it contains every positive payload-copy transition described by
`FixedDuplicatingCarrierStep`. -/
def fixedDuplicatingCarrierSystem : StepDuplicatingSystem where
  toStepDuplicatingSchema := fixedDuplicatingCarrierSchema
  Step := FixedDuplicatingCarrierStep
  dup_step := by
    intro baseState payloadState counterState
    refine ⟨counterState.1, counterState.2, payloadState.2 + 1, ?_, rfl, rfl⟩
    exact Nat.succ_le_succ (Nat.zero_le payloadState.2)

/-- The complete carrier relation is inhabited by its smallest positive-copy
edge. -/
theorem fixedDuplicatingCarrierSystem_step_nonempty :
    ∃ before after,
      fixedDuplicatingCarrierSystem.Step before after :=
  ⟨(1, 0), (0, 1), 0, 0, 1, by decide, rfl, rfl⟩

/-- Paper-facing target predicate: the reflected expression globally orients
every step of the complete fixed-carrier system. -/
def GloballyOrientsFixedDuplicatingCarrier (e : MeasureExpr) : Prop :=
  GlobalOrients fixedDuplicatingCarrierSystem (evalOnCarrier e) (fun x y => x < y)

/-- The grammar's payload expression is literally the `pi_y` projection. -/
theorem payload_eval_eq_stepArgumentProjection (state : Nat × Nat) :
    evalOnCarrier MeasureExpr.payload state = stepArgumentProjection state :=
  rfl

/-- `AdequateForDupOrientation` is exactly strict decrease along the explicit
fixed root duplicating transition above. -/
theorem adequateForDupOrientation_iff_fixedCarrierStep
    (e : MeasureExpr) :
    AdequateForDupOrientation e ↔
      forall before after,
        FixedDuplicatingCarrierStep before after →
          evalOnCarrier e after < evalOnCarrier e before := by
  constructor
  · intro hOrients before after hStep
    obtain ⟨counter, payload, copiedPayload, hPositive, rfl, rfl⟩ := hStep
    exact hOrients counter payload copiedPayload hPositive
  · intro hStep counter payload copiedPayload hPositive
    exact hStep (counter + 1, payload) (counter, payload + copiedPayload)
      ⟨counter, payload, copiedPayload, hPositive, rfl, rfl⟩

/-- The global target is exactly the earlier duplicating-root predicate because
the system's whole relation is `FixedDuplicatingCarrierStep`.  This is the
explicit adapter that lets the root obstruction discharge a genuinely global
orientation question. -/
theorem globallyOrientsFixedDuplicatingCarrier_iff_adequateForDupOrientation
    (e : MeasureExpr) :
    GloballyOrientsFixedDuplicatingCarrier e ↔
      AdequateForDupOrientation e := by
  constructor
  · intro hGlobal counter payload copiedPayload hPositive
    have hStep : fixedDuplicatingCarrierSystem.Step
        (counter + 1, payload) (counter, payload + copiedPayload) := by
      change FixedDuplicatingCarrierStep
        (counter + 1, payload) (counter, payload + copiedPayload)
      exact ⟨counter, payload, copiedPayload, hPositive, rfl, rfl⟩
    exact hGlobal hStep
  · intro hRoot before after hStep
    change FixedDuplicatingCarrierStep before after at hStep
    exact
      (adequateForDupOrientation_iff_fixedCarrierStep e).1 hRoot
        before after hStep

/-- The payload-blind counter projection globally orients every step of the
complete carrier relation.  Hence the target predicate is inhabited. -/
theorem counter_globallyOrientsFixedDuplicatingCarrier :
    GloballyOrientsFixedDuplicatingCarrier MeasureExpr.counter :=
  (globallyOrientsFixedDuplicatingCarrier_iff_adequateForDupOrientation
    MeasureExpr.counter).2 counter_adequateForDupOrientation

/-- The payload projection fails the genuine global target. -/
theorem payload_not_globallyOrientsFixedDuplicatingCarrier :
    ¬ GloballyOrientsFixedDuplicatingCarrier MeasureExpr.payload := by
  intro hGlobal
  exact payload_not_adequateForDupOrientation
    ((globallyOrientsFixedDuplicatingCarrier_iff_adequateForDupOrientation
      MeasureExpr.payload).1 hGlobal)

/-- The step-argument dimension is present exactly when the direct grammar
contains a measure whose denotation is not payload-blind. -/
def StepArgumentDimensionPresent : Prop :=
  exists e : MeasureExpr, UsesPayload e

/-- The canonical operational question at `pi_y`.  Its statements are all
reflected direct-grammar expressions, its dimension predicate is genuine
payload dependence, and its target predicate is global orientation of the
complete fixed-carrier relation. -/
def ko7StepArgumentQuestion : OperationalQuestion MeasureExpr where
  derivable := DirectGrammarDerivable
  dependsOnDimension := UsesPayload
  constrainsTarget := GloballyOrientsFixedDuplicatingCarrier
  dimensionPresent := StepArgumentDimensionPresent

/-- The question's derivability field is definitionally the existence of a
typed direct-grammar formation derivation. -/
theorem derivable_iff_typedDirectGrammarDerivation (e : MeasureExpr) :
    ko7StepArgumentQuestion.derivable e ↔
      Nonempty (DirectGrammarDerivation e) :=
  Iff.rfl

/-- Every expression in the declared reflected grammar has a recursively
constructed formation derivation.  Thus the boundary theorem covers the whole
grammar without replacing membership evidence by `True`. -/
theorem every_directGrammar_claim_derivable (e : MeasureExpr) :
    ko7StepArgumentQuestion.derivable e :=
  directGrammarDerivable_complete e

/-- Explicit typed derivation witness for the payload projection used on the
blocked side of the separation. -/
def payload_directGrammarDerivation :
    DirectGrammarDerivation MeasureExpr.payload :=
  .payload

/-- Explicit typed derivation witness for the counter projection used on the
orienting side of the separation. -/
def counter_directGrammarDerivation :
    DirectGrammarDerivation MeasureExpr.counter :=
  .counter

/-- The declared dimension is genuinely present, witnessed by the payload
projection. -/
theorem ko7StepArgument_dimensionPresent :
    ko7StepArgumentQuestion.dimensionPresent :=
  ⟨MeasureExpr.payload, payload_usesPayload⟩

/-- The dimension predicate is definitionally the semantic payload-use
predicate, not a constant placeholder. -/
theorem dependsOnDimension_iff_usesPayload (e : MeasureExpr) :
    ko7StepArgumentQuestion.dependsOnDimension e ↔ UsesPayload e :=
  Iff.rfl

/-- The target predicate is definitionally global orientation of every step in
the complete fixed-carrier system. -/
theorem constrainsTarget_iff_globalOrientation (e : MeasureExpr) :
    ko7StepArgumentQuestion.constrainsTarget e ↔
      GloballyOrientsFixedDuplicatingCarrier e :=
  Iff.rfl

/-- Compatibility bridge to the exact root predicate.  The equality of scopes
comes from the system definition, not from weakening the global target. -/
theorem constrainsTarget_iff_orientsDupStep (e : MeasureExpr) :
    ko7StepArgumentQuestion.constrainsTarget e ↔ OrientsDupStep e.eval :=
  globallyOrientsFixedDuplicatingCarrier_iff_adequateForDupOrientation e

/-- Both semantic predicates are nonconstant.  `payload` uses `pi_y` but is
blocked, whereas `counter` ignores `pi_y` but orients the duplicating step. -/
theorem ko7StepArgument_predicates_nonconstant :
    (exists e, ko7StepArgumentQuestion.dependsOnDimension e) ∧
      (exists e, Not (ko7StepArgumentQuestion.dependsOnDimension e)) ∧
      (exists e, ko7StepArgumentQuestion.constrainsTarget e) ∧
      (exists e, Not (ko7StepArgumentQuestion.constrainsTarget e)) := by
  refine ⟨⟨MeasureExpr.payload, payload_usesPayload⟩, ?_⟩
  refine ⟨⟨MeasureExpr.counter, counter_not_usesPayload⟩, ?_⟩
  refine ⟨⟨MeasureExpr.counter, counter_globallyOrientsFixedDuplicatingCarrier⟩, ?_⟩
  exact ⟨MeasureExpr.payload, payload_not_globallyOrientsFixedDuplicatingCarrier⟩

/-- Per-statement two-sided boundary.  A claim that reads `pi_y` cannot
orient the duplicating step; a semantically payload-blind claim does not read
`pi_y`.  The derivability premise records that the statement belongs to the
declared question, although every reflected expression is derivable here. -/
theorem derivable_claim_stepArgument_boundary
    (e : MeasureExpr) (hDerivable : ko7StepArgumentQuestion.derivable e) :
    (ko7StepArgumentQuestion.dependsOnDimension e →
        Not (ko7StepArgumentQuestion.constrainsTarget e)) ∧
      (PayloadBlind e.eval →
        Not (ko7StepArgumentQuestion.dependsOnDimension e)) := by
  constructor
  · intro hUses hGlobal
    exact directGrammarDerivable_no_payload_orientation hDerivable
      ⟨hUses,
        (globallyOrientsFixedDuplicatingCarrier_iff_adequateForDupOrientation
          e).1 hGlobal⟩
  · intro hBlind hUses
    exact hUses hBlind

/-- Canonical non-vacuous operational-incompleteness instance at the genuine
step-argument dimension.  It quantifies over the full reflected direct grammar
and is discharged by the grammar barrier, not by constant predicates. -/
theorem ko7StepArgument_operationallyIncomplete :
    OperationallyIncomplete ko7StepArgumentQuestion := by
  refine ⟨ko7StepArgument_dimensionPresent, ?_⟩
  intro e hDerivable
  intro hBoth
  exact directGrammarDerivable_no_payload_orientation hDerivable
    ⟨hBoth.1,
      (globallyOrientsFixedDuplicatingCarrier_iff_adequateForDupOrientation
        e).1 hBoth.2⟩

end OperatorKO7.Meta.OperationalInexpressibility.KO7StepArgumentInstance
