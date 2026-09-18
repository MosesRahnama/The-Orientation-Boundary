import OperatorKO7.Meta.SafeStep.SafeStepConfessionBridge
import OperatorKO7.Meta.OperationalInexpressibility.KO7StepArgumentInstance
import OperatorKO7.Meta.InformationalIncompleteness.ForcedTrilemma

/-!
# Cross-axis confession constructor

This module supplies the missing termination-side evidence for the cross-axis
comparison.  The evidence is the payload constructor of the reflected direct
grammar on the exact fixed carrier-level duplicating relation.  It genuinely
reads the step argument, changes on a concrete duplicating edge, and is blocked
from orienting that relation by the direct-grammar theorem.  The payload
projection is packaged as semantic measure data, and a counter-plus-payload
measure containing that exact projection is passed through the forced-output
theorem on `iiRecursor` with both positive conjuncts inhabited.

These are two relation-local receipts over two explicit measure functions, not
a relation transport: `iiRecursor` preserves payload, whereas
`FixedDuplicatingCarrierStep` increases it.  The common-witness theorem below
keeps both relations explicit and the direct-grammar refusal independent.

The resulting semantic classifier and the concrete SafeStep classifier both
emit `T3_confession`.  The comparison is deliberately constructor-level only:
their four payload fields differ, and a separate theorem proves that the full
typed outputs are unequal.

Relation: `FixedDuplicatingCarrierStep` on the termination axis; `Step` versus
  `SafeStep` on the confluence axis.
Closure: root single-step on both axes.
Strategy: not applicable.
Trust: targeted kernel elaboration and explicit axiom audit passed on
  2026-08-02; the dated Tier-17B receipt records the exact trust surface.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.SafeStep.CrossAxisConfession

open OperatorKO7.MetaHalt.Predicate
open OperatorKO7.Meta.BoundaryGeneral.DirectMeasureGrammarClosure
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.OperationalInexpressibility.KO7StepArgumentInstance
open OperatorKO7.Meta.SafeStep.SafeStepConfessionBridge
open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity

/-- Canonical termination-axis expression: the payload projection in the exact
reflected direct grammar used by the step-argument boundary. -/
def terminationAxisPayloadProjection : MeasureExpr :=
  .payload

/-- Decisive support at the termination interface would both read `pi_y` and
orient the fixed duplicating relation. -/
def TerminationAxisDecisiveSupport (e : MeasureExpr) : Prop :=
  UsesPayload e ∧ AdequateForDupOrientation e

/-! ## One payload projection, two relation-local refusal receipts -/

/-- Semantic measure data whose measure function is exactly the actual
step-argument projection used by the reflected direct grammar. -/
def terminationAxisPayloadMeasure : SemanticMeasureData (Nat × Nat) where
  A := Nat
  ltA := (· < ·)
  wf_ltA := Nat.lt_wfRel.wf
  μ := stepArgumentProjection

/-- The semantic measure and reflected expression are pointwise the same
payload projection on the shared `(counter, payload)` carrier. -/
theorem terminationAxisPayloadMeasure_mu_eq_reflectedProjection
    (state : Nat × Nat) :
    terminationAxisPayloadMeasure.μ state =
      evalOnCarrier terminationAxisPayloadProjection state :=
  rfl

/-- The common measure genuinely reads the step argument on `iiRecursor`:
changing the payload at a fixed counter changes the measured LHS. -/
theorem terminationAxisPayloadMeasure_rawSensitive_iiRecursor :
    PayloadSensitiveRaw
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
      terminationAxisPayloadMeasure := by
  refine ⟨(), 0, 1, 0, ?_⟩
  change (0 : Nat) ≠ 1
  decide

/-- The payload projection cannot orient `iiRecursor`, because that relation
preserves payload.  This is relation-local and is not a claim about the fixed
payload-increasing duplicator. -/
theorem terminationAxisPayloadMeasure_not_orients_iiRecursor :
    ¬ Orients
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
      terminationAxisPayloadMeasure.μ terminationAxisPayloadMeasure.ltA := by
  intro hOrients
  have hZero := hOrients () 0 0
  change (0 : Nat) < 0 at hZero
  exact (Nat.lt_irrefl 0) hZero

/-- Semantic measure whose counter-plus-payload function contains the exact
step-argument projection as its second summand. -/
def terminationAxisCounterPlusPayloadMeasure :
    SemanticMeasureData (Nat × Nat) where
  A := Nat
  ltA := (· < ·)
  wf_ltA := Nat.lt_wfRel.wf
  μ := fun state => state.1 + stepArgumentProjection state

/-- Exact link from the substantive `iiRecursor` witness to the reflected
step-argument projection. -/
theorem terminationAxisCounterPlusPayloadMeasure_mu_eq_projectionSum
    (state : Nat × Nat) :
    terminationAxisCounterPlusPayloadMeasure.μ state =
      state.1 + evalOnCarrier terminationAxisPayloadProjection state :=
  rfl

/-- The counter-plus-payload witness genuinely reads the payload coordinate. -/
theorem terminationAxisCounterPlusPayloadMeasure_rawSensitive_iiRecursor :
    PayloadSensitiveRaw
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
      terminationAxisCounterPlusPayloadMeasure := by
  refine ⟨(), 0, 1, 0, ?_⟩
  change (1 : Nat) ≠ 2
  decide

/-- The counter-plus-payload witness orients the payload-preserving
`iiRecursor` by strict decrease of its counter summand. -/
theorem terminationAxisCounterPlusPayloadMeasure_orients_iiRecursor :
    Orients
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
      terminationAxisCounterPlusPayloadMeasure.μ
      terminationAxisCounterPlusPayloadMeasure.ltA := by
  intro _ payload counter
  change counter + payload < (counter + 1) + payload
  exact Nat.add_lt_add_right (Nat.lt_succ_self counter) payload

/-- The same orienting witness is counter-dominated on `iiRecursor`; this is
the substantive failure of the third decisive-support conjunct. -/
theorem terminationAxisCounterPlusPayloadMeasure_counterDominated_iiRecursor :
    CounterDominated
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
      terminationAxisCounterPlusPayloadMeasure :=
  OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor_orienting_measure_counter_dominated
    terminationAxisCounterPlusPayloadMeasure
    terminationAxisCounterPlusPayloadMeasure_orients_iiRecursor

/-- Legacy `iiRecursor` forced-trilemma theorem instantiated at a non-vacuous
witness: it both orients and reads payload, while counter domination defeats
the third decisive-support conjunct. -/
theorem terminationAxisCounterPlusPayload_forcedTrilemma_noDecisiveSupport :
    ¬ PayloadSensitiveDecisive
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
      terminationAxisCounterPlusPayloadMeasure :=
  OperatorKO7.Meta.InformationalIncompleteness.ForcedTrilemma.forced_output_trilemma_no_decisive_support
    terminationAxisCounterPlusPayloadMeasure

/-- Complete substantive `iiRecursor` receipt: the first two decisive-support
conjuncts hold and the third fails through an explicit counter-dominated
alternative. -/
theorem terminationAxisCounterPlusPayload_substantiveNoDecisiveReceipt :
    Orients
        OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
        terminationAxisCounterPlusPayloadMeasure.μ
        terminationAxisCounterPlusPayloadMeasure.ltA ∧
      PayloadSensitiveRaw
        OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
        terminationAxisCounterPlusPayloadMeasure ∧
      CounterDominated
        OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
        terminationAxisCounterPlusPayloadMeasure ∧
      Not (PayloadSensitiveDecisive
        OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
        terminationAxisCounterPlusPayloadMeasure) :=
  ⟨terminationAxisCounterPlusPayloadMeasure_orients_iiRecursor,
    terminationAxisCounterPlusPayloadMeasure_rawSensitive_iiRecursor,
    terminationAxisCounterPlusPayloadMeasure_counterDominated_iiRecursor,
    terminationAxisCounterPlusPayload_forcedTrilemma_noDecisiveSupport⟩

/-- The root-step relation induced by `iiRecursor`.  Its payload coordinate is
preserved from `before` to `after`. -/
def IiRecursorRootStep (before after : Nat × Nat) : Prop :=
  exists payload counter,
    before =
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor.lhs
        () payload counter ∧
    after =
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor.rhs
        () payload counter

/-- Explicit no-transport receipt: the canonical fixed-duplicator edge grows
payload from zero to one, so it is not an `iiRecursor` edge, whose payload is
preserved. -/
theorem fixedDuplicator_actualEdge_not_iiRecursorRootStep :
    FixedDuplicatingCarrierStep (1, 0) (0, 1) ∧
      Not (IiRecursorRootStep (1, 0) (0, 1)) := by
  constructor
  · exact ⟨0, 0, 1, by decide, rfl, rfl⟩
  · rintro ⟨payload, counter, hBefore, hAfter⟩
    change (1, 0) = (counter + 1, payload) at hBefore
    change (0, 1) = (counter, payload) at hAfter
    have hPayloadZero : (0 : Nat) = payload := (Prod.mk.inj hBefore).2
    have hPayloadOne : (1 : Nat) = payload := (Prod.mk.inj hAfter).2
    omega

/-- Independent direct-grammar receipt on the exact fixed duplicating
relation. -/
theorem directGrammar_noDecisiveSupport_fixedDuplicator
    (e : MeasureExpr) :
    Not (TerminationAxisDecisiveSupport e) :=
  no_directGrammar_measure_usesPayload_and_orients e

/-- Exact edge-local refusal event: on the concrete payload-growing edge
`(1, 0) -> (0, 1)`, the payload projection evaluates to one after and zero
before, so the strict-decrease obligation is false. -/
theorem terminationAxis_payloadProjection_actualEdge_not_decreasing :
    Not (
      evalOnCarrier terminationAxisPayloadProjection (0, 1) <
        evalOnCarrier terminationAxisPayloadProjection (1, 0)) := by
  change Not ((1 : Nat) < 0)
  decide

/-- Concrete termination-axis refusal evidence.  It retains the exact payload
projection, the substantive `iiRecursor` third-leg failure, and the independent
relation-specific trilemma refusal on the fixed duplicator. -/
structure TerminationAxisRefusalEvidence : Prop where
  directGrammarMembership :
    ko7StepArgumentQuestion.derivable terminationAxisPayloadProjection
  semanticMeasureMatchesProjection :
    forall state,
      terminationAxisPayloadMeasure.μ state =
        evalOnCarrier terminationAxisPayloadProjection state
  readsStepArgument :
    ko7StepArgumentQuestion.dependsOnDimension
      terminationAxisPayloadProjection
  iiRecursorMeasureIncludesProjection :
    forall state,
      terminationAxisCounterPlusPayloadMeasure.μ state =
        state.1 + evalOnCarrier terminationAxisPayloadProjection state
  rawSensitiveOnIiRecursor :
    PayloadSensitiveRaw
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
      terminationAxisCounterPlusPayloadMeasure
  orientsIiRecursor :
    Orients
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
      terminationAxisCounterPlusPayloadMeasure.μ
      terminationAxisCounterPlusPayloadMeasure.ltA
  counterDominatedOnIiRecursor :
    CounterDominated
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
      terminationAxisCounterPlusPayloadMeasure
  forcedTrilemmaNoDecisiveSupport :
    Not (PayloadSensitiveDecisive
      OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
      terminationAxisCounterPlusPayloadMeasure)
  actualDuplicatingEdge :
    FixedDuplicatingCarrierStep (1, 0) (0, 1)
  stepArgumentChangesOnEdge :
    stepArgumentProjection (1, 0) ≠ stepArgumentProjection (0, 1)
  actualEdgeStrictDecreaseRefused :
    Not (
      evalOnCarrier terminationAxisPayloadProjection (0, 1) <
        evalOnCarrier terminationAxisPayloadProjection (1, 0))
  decisiveSupportRefused :
    Not (TerminationAxisDecisiveSupport terminationAxisPayloadProjection)

/-- The canonical payload projection supplies a real refusal event on the
duplicating carrier.  Its refusal is the actual direct-grammar barrier, never
an enum-exhaustiveness argument. -/
theorem canonicalTerminationAxisRefusalEvidence :
    TerminationAxisRefusalEvidence where
  directGrammarMembership := every_directGrammar_claim_derivable _
  semanticMeasureMatchesProjection :=
    terminationAxisPayloadMeasure_mu_eq_reflectedProjection
  readsStepArgument := payload_usesPayload
  iiRecursorMeasureIncludesProjection :=
    terminationAxisCounterPlusPayloadMeasure_mu_eq_projectionSum
  rawSensitiveOnIiRecursor :=
    terminationAxisCounterPlusPayloadMeasure_rawSensitive_iiRecursor
  orientsIiRecursor :=
    terminationAxisCounterPlusPayloadMeasure_orients_iiRecursor
  counterDominatedOnIiRecursor :=
    terminationAxisCounterPlusPayloadMeasure_counterDominated_iiRecursor
  forcedTrilemmaNoDecisiveSupport :=
    terminationAxisCounterPlusPayload_forcedTrilemma_noDecisiveSupport
  actualDuplicatingEdge :=
    ⟨0, 0, 1, by decide, rfl, rfl⟩
  stepArgumentChangesOnEdge := by decide
  actualEdgeStrictDecreaseRefused :=
    terminationAxis_payloadProjection_actualEdge_not_decreasing
  decisiveSupportRefused :=
    OperatorKO7.Meta.InformationalIncompleteness.ForcedTrilemma.forced_output_trilemma_no_decisive_support_fixedDuplicatingCarrier
      terminationAxisPayloadProjection

/-- Public relation-precision receipt: the refusal evidence contains the
explicit counter-drop, payload-growth edge of the fixed duplicating carrier. -/
theorem terminationAxis_refusal_actualDuplicatingEdge :
    FixedDuplicatingCarrierStep (1, 0) (0, 1) :=
  canonicalTerminationAxisRefusalEvidence.actualDuplicatingEdge

/-- Public actual-event receipt: the canonical payload projection fails strict
decrease on the explicit fixed-duplicator edge stored in the evidence. -/
theorem terminationAxis_refusal_actualEdge_not_decreasing :
    Not (
      evalOnCarrier terminationAxisPayloadProjection (0, 1) <
        evalOnCarrier terminationAxisPayloadProjection (1, 0)) :=
  canonicalTerminationAxisRefusalEvidence.actualEdgeStrictDecreaseRefused

/-- Public refusal receipt at the exact duplicating relation. -/
theorem terminationAxis_payloadProjection_not_decisive :
    ¬ TerminationAxisDecisiveSupport terminationAxisPayloadProjection :=
  canonicalTerminationAxisRefusalEvidence.decisiveSupportRefused

/-- Exact common-witness bridge used by the classifier premise.  The pure
payload measure identifies the reflected projection; the counter-plus-payload
measure has inhabited orientation and raw-sensitivity conjuncts on
`iiRecursor`, but is counter-dominated; and the upstream fixed-duplicator
trilemma supplies the classifier's exact refusal.  No relation transport is
asserted. -/
theorem terminationAxis_commonSemanticRefusalBridge :
    (forall state,
      terminationAxisPayloadMeasure.μ state =
        evalOnCarrier terminationAxisPayloadProjection state) ∧
      (forall state,
        terminationAxisCounterPlusPayloadMeasure.μ state =
          state.1 + evalOnCarrier terminationAxisPayloadProjection state) ∧
      Orients
        OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
        terminationAxisCounterPlusPayloadMeasure.μ
        terminationAxisCounterPlusPayloadMeasure.ltA ∧
      PayloadSensitiveRaw
        OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
        terminationAxisCounterPlusPayloadMeasure ∧
      CounterDominated
        OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
        terminationAxisCounterPlusPayloadMeasure ∧
      Not (PayloadSensitiveDecisive
        OperatorKO7.Meta.InformationalIncompleteness.RecursorPayloadErasure.iiRecursor
        terminationAxisCounterPlusPayloadMeasure) ∧
      Not (
        evalOnCarrier terminationAxisPayloadProjection (0, 1) <
          evalOnCarrier terminationAxisPayloadProjection (1, 0)) ∧
      Not (TerminationAxisDecisiveSupport terminationAxisPayloadProjection) :=
  ⟨canonicalTerminationAxisRefusalEvidence.semanticMeasureMatchesProjection,
    canonicalTerminationAxisRefusalEvidence.iiRecursorMeasureIncludesProjection,
    canonicalTerminationAxisRefusalEvidence.orientsIiRecursor,
    canonicalTerminationAxisRefusalEvidence.rawSensitiveOnIiRecursor,
    canonicalTerminationAxisRefusalEvidence.counterDominatedOnIiRecursor,
    canonicalTerminationAxisRefusalEvidence.forcedTrilemmaNoDecisiveSupport,
    canonicalTerminationAxisRefusalEvidence.actualEdgeStrictDecreaseRefused,
    canonicalTerminationAxisRefusalEvidence.decisiveSupportRefused⟩

/-- Independent semantic premise used by the termination-axis classifier. -/
def HasTerminationAxisRefusal : Prop :=
  Nonempty TerminationAxisRefusalEvidence

/-- The concrete direct-measure evidence inhabits the classifier premise. -/
theorem terminationAxis_hasRefusal : HasTerminationAxisRefusal :=
  ⟨canonicalTerminationAxisRefusalEvidence⟩

/-- Termination-side semantic classifier.  A proof-carrying direct-measure
refusal emits confession; absence of such evidence emits typed abstention. -/
noncomputable def terminationAxisSemanticClassifier : TypedOutput := by
  classical
  exact if HasTerminationAxisRefusal then
    .T3_confession
      "DirectGrammarBoundary.payload_not_adequateForDupOrientation"
      "KO7.Termination"
      "pi_y.stepArgument"
      "payloadProjection.decisiveSupportRefused"
  else
    .T4_abstention
      "noTerminationAxisRefusalEvidence"
      ["KO7.Termination"]
      ["T3_confession"]

/-- Positive semantic branch: an actual refusal witness forces the
termination-axis classifier to return `T3_confession`. -/
theorem terminationAxisSemanticClassifier_eq_t3
    (h : HasTerminationAxisRefusal) :
    terminationAxisSemanticClassifier =
      .T3_confession
        "DirectGrammarBoundary.payload_not_adequateForDupOrientation"
        "KO7.Termination"
        "pi_y.stepArgument"
        "payloadProjection.decisiveSupportRefused" := by
  classical
  simp only [terminationAxisSemanticClassifier, if_pos h]

/-- Counterfactual falsifier branch: if refusal evidence were absent the same
classifier would abstain.  Its premise is uninhabited in this module because
`terminationAxis_hasRefusal` proves the canonical evidence exists. -/
theorem terminationAxisSemanticClassifier_eq_t4
    (h : Not HasTerminationAxisRefusal) :
    terminationAxisSemanticClassifier =
      .T4_abstention
        "noTerminationAxisRefusalEvidence"
        ["KO7.Termination"]
        ["T3_confession"] := by
  classical
  simp only [terminationAxisSemanticClassifier, if_neg h]

/-- The actual classifier cannot take its counterfactual T4 branch because the
canonical termination-axis refusal evidence is inhabited. -/
theorem terminationAxisSemanticClassifier_ne_t4 :
    terminationAxisSemanticClassifier ≠
      .T4_abstention
        "noTerminationAxisRefusalEvidence"
        ["KO7.Termination"]
        ["T3_confession"] := by
  rw [terminationAxisSemanticClassifier_eq_t3 terminationAxis_hasRefusal]
  decide

/-- The actual direct-measure refusal event is classified as confession.  The
returned evidence is exactly the canonical evidence object constructed from
the trilemma's no-decisive-support leg. -/
theorem termination_axis_direct_refusal_emits_confession :
    exists E : TerminationAxisRefusalEvidence,
      E = canonicalTerminationAxisRefusalEvidence ∧
        Not (
          evalOnCarrier terminationAxisPayloadProjection (0, 1) <
            evalOnCarrier terminationAxisPayloadProjection (1, 0)) ∧
          terminationAxisSemanticClassifier =
          .T3_confession
            "DirectGrammarBoundary.payload_not_adequateForDupOrientation"
            "KO7.Termination"
            "pi_y.stepArgument"
            "payloadProjection.decisiveSupportRefused" := by
  refine ⟨canonicalTerminationAxisRefusalEvidence, rfl,
    canonicalTerminationAxisRefusalEvidence.actualEdgeStrictDecreaseRefused,
    ?_⟩
  exact terminationAxisSemanticClassifier_eq_t3 terminationAxis_hasRefusal

/-- Cross-axis constructor identity: the concrete SafeStep refusal and the
concrete termination-side direct-measure refusal both emit the outer
`T3_confession` constructor.  This theorem compares no payload fields. -/
theorem confluence_and_termination_refusals_share_t3_constructor :
    IsT3Confession safeStepSemanticClassifier ∧
      IsT3Confession terminationAxisSemanticClassifier := by
  obtain ⟨_safeEvidence, _hRetained, hSafe⟩ :=
    safestep_guard_emits_confession concreteSafeStepEvidence
  have hTermination := terminationAxisSemanticClassifier_eq_t3
    terminationAxis_hasRefusal
  constructor
  · rw [hSafe]
    trivial
  · rw [hTermination]
    trivial

/-- The two axes do not emit the same full value: their theorem chains,
framework names, dropped dimensions, and residual tags are different. -/
theorem crossAxis_confession_full_outputs_ne :
    safeStepSemanticClassifier ≠ terminationAxisSemanticClassifier := by
  obtain ⟨_safeEvidence, _hRetained, hSafe⟩ :=
    safestep_guard_emits_confession concreteSafeStepEvidence
  have hTermination := terminationAxisSemanticClassifier_eq_t3
    terminationAxis_hasRefusal
  rw [hSafe, hTermination]
  decide

/-- Headline cross-axis result at its exact strength: shared outer confession
constructor together with explicit failure of full-output identity. -/
theorem crossAxis_confession_same_constructor_not_full_output :
    IsT3Confession safeStepSemanticClassifier ∧
      IsT3Confession terminationAxisSemanticClassifier ∧
      safeStepSemanticClassifier ≠ terminationAxisSemanticClassifier :=
  ⟨confluence_and_termination_refusals_share_t3_constructor.1,
    confluence_and_termination_refusals_share_t3_constructor.2,
    crossAxis_confession_full_outputs_ne⟩

end OperatorKO7.Meta.SafeStep.CrossAxisConfession
