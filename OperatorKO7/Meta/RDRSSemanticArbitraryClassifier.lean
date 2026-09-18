import OperatorKO7.Meta.RDRSSemanticNormalizedRawSyntax

set_option autoImplicit false

/-!
# RDRS Semantic Arbitrary-Function Classifier

This module states semantic theorems over arbitrary
`SemanticMeasureData` values rather than inspecting the source syntax of
Lean functions.

The key lemma is payload-erasure dominance: if an RDRS step admits a
static erasure map that replaces the payload by one neutral payload,
then every orienting semantic measure is counter-dominated. Therefore every
orienting semantic measure on such a step has a counter-dominated witness,
which contradicts the defined `PayloadSensitiveDecisive` predicate.

## Formal scope

```text
Relation: abstract RDRSStep B S N T; canonical instance is
          counterFirstLexRaw_R on Nat x Nat.
Closure: root single-step orientation only.
Strategy: not applicable.
Trust: kernel-only for the erasure-dominance and no-decisive theorems.
       The optional total classifier uses classical excluded middle
       to split orientation from non-orientation and is marked
       noncomputable.
Scope: arbitrary semantic measure functions in SemanticMeasureData,
       not just the closed RawDirectMeasureShape grammar. This still
       does not inspect source code of Lean functions.
```
-/

namespace OperatorKO7.RDRSSemanticArbitraryClassifier

open OperatorKO7.RDRSDescentLens
open OperatorKO7.RDRSSemanticDirectMeasure
open OperatorKO7.RDRSSemanticPayloadSensitivity
open OperatorKO7.RDRSSemanticLensPump
open OperatorKO7.RDRSSemanticNormalizedRawSyntax

/-! ## 1. Static payload erasure -/

/--
Proves: a payload erasure interface for an abstract RDRS step pair.
The erasure map sends every payload instance of a step to the same
neutral-payload instance.

Does not prove: that every RDRS step has such an erasure. The
canonical counter-first-lex RDRS below provides the concrete witness.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step shape equations.
Strategy: not applicable.
Trust: kernel-only.
Scope: per supplied step pair.
-/
structure PayloadErasure {B S N T : Type} (R : RDRSStep B S N T) where
  erase : T → T
  neutralPayload : S
  lhs_erase : ∀ b s n, erase (R.lhs b s n) = R.lhs b neutralPayload n
  rhs_erase : ∀ b s n, erase (R.rhs b s n) = R.rhs b neutralPayload n

/--
Proves: if a step has a payload-erasure map, every orienting semantic
measure is counter-dominated. The counter-dominated witness is
`M.μ` after erasing the payload.

Does not prove: source-system termination, contextual closure, or
anything outside the supplied root step pair.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `SemanticMeasureData T` and every `PayloadErasure R`.
-/
theorem orienting_measure_counter_dominated_of_payload_erasure
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : PayloadErasure R) (M : SemanticMeasureData T)
    (hOrient : Orients R M.μ M.ltA) :
    CounterDominated R M := by
  refine ⟨fun t => M.μ (E.erase t), ?_, ?_, ?_⟩
  · intro b s s' n
    change M.μ (E.erase (R.lhs b s n)) =
      M.μ (E.erase (R.lhs b s' n))
    rw [E.lhs_erase b s n, E.lhs_erase b s' n]
  · intro b s s' n
    change M.μ (E.erase (R.rhs b s n)) =
      M.μ (E.erase (R.rhs b s' n))
    rw [E.rhs_erase b s n, E.rhs_erase b s' n]
  · intro b s n
    change M.ltA (M.μ (E.erase (R.rhs b s n)))
      (M.μ (E.erase (R.lhs b s n)))
    rw [E.rhs_erase b s n, E.lhs_erase b s n]
    exact hOrient b E.neutralPayload n

/--
Proves: under a payload erasure interface, no arbitrary semantic
measure can be both orienting and decisively payload-sensitive.

Does not prove: that raw payload-sensitive measures cannot mention the
payload. It proves they cannot be decisive if they orient, because the
erased counter-dominated witness also orients.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `SemanticMeasureData T` and every `PayloadErasure R`.
-/
theorem no_decisive_payload_sensitive_of_payload_erasure
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : PayloadErasure R) (M : SemanticMeasureData T) :
    ¬ PayloadSensitiveDecisive R M := by
  rintro ⟨hOrient, _, hNoCounterDominated⟩
  exact hNoCounterDominated
    (orienting_measure_counter_dominated_of_payload_erasure E M hOrient)

/--
Proves: the same no-decisive theorem for certified semantic direct
measures.

Does not prove: syntactic source inspection of the measure function.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `SemanticDirectMeasure T` and every `PayloadErasure R`.
-/
theorem no_direct_decisive_payload_sensitive_of_payload_erasure
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : PayloadErasure R) (M : SemanticDirectMeasure T) :
    ¬ PayloadSensitiveDecisive R M.data :=
  no_decisive_payload_sensitive_of_payload_erasure E M.data

/-! ## 2. Classical total classifier over arbitrary semantic measures -/

/--
Proves: non-orientation gives a concrete semantic lens-pump witness.

Does not prove: computable discovery of the witness. The proof uses a
classical contradiction split over the root-step orientation predicate.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: classical proof search over propositions.
Scope: every `SemanticMeasureData T`.
-/
theorem semantic_lens_pump_witness_of_not_orients
    {B S N T : Type} (R : RDRSStep B S N T)
    (M : SemanticMeasureData T) :
    ¬ Orients R M.μ M.ltA → SemanticLensPumpWitness R M := by
  classical
  intro hNot
  by_cases hWitness : SemanticLensPumpWitness R M
  · exact hWitness
  · exfalso
    apply hNot
    intro b s n
    by_cases hStep : M.ltA (M.μ (R.rhs b s n)) (M.μ (R.lhs b s n))
    · exact hStep
    · exact False.elim (hWitness ⟨b, s, n, hStep⟩)

/--
Proves: if there is no semantic lens-pump witness, the measure orients
the root step.

Does not prove: source-system termination.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: classical proof search over propositions.
Scope: every `SemanticMeasureData T`.
-/
theorem orients_of_no_semantic_lens_pump_witness
    {B S N T : Type} (R : RDRSStep B S N T)
    (M : SemanticMeasureData T) :
    ¬ SemanticLensPumpWitness R M → Orients R M.μ M.ltA := by
  classical
  intro hNoWitness b s n
  by_cases hStep : M.ltA (M.μ (R.rhs b s n)) (M.μ (R.lhs b s n))
  · exact hStep
  · exact False.elim (hNoWitness ⟨b, s, n, hStep⟩)

/--
Proves: exact classification data for an arbitrary semantic measure on
a payload-erasing RDRS step. There is no residual constructor.

Does not prove: that the classifier is computable. The classifier
below is noncomputable because it splits on a proposition.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: constructor data only.
Scope: every `SemanticMeasureData T` once a `PayloadErasure R` is
supplied.
-/
inductive ArbitrarySemanticClassification
    {B S N T : Type} (R : RDRSStep B S N T)
    (M : SemanticMeasureData T) : Type 1 where
  | blockedByLensPump
      (witness : SemanticLensPumpWitness R M)
  | counterDominatedOrientation
      (orientation : Orients R M.μ M.ltA)
      (counter_dominated : CounterDominated R M)

/-- Productive labels for the arbitrary semantic classifier. -/
inductive ArbitrarySemanticLabel where
  | blockedByLensPump
  | counterDominatedOrientation
  deriving DecidableEq, Repr

/--
Proves: label projection for an arbitrary semantic classification.
Does not prove: any new mathematical property beyond the constructor
identity.
Relation: metadata projection.
Closure: not applicable.
Strategy: not applicable.
Trust: kernel-only.
Scope: every arbitrary semantic classification.
-/
def ArbitrarySemanticClassification.label
    {B S N T : Type} {R : RDRSStep B S N T}
    {M : SemanticMeasureData T}
    (C : ArbitrarySemanticClassification R M) :
    ArbitrarySemanticLabel :=
  match C with
  | .blockedByLensPump _ => .blockedByLensPump
  | .counterDominatedOrientation _ _ => .counterDominatedOrientation

/--
Proves: total classifier over arbitrary semantic measure functions for
payload-erasing RDRS steps. The result is either a lens-pump block or
a counter-dominated orientation.

Does not prove: computable source inspection. This is a noncomputable
semantic classifier over propositions.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: classical excluded-middle split on `Orients`.
Scope: every `SemanticMeasureData T` and every `PayloadErasure R`.
-/
noncomputable def classifyArbitrarySemantic
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : PayloadErasure R) (M : SemanticMeasureData T) :
    ArbitrarySemanticClassification R M := by
  classical
  exact
    if hOrient : Orients R M.μ M.ltA then
      .counterDominatedOrientation hOrient
        (orienting_measure_counter_dominated_of_payload_erasure E M hOrient)
    else
      .blockedByLensPump
        (semantic_lens_pump_witness_of_not_orients R M hOrient)

/--
Proves: the arbitrary semantic classifier is total. There is always a
classification inhabitant.

Does not prove: computability of the classification.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: by definition of `classifyArbitrarySemantic`.
Scope: every `SemanticMeasureData T` and every `PayloadErasure R`.
-/
theorem classifyArbitrarySemantic_total
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : PayloadErasure R) (M : SemanticMeasureData T) :
    ∃ C : ArbitrarySemanticClassification R M,
      classifyArbitrarySemantic E M = C := by
  exact ⟨classifyArbitrarySemantic E M, rfl⟩

/--
Proves: the arbitrary semantic classifier has no residual label. It
returns one of the two productive labels.

Does not prove: computability of the label.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: classical split inherited from the classifier.
Scope: every `SemanticMeasureData T` and every `PayloadErasure R`.
-/
theorem classifyArbitrarySemantic_label_total
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : PayloadErasure R) (M : SemanticMeasureData T) :
    (classifyArbitrarySemantic E M).label =
        ArbitrarySemanticLabel.blockedByLensPump ∨
      (classifyArbitrarySemantic E M).label =
        ArbitrarySemanticLabel.counterDominatedOrientation := by
  generalize hC : classifyArbitrarySemantic E M = C
  cases C with
  | blockedByLensPump _ =>
      left
      rfl
  | counterDominatedOrientation _ _ =>
      right
      rfl

/--
Proves: soundness of each arbitrary semantic classification.

Does not prove: source-system termination.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every classification inhabitant.
-/
theorem arbitrarySemanticClassification_sound
    {B S N T : Type} {R : RDRSStep B S N T}
    {M : SemanticMeasureData T}
    (C : ArbitrarySemanticClassification R M) :
    (∃ w : SemanticLensPumpWitness R M,
      C = ArbitrarySemanticClassification.blockedByLensPump w ∧
        ¬ Orients R M.μ M.ltA) ∨
    (∃ (hOrient : Orients R M.μ M.ltA)
        (hCD : CounterDominated R M),
      C = ArbitrarySemanticClassification.counterDominatedOrientation
            hOrient hCD ∧
        Orients R M.μ M.ltA ∧
        CounterDominated R M) := by
  cases C with
  | blockedByLensPump w =>
      exact Or.inl
        ⟨w, rfl, semantic_lens_pump_no_orients R M w⟩
  | counterDominatedOrientation hOrient hCD =>
      exact Or.inr ⟨hOrient, hCD, rfl, hOrient, hCD⟩

/--
Proves: soundness of the total arbitrary semantic classifier.

Does not prove: computable classification.
Relation: abstract `RDRSStep B S N T`.
Closure: root single-step.
Strategy: not applicable.
Trust: combines the noncomputable classifier with kernel soundness of
the two returned constructors.
Scope: every `SemanticMeasureData T` and every `PayloadErasure R`.
-/
theorem classifyArbitrarySemantic_sound
    {B S N T : Type} {R : RDRSStep B S N T}
    (E : PayloadErasure R) (M : SemanticMeasureData T) :
    (∃ w : SemanticLensPumpWitness R M,
      classifyArbitrarySemantic E M =
          ArbitrarySemanticClassification.blockedByLensPump w ∧
        ¬ Orients R M.μ M.ltA) ∨
    (∃ (hOrient : Orients R M.μ M.ltA)
        (hCD : CounterDominated R M),
      classifyArbitrarySemantic E M =
          ArbitrarySemanticClassification.counterDominatedOrientation
            hOrient hCD ∧
        Orients R M.μ M.ltA ∧
        CounterDominated R M) :=
  arbitrarySemanticClassification_sound (classifyArbitrarySemantic E M)

/-! ## 3. Canonical RDRS instance -/

/--
Proves: payload erasure for the canonical counter-first-lex RDRS:
`(counter, payload)` is sent to `(counter, 0)`.

Does not prove: anything about other carriers.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step equations.
Strategy: not applicable.
Trust: kernel-only.
Scope: canonical `Nat x Nat` carrier.
-/
def counterFirstLexPayloadErasure :
    PayloadErasure counterFirstLexRaw_R where
  erase := fun p => (p.fst, 0)
  neutralPayload := 0
  lhs_erase := by intro _ _ _; rfl
  rhs_erase := by intro _ _ _; rfl

/--
Proves: every arbitrary semantic measure function that orients the
canonical counter-first-lex RDRS is counter-dominated.

Does not prove: that raw payload-sensitive measures cannot mention
payload; it proves any successful orientation has a payload-erased
counter-dominated witness.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `SemanticMeasureData (Nat x Nat)`.
-/
theorem counterFirstLex_arbitrary_orienting_measure_counter_dominated
    (M : SemanticMeasureData (Nat × Nat))
    (hOrient : Orients counterFirstLexRaw_R M.μ M.ltA) :
    CounterDominated counterFirstLexRaw_R M :=
  orienting_measure_counter_dominated_of_payload_erasure
    counterFirstLexPayloadErasure M hOrient

/--
Proves: no arbitrary semantic measure function on the canonical
counter-first-lex RDRS can be decisively payload-sensitive.

Does not prove: that arbitrary raw payload-sensitive measures fail to
orient. Counter-dominated payload-mentioning measures may orient, but
they are not decisive payload-sensitive descents.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `SemanticMeasureData (Nat x Nat)`.
-/
theorem counterFirstLex_no_arbitrary_decisive_payload_sensitive
    (M : SemanticMeasureData (Nat × Nat)) :
    ¬ PayloadSensitiveDecisive counterFirstLexRaw_R M :=
  no_decisive_payload_sensitive_of_payload_erasure
    counterFirstLexPayloadErasure M

/--
Proves: no certified semantic direct measure on the canonical
counter-first-lex RDRS can be decisively payload-sensitive.

Does not prove: source-code inspection of the direct measure body.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: kernel-only.
Scope: every `SemanticDirectMeasure (Nat x Nat)`.
-/
theorem counterFirstLex_no_arbitrary_direct_decisive_payload_sensitive
    (M : SemanticDirectMeasure (Nat × Nat)) :
    ¬ PayloadSensitiveDecisive counterFirstLexRaw_R M.data :=
  no_direct_decisive_payload_sensitive_of_payload_erasure
    counterFirstLexPayloadErasure M

/-- Canonical arbitrary semantic classifier over `counterFirstLexRaw_R`. -/
noncomputable def counterFirstLex_classify_arbitrary_semantic
    (M : SemanticMeasureData (Nat × Nat)) :
    ArbitrarySemanticClassification counterFirstLexRaw_R M :=
  classifyArbitrarySemantic counterFirstLexPayloadErasure M

/--
Proves: totality of the canonical arbitrary semantic classifier.

Does not prove: computable source inspection.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: classical split inherited from `classifyArbitrarySemantic`.
Scope: every `SemanticMeasureData (Nat x Nat)`.
-/
theorem counterFirstLex_classify_arbitrary_semantic_total
    (M : SemanticMeasureData (Nat × Nat)) :
    ∃ C : ArbitrarySemanticClassification counterFirstLexRaw_R M,
      counterFirstLex_classify_arbitrary_semantic M = C :=
  classifyArbitrarySemantic_total counterFirstLexPayloadErasure M

/--
Proves: the canonical arbitrary semantic classifier has no residual
classification label.

Does not prove: computable source inspection.
Relation: `counterFirstLexRaw_R`.
Closure: root single-step.
Strategy: not applicable.
Trust: classical split inherited from `classifyArbitrarySemantic`.
Scope: every `SemanticMeasureData (Nat x Nat)`.
-/
theorem counterFirstLex_classify_arbitrary_semantic_label_total
    (M : SemanticMeasureData (Nat × Nat)) :
    (counterFirstLex_classify_arbitrary_semantic M).label =
        ArbitrarySemanticLabel.blockedByLensPump ∨
      (counterFirstLex_classify_arbitrary_semantic M).label =
        ArbitrarySemanticLabel.counterDominatedOrientation :=
  classifyArbitrarySemantic_label_total counterFirstLexPayloadErasure M

/-- Stable declaration-name string for the arbitrary semantic classifier surface. -/
def rdrs_semantic_arbitrary_classifier_anchor : String :=
  "OperatorKO7.RDRSSemanticArbitraryClassifier.counterFirstLex_no_arbitrary_decisive_payload_sensitive"

end OperatorKO7.RDRSSemanticArbitraryClassifier
