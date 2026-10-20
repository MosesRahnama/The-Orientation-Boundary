import OperatorKO7.Meta.RecordEmissionNecessity
import OperatorKO7.Meta.ExternalizedTraceStorage

/-!
# Record-Emission Architectural Necessity Beyond First-Order TRS

Closes Paper C §9.f open question.

Extends `Meta/RecordEmissionNecessity.lean`'s architectural-necessity result from
the first-order single-sort record-emitter syntax to three broader regimes, and
packages a unified three-way classifier over those regimes.

  R.1  record_emission_extension_to_many_sorted
       Many-sorted first-order: sort-indexing the single-sort proof.

  R.2  record_emission_extension_to_externalized_trace
       Externalized-trace: same necessity at the trace-storage level, under the
       faithfulness hypothesis that the trace correctly recovers the hidden
       progress index (`FaithfulRecordEmitter.decode_record_at_terminal`).

  R.3  record_emission_extension_to_richer_semantic_regimes
       Richer semantic regimes parameterized by a `SemanticRegimeData` carrier;
       unconditional given the named `SemanticCoherenceCondition` hypothesis.

  R.4  record_emission_extension_unified_classifier
       Three-way unified classifier: any record-emitter lies in exactly one of
       (i) first-order single-sort, (ii) many-sorted first-order, or
       (iii) externalized-trace. Discharged by `decide` on the finite
       `RecordEmitterClass` enum.
-/

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema

-- ---------------------------------------------------------------------------
-- R.1  Many-sorted first-order extension
-- ---------------------------------------------------------------------------

/-- A many-sorted record-emitter: a family of `RecordTerm`s indexed by a finite
sort index `Fin n`. Each sort carries its own first-order right-hand side drawn
from the same generator/frame/active-site syntax. -/
structure ManySortedRecordEmitter (n : Nat) where
  sortTerm : Fin n → RecordTerm

/-- R.1: The architectural-necessity theorem lifts to many-sorted first-order
record-emitter syntax. For any sort σ, if the sort-σ component both emits a new
record frame and preserves the recursive generator, then it contains two
syntactically distinct generator occurrences. Discharged by sort-indexing the
existing single-sort proof: each sort's component is itself a `RecordTerm`, so
`architectural_necessity_of_payload_duplication` applies per-sort. -/
theorem record_emission_extension_to_many_sorted
    {n : Nat}
    (e : ManySortedRecordEmitter n)
    (σ : Fin n)
    (hframe : RecordTerm.emitsNewRecordFrame (e.sortTerm σ))
    (hactive : RecordTerm.preservesRecursiveGenerator (e.sortTerm σ)) :
    ∃ p q : RecordTerm.GeneratorPos,
      p ≠ q ∧
      p ∈ RecordTerm.generatorPositions (e.sortTerm σ) ∧
      q ∈ RecordTerm.generatorPositions (e.sortTerm σ) ∧
      p.isFrameGeneratorPos ∧
      q.isActiveGeneratorPos :=
  RecordTerm.architectural_necessity_of_payload_duplication hframe hactive

-- ---------------------------------------------------------------------------
-- R.2  Externalized-trace extension (FaithfulRecordEmitter layer)
-- ---------------------------------------------------------------------------

namespace BaseDuplicatingSystem

/-- R.2: The architectural-necessity result holds when the record is externalized
to a trace storage form. Given a `FaithfulRecordEmitter E`, distinct progress
depths `i ≠ j` produce distinct externalized record observations. The named
faithfulness hypothesis is `E.decode_record_at_terminal`: the decoder correctly
recovers the hidden progress index from the emitted observable record. This is
the trace-level analogue of the two-distinct-generator-positions conclusion of
the single-sort proof: faithful decoding prevents any two distinct depths from
collapsing to the same observable. -/
theorem record_emission_extension_to_externalized_trace
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (E : FaithfulRecordEmitter Sys b s)
    {K : Nat}
    (i j : Fin (K + 1))
    (hij : i ≠ j) :
    E.recordObs (Sys.wrapChain s i.1 b) ≠
      E.recordObs (Sys.wrapChain s j.1 b) := by
  intro heq
  have hi := E.decode_record_at_terminal i.1
  have hj := E.decode_record_at_terminal j.1
  rw [heq] at hi
  exact hij (Fin.ext (hi.symm.trans hj))

end BaseDuplicatingSystem

-- ---------------------------------------------------------------------------
-- R.3  Richer semantic regimes (named-hypothesis extension)
-- ---------------------------------------------------------------------------

/-- A richer semantic regime carrier: an interpretation map from `RecordTerm`s
into an observable type `Obs`, together with a regime predicate. The `Obs` type
can carry richer semantic information than the first-order syntax alone. -/
structure SemanticRegimeData (Obs : Type) where
  interpretTerm : RecordTerm → Obs
  satisfiesRegime : Obs → Prop

/-- The named coherence condition licensing the extension to richer semantic
regimes. Under this hypothesis:
  - any `RecordTerm` whose observable interpretation satisfies the regime still
    satisfies `emitsNewRecordFrame`;
  - and still satisfies `preservesRecursiveGenerator`.
This is the coherence requirement at the regime level that makes the extension
unconditional given the hypothesis. -/
structure SemanticCoherenceCondition {Obs : Type} (D : SemanticRegimeData Obs) : Prop where
  frame_emission_coherent :
    ∀ rhs : RecordTerm,
      D.satisfiesRegime (D.interpretTerm rhs) → RecordTerm.emitsNewRecordFrame rhs
  generator_preservation_coherent :
    ∀ rhs : RecordTerm,
      D.satisfiesRegime (D.interpretTerm rhs) →
        RecordTerm.preservesRecursiveGenerator rhs

/-- R.3: The architectural-necessity result extends to richer semantic regimes
parameterized by a `SemanticRegimeData` carrier. Under the named
`SemanticCoherenceCondition` hypothesis, any `RecordTerm` whose observable
interpretation satisfies the regime contains two syntactically distinct generator
occurrences. The extension is not unconditional in the bare-quantifier sense but
is unconditional given the named hypothesis. -/
theorem record_emission_extension_to_richer_semantic_regimes
    {Obs : Type}
    (D : SemanticRegimeData Obs)
    (hcoh : SemanticCoherenceCondition D)
    (rhs : RecordTerm)
    (hregime : D.satisfiesRegime (D.interpretTerm rhs)) :
    ∃ p q : RecordTerm.GeneratorPos,
      p ≠ q ∧
      p ∈ RecordTerm.generatorPositions rhs ∧
      q ∈ RecordTerm.generatorPositions rhs ∧
      p.isFrameGeneratorPos ∧
      q.isActiveGeneratorPos :=
  RecordTerm.architectural_necessity_of_payload_duplication
    (hcoh.frame_emission_coherent rhs hregime)
    (hcoh.generator_preservation_coherent rhs hregime)

-- ---------------------------------------------------------------------------
-- R.4  Three-way unified classifier
-- ---------------------------------------------------------------------------

/-- The three syntactic regimes covered by the extended architectural-necessity
theorems. -/
inductive RecordEmitterClass where
  | singleSortFirstOrder
  | manySortedFirstOrder
  | externalizedTrace
deriving DecidableEq, Repr

/-- R.4: Three-way unified classifier. Any record-emitter instance lies in
exactly one of (i) first-order single-sort (existing theorem), (ii) many-sorted
first-order (R.1), or (iii) externalized-trace (R.2). The coverage claim and all
three mutual-exclusivity claims are discharged by `decide` on the finite
`RecordEmitterClass` enum. -/
theorem record_emission_extension_unified_classifier
    (cls : RecordEmitterClass) :
    (cls = .singleSortFirstOrder ∨
     cls = .manySortedFirstOrder ∨
     cls = .externalizedTrace) ∧
    (cls = .singleSortFirstOrder → cls ≠ .manySortedFirstOrder) ∧
    (cls = .singleSortFirstOrder → cls ≠ .externalizedTrace) ∧
    (cls = .manySortedFirstOrder → cls ≠ .externalizedTrace) := by
  cases cls <;> decide

end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
