import OperatorKO7.Meta.RecordEmissionNecessity_BeyondFirstOrder

/-!
# Reach tests for RecordEmissionNecessity_BeyondFirstOrder

Exercises R.1-R.4 from the extension module by name.
-/

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema

-- ---------------------------------------------------------------------------
-- R.1  Many-sorted extension reach
-- ---------------------------------------------------------------------------

-- Concrete two-sort emitter: sort 0 is the primitive duplicator rhs.
private def twoSortEmitter (n : RecordCounter) : ManySortedRecordEmitter 2 where
  sortTerm := fun i =>
    match i with
    | ⟨0, _⟩ => RecordTerm.primitiveDuplicatorRhs n
    | ⟨_, _⟩ => RecordTerm.base

-- Sort 0 emits a record frame.
example (n : RecordCounter) :
    RecordTerm.emitsNewRecordFrame ((twoSortEmitter n).sortTerm ⟨0, by decide⟩) :=
  RecordTerm.primitiveDuplicatorRhs_emitsNewRecordFrame n

-- Sort 0 preserves the recursive generator.
example (n : RecordCounter) :
    RecordTerm.preservesRecursiveGenerator ((twoSortEmitter n).sortTerm ⟨0, by decide⟩) :=
  RecordTerm.primitiveDuplicatorRhs_preservesRecursiveGenerator n

-- R.1 applied to sort 0 of the two-sort emitter.
example (n : RecordCounter) :
    ∃ p q : RecordTerm.GeneratorPos,
      p ≠ q ∧
      p ∈ RecordTerm.generatorPositions ((twoSortEmitter n).sortTerm ⟨0, by decide⟩) ∧
      q ∈ RecordTerm.generatorPositions ((twoSortEmitter n).sortTerm ⟨0, by decide⟩) ∧
      p.isFrameGeneratorPos ∧
      q.isActiveGeneratorPos :=
  record_emission_extension_to_many_sorted (twoSortEmitter n) ⟨0, by decide⟩
    (RecordTerm.primitiveDuplicatorRhs_emitsNewRecordFrame n)
    (RecordTerm.primitiveDuplicatorRhs_preservesRecursiveGenerator n)

-- ---------------------------------------------------------------------------
-- R.2  Externalized-trace reach
-- ---------------------------------------------------------------------------

-- The free faithful emitter's records at distinct depths are distinct.
example {K : Nat} (i j : Fin (K + 1)) (hij : i ≠ j) :
    freeFaithfulRecordEmitter.recordObs
        (freeBaseSystem.wrapChain freeSeedY i.1 freeSeedX) ≠
      freeFaithfulRecordEmitter.recordObs
        (freeBaseSystem.wrapChain freeSeedY j.1 freeSeedX) :=
  BaseDuplicatingSystem.record_emission_extension_to_externalized_trace
    freeFaithfulRecordEmitter i j hij

-- Same result via the record-emission witness (R.2 at the raw-coordinate level).
example {K : Nat} (i j : Fin (K + 1)) (hij : i ≠ j) :
    freeRecordEmissionWitness.recordCoord
        (freeBaseSystem.wrapChain freeSeedY i.1 freeSeedX) ≠
      freeRecordEmissionWitness.recordCoord
        (freeBaseSystem.wrapChain freeSeedY j.1 freeSeedX) := by
  simp [BaseDuplicatingSystem.RecordEmissionWitness.record_terminal]
  exact fun h => hij (Fin.ext h)

-- ---------------------------------------------------------------------------
-- R.3  Semantic-regime reach
-- ---------------------------------------------------------------------------

-- SemanticRegimeData whose satisfiesRegime is Prop-valued directly.
private def propRegimeData : SemanticRegimeData Prop where
  interpretTerm := fun rhs =>
    RecordTerm.emitsNewRecordFrame rhs ∧ RecordTerm.preservesRecursiveGenerator rhs
  satisfiesRegime := id

private def propRegimeCoherence : SemanticCoherenceCondition propRegimeData where
  frame_emission_coherent := fun _ h => h.1
  generator_preservation_coherent := fun _ h => h.2

example (n : RecordCounter) :
    ∃ p q : RecordTerm.GeneratorPos,
      p ≠ q ∧
      p ∈ RecordTerm.generatorPositions (RecordTerm.primitiveDuplicatorRhs n) ∧
      q ∈ RecordTerm.generatorPositions (RecordTerm.primitiveDuplicatorRhs n) ∧
      p.isFrameGeneratorPos ∧
      q.isActiveGeneratorPos :=
  record_emission_extension_to_richer_semantic_regimes
    propRegimeData
    propRegimeCoherence
    (RecordTerm.primitiveDuplicatorRhs n)
    ⟨RecordTerm.primitiveDuplicatorRhs_emitsNewRecordFrame n,
     RecordTerm.primitiveDuplicatorRhs_preservesRecursiveGenerator n⟩

-- ---------------------------------------------------------------------------
-- R.4  Unified classifier reach
-- ---------------------------------------------------------------------------

-- Every constructor passes the R.4 coverage predicate.
example : (RecordEmitterClass.singleSortFirstOrder = .singleSortFirstOrder ∨
           RecordEmitterClass.singleSortFirstOrder = .manySortedFirstOrder ∨
           RecordEmitterClass.singleSortFirstOrder = .externalizedTrace) :=
  (record_emission_extension_unified_classifier .singleSortFirstOrder).1

example : (RecordEmitterClass.manySortedFirstOrder = .singleSortFirstOrder ∨
           RecordEmitterClass.manySortedFirstOrder = .manySortedFirstOrder ∨
           RecordEmitterClass.manySortedFirstOrder = .externalizedTrace) :=
  (record_emission_extension_unified_classifier .manySortedFirstOrder).1

example : (RecordEmitterClass.externalizedTrace = .singleSortFirstOrder ∨
           RecordEmitterClass.externalizedTrace = .manySortedFirstOrder ∨
           RecordEmitterClass.externalizedTrace = .externalizedTrace) :=
  (record_emission_extension_unified_classifier .externalizedTrace).1

-- Mutual exclusivity: all three pairs are distinct.
example : RecordEmitterClass.singleSortFirstOrder ≠ .manySortedFirstOrder := by decide
example : RecordEmitterClass.singleSortFirstOrder ≠ .externalizedTrace := by decide
example : RecordEmitterClass.manySortedFirstOrder ≠ .externalizedTrace := by decide

-- record_emission_extension_unified_classifier exercised on all three values.
example : ∀ cls : RecordEmitterClass,
    (cls = .singleSortFirstOrder ∨ cls = .manySortedFirstOrder ∨ cls = .externalizedTrace) ∧
    (cls = .singleSortFirstOrder → cls ≠ .manySortedFirstOrder) ∧
    (cls = .singleSortFirstOrder → cls ≠ .externalizedTrace) ∧
    (cls = .manySortedFirstOrder → cls ≠ .externalizedTrace) := fun cls =>
  record_emission_extension_unified_classifier cls

end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
