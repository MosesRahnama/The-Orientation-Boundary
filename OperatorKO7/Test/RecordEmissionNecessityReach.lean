import OperatorKO7.Meta.RecordEmissionNecessity

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema
namespace RecordTerm

example (n : RecordCounter) :
    emitsNewRecordFrame (primitiveDuplicatorRhs n) := by
  simpa using primitiveDuplicatorRhs_emitsNewRecordFrame n

example (n : RecordCounter) :
    preservesRecursiveGenerator (primitiveDuplicatorRhs n) := by
  simpa using primitiveDuplicatorRhs_preservesRecursiveGenerator n

example (n : RecordCounter) :
    ∃ p q,
      p ≠ q ∧
      p ∈ generatorPositions (primitiveDuplicatorRhs n) ∧
      q ∈ generatorPositions (primitiveDuplicatorRhs n) := by
  simpa using primitiveDuplicatorRhs_witnesses_duplication n

end RecordTerm
end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
