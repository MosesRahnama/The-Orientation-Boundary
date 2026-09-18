import OperatorKO7.Meta.StepDuplicatingSchema

/-!
# Confession Methods: Generic Interface

A confession method combines a `ProjectionRank` with a metadata tag naming an
intended external soundness result. The rank carries the formal orientation and
sensitivity-violation fields; the tag carries a label. This module projects the
rank fields through `ConfessionMethod`.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- Metadata labels for external soundness results associated with confession methods. -/
inductive SoundnessLicense
  | artsGiesl2000              -- dependency pairs and the subterm criterion
  | subtermCriterionDirect     -- subterm criterion without DP extraction
  | leeJonesBenAmram2001       -- size-change termination
  | argumentFilteringSoundness -- argument filtering in the DP framework
  deriving DecidableEq, Repr

/-- A projection rank paired with a metadata label for an intended external result. -/
structure ConfessionMethod (S : StepDuplicatingSchema) extends
    ProjectionRank S where
  license : SoundnessLicense

/-- Every confession method determines a method-agnostic confession-core
    witness by forgetting the external soundness license. -/
def ConfessionMethod.toConfessionCoreWitness {S : StepDuplicatingSchema}
    (C : ConfessionMethod S) : ConfessionCoreWitness S :=
  ConfessionCoreWitness.ofProjectionRank C.toProjectionRank

@[simp] theorem ConfessionMethod.toConfessionCoreWitness_rank
    {S : StepDuplicatingSchema} (C : ConfessionMethod S) :
    C.toConfessionCoreWitness.rank = C.rank := rfl

/-- Every confession method orients the duplicating step.
    This follows directly from the `ProjectionRank` orientation theorem. -/
theorem confession_orients {S : StepDuplicatingSchema} (C : ConfessionMethod S)
    (b s n : S.T) :
    C.rank (S.wrap s (S.recur b s n)) < C.rank (S.recur b s (S.succ n)) :=
  projection_orients_dup_step C.toProjectionRank b s n

/-- Project the first-argument sensitivity-violation field from the method rank. -/
theorem confession_violates_wrap1 {S : StepDuplicatingSchema} (C : ConfessionMethod S) :
    ∃ x y : S.T, ¬ (C.rank (S.wrap x y) > C.rank x) :=
  projection_violates_wrap_subterm1 C.toProjectionRank

/-- Every confession method violates wrapper sensitivity on the second argument. -/
theorem confession_violates_wrap2 {S : StepDuplicatingSchema} (C : ConfessionMethod S) :
    ∃ x y : S.T, ¬ (C.rank (S.wrap x y) > C.rank y) :=
  projection_violates_wrap_subterm2 C.toProjectionRank

end OperatorKO7.ConfessionMethodFamily
