import OperatorKO7.Meta.ConfessionMethod
import OperatorKO7.Meta.CompositionalMeasure_Impossibility
import OperatorKO7.Meta.DependencyPairs_Works

/-!
# Confession Method Instance: Dependency Pairs + Subterm Criterion

This module packages the KO7 dependency-pair route. The imported pair relation
contains the recursive pair
`recΔ b s (delta n) -> recΔ b s n`. Lean proves that `dpProjection` strictly
decreases on every pair in that relation and that the reverse pair relation is
well founded.

`dpConfession` pairs `dpProjectionRank` with the `artsGiesl2000` license tag.
That tag records the intended external dependency-pair soundness theorem; it is
data, not a formalized source-system transport theorem. No dependency graph or
general dependency-pair processor soundness theorem is constructed in this
file.
-/

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaDependencyPairs

/-- Witness selecting the third, counter coordinate of the marked recursive
symbol. The structure records the selected position; uniqueness is not a field. -/
structure DPWitness where
  selectedCoordinate : Fin 3
  selectedCoordinate_is_counter : selectedCoordinate = ⟨2, by decide⟩

/-- The concrete dependency-pair witness on the KO7 schema. -/
def schemaDPWitness : DPWitness where
  selectedCoordinate := ⟨2, by decide⟩
  selectedCoordinate_is_counter := rfl

/-- The DP witness packaged as the intermediate confession-core witness. -/
def DPWitness.toConfessionCoreWitness (_W : DPWitness) : ConfessionCoreWitness ko7Schema where
  rank := dpProjection
  rank_base := by rfl
  rank_succ := by intro t; rfl
  rank_wrap := by intro x y; rfl
  rank_recur := by intro b s n; rfl

/-- Explicit marked-pair view for the DP route on the single recursive call. -/
structure DPPairShapeEvidence where
  caller : Trace
  callee : Trace
  callerShape : ∃ b s n, caller = recΔ b s (delta n)
  calleeShape : ∃ b s n, callee = recΔ b s n

/-- Evidence that a caller-to-right-hand-side KO7 step yields the stated
dependency pair and that the pair strictly decreases `dpRank`. Well-foundedness
of the full reverse pair relation is stored separately in `DPRouteEvidence`. -/
structure DPPairProblemEvidence where
  caller : Trace
  rhs : Trace
  callee : Trace
  extractedFromStep : Step caller rhs
  dependencyPair : DPPair caller callee
  strictRankDescent : MetaDependencyPairs.dpRank callee < MetaDependencyPairs.dpRank caller

/-- The concrete pair-problem semantics for the schema's single recursive
    dependency pair. -/
def schemaDPPairProblemEvidence (b s n : Trace) : DPPairProblemEvidence where
  caller := recΔ b s (delta n)
  rhs := app s (recΔ b s n)
  callee := recΔ b s n
  extractedFromStep := (rec_succ_extracts_dependency_pair b s n).1
  dependencyPair := (rec_succ_extracts_dependency_pair b s n).2
  strictRankDescent := by
    exact dpPair_decreases (rec_succ_extracts_dependency_pair b s n).2

/-- The concrete marked-pair view for the schema's single recursive call. -/
def schemaDPPairShapeEvidence (b s n : Trace) : DPPairShapeEvidence where
  caller := recΔ b s (delta n)
  callee := recΔ b s n
  callerShape := ⟨b, s, n, rfl⟩
  calleeShape := ⟨b, s, n, rfl⟩

/-- Pair `dpProjectionRank` with the `artsGiesl2000` license tag. The tag names
the external route and does not itself prove its soundness theorem. -/
def dpConfession : ConfessionMethod ko7Schema where
  toProjectionRank := dpProjectionRank
  license := SoundnessLicense.artsGiesl2000

/-- The DP confession contains `dpProjectionRank` definitionally. -/
theorem dpConfession_is_canonical :
    dpConfession.toProjectionRank = dpProjectionRank := rfl

/-- The DP witness designates the counter coordinate of the marked recursive
symbol. Pair-rank descent is proved separately in `DPPairProblemEvidence`. -/
theorem dpWitness_selects_counter_coordinate :
    schemaDPWitness.selectedCoordinate = ⟨2, by decide⟩ :=
  schemaDPWitness.selectedCoordinate_is_counter

/-- The DP confession and `dpProjectionRank` have the same rank function
definitionally. -/
theorem dpWitness_realizes_projection_core :
    dpConfession.rank = dpProjectionRank.rank := rfl

/-- The witness's packaged confession core converts to `dpProjectionRank`. -/
theorem dpWitness_toConfessionCoreWitness_eq_core :
    schemaDPWitness.toConfessionCoreWitness.toProjectionRank = dpProjectionRank := by
  rfl

/-- Route evidence bundling the selected coordinate, marked-pair shape,
caller-step extraction, pair-rank descent, wrapper erasure, and well-foundedness
of the reverse pair relation. -/
structure DPRouteEvidence where
  witness : DPWitness
  markedPairShape : Trace → Trace → Trace → DPPairShapeEvidence
  pairProblemSemantics : Trace → Trace → Trace → DPPairProblemEvidence
  stepShape :
    ∀ (b s n : Trace),
      witness.toConfessionCoreWitness.rank (recΔ b s (delta n)) =
        witness.toConfessionCoreWitness.rank n + 1
  wrapperPayloadDropped :
    ∀ (x y : Trace), witness.toConfessionCoreWitness.rank (app x y) = 0
  pairProblemWellFounded : WellFounded MetaDependencyPairs.DPPairRev

/-- Concrete DP route evidence for the KO7 extracted pair relation. -/
def schemaDPRouteEvidence : DPRouteEvidence where
  witness := schemaDPWitness
  markedPairShape := schemaDPPairShapeEvidence
  pairProblemSemantics := schemaDPPairProblemEvidence
  stepShape := by
    intro b s n
    rfl
  wrapperPayloadDropped := by
    intro x y
    rfl
  pairProblemWellFounded := wf_DPPairRev

/-- Forget the pair-problem fields and retain the generic projection-rank
profile carried by the witness. -/
def DPRouteEvidence.toRouteEvidence (E : DPRouteEvidence) : RouteEvidence ko7Schema where
  rank := E.witness.toConfessionCoreWitness.rank
  rank_base := E.witness.toConfessionCoreWitness.rank_base
  rank_succ := E.witness.toConfessionCoreWitness.rank_succ
  rank_wrap := E.witness.toConfessionCoreWitness.rank_wrap
  rank_recur := E.witness.toConfessionCoreWitness.rank_recur

/-- The concrete DP route evidence packaged through the generic adapter. -/
abbrev schemaDPGenericRouteEvidence : RouteEvidence ko7Schema :=
  schemaDPRouteEvidence.toRouteEvidence

/-- The witness component satisfies the four generic projection-rank equations.
The pair-problem fields are not used in this theorem. -/
theorem dpRouteEvidence_implies_semantic_profile :
    NormalizedAtBase ko7Schema schemaDPRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema schemaDPRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema schemaDPRouteEvidence.witness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema schemaDPRouteEvidence.witness.toConfessionCoreWitness.rank := by
  exact schemaDPRouteEvidence.witness.toConfessionCoreWitness.satisfies_semantic_profile

/-- The witness's packaged projection rank satisfies the generic profile. -/
theorem dpWitness_has_semantic_profile :
    NormalizedAtBase ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
    ∧ TracksSuccessorDepth ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
    ∧ ForgetsWrapperPayload ko7Schema schemaDPWitness.toConfessionCoreWitness.rank
    ∧ FollowsRecursiveCounter ko7Schema schemaDPWitness.toConfessionCoreWitness.rank := by
  exact schemaDPWitness.toConfessionCoreWitness.satisfies_semantic_profile

end OperatorKO7.ConfessionMethodFamily
