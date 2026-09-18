import OperatorKO7.Meta.StepDuplicatingSchema
import OperatorKO7.Meta.ConfessionMethod

/-!
# Schema-Generic Forgetting Witness

## Formal Scope

ForgettingWitness packages orientation together with two sensitivity violations. The conjunction alone does not prove a causal claim that orientation succeeds because of those violations, and concrete method coverage requires typed adapters.
-/

namespace OperatorKO7.StepDuplicating

namespace StepDuplicatingSchema

/-- **Schema-generic forgetting witness.** A rank on a step-duplicating
schema that orients the duplicating step and *explicitly* violates wrapper
sensitivity on each of the two payload positions.

The historical name "forgetting" refers to the two stored counterexamples to
wrapper sensitivity. The structure records those counterexamples together
with orientation; it does not state that one causes the other. -/
structure ForgettingWitness (S : StepDuplicatingSchema) where
  rank : S.T → Nat
  orientsDupStep :
    ∀ b s n,
      rank (S.wrap s (S.recur b s n))
        < rank (S.recur b s (S.succ n))
  violatesPayloadLeft :
    ∃ x y : S.T, ¬ (rank (S.wrap x y) > rank x)
  violatesPayloadRight :
    ∃ x y : S.T, ¬ (rank (S.wrap x y) > rank y)

namespace ForgettingWitness

/-- Package the orientation and sensitivity fields of a `ProjectionRank S` as
a `ForgettingWitness S`. -/
def ofProjectionRank {S : StepDuplicatingSchema}
    (R : ProjectionRank S) : ForgettingWitness S where
  rank := R.rank
  orientsDupStep := projection_orients_dup_step R
  violatesPayloadLeft := projection_violates_wrap_subterm1 R
  violatesPayloadRight := projection_violates_wrap_subterm2 R

@[simp] theorem ofProjectionRank_rank {S : StepDuplicatingSchema}
    (R : ProjectionRank S) :
    (ofProjectionRank R).rank = R.rank := rfl

/-- Every confession-core witness also yields a generic forgetting witness,
    by packaging it as the shared projection core first. -/
def ofConfessionCoreWitness {S : StepDuplicatingSchema}
    (W : ConfessionCoreWitness S) : ForgettingWitness S :=
  ofProjectionRank W.toProjectionRank

@[simp] theorem ofConfessionCoreWitness_rank {S : StepDuplicatingSchema}
    (W : ConfessionCoreWitness S) :
    (ofConfessionCoreWitness W).rank = W.rank := rfl

/-- Any rank satisfying the semantic confession-core profile yields a generic
    forgetting witness directly. -/
def ofSemanticProfile {S : StepDuplicatingSchema} (rank : S.T → Nat)
    (hbase : NormalizedAtBase S rank)
    (hsucc : TracksSuccessorDepth S rank)
    (hwrap : ForgetsWrapperPayload S rank)
    (hrecur : FollowsRecursiveCounter S rank) : ForgettingWitness S where
  rank := rank
  orientsDupStep := semanticProfile_orients_dup_step hbase hsucc hwrap hrecur
  violatesPayloadLeft := semanticProfile_violates_wrap_subterm1 hbase hsucc hwrap
  violatesPayloadRight := semanticProfile_violates_wrap_subterm2 hbase hsucc hwrap

@[simp] theorem ofSemanticProfile_rank {S : StepDuplicatingSchema}
    (rank : S.T → Nat)
    (hbase : NormalizedAtBase S rank)
    (hsucc : TracksSuccessorDepth S rank)
    (hwrap : ForgetsWrapperPayload S rank)
    (hrecur : FollowsRecursiveCounter S rank) :
    (ofSemanticProfile rank hbase hsucc hwrap hrecur).rank = rank := rfl

/-- Generic route evidence also yields a generic forgetting witness. -/
def ofRouteEvidence {S : StepDuplicatingSchema}
    (E : RouteEvidence S) : ForgettingWitness S :=
  ofSemanticProfile E.rank E.rank_base E.rank_succ E.rank_wrap E.rank_recur

@[simp] theorem ofRouteEvidence_rank {S : StepDuplicatingSchema}
    (E : RouteEvidence S) :
    (ofRouteEvidence E).rank = E.rank := rfl

end ForgettingWitness

end StepDuplicatingSchema

end OperatorKO7.StepDuplicating

namespace OperatorKO7.ConfessionMethodFamily

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-- **Every `ConfessionMethod S` yields a `ForgettingWitness S`**, via its
underlying projection rank. -/
def ConfessionMethod.toForgettingWitness
    {S : StepDuplicatingSchema} (C : ConfessionMethod S) :
    ForgettingWitness S :=
  ForgettingWitness.ofProjectionRank C.toProjectionRank

@[simp] theorem ConfessionMethod.toForgettingWitness_rank
    {S : StepDuplicatingSchema} (C : ConfessionMethod S) :
    C.toForgettingWitness.rank = C.rank := rfl

end OperatorKO7.ConfessionMethodFamily
