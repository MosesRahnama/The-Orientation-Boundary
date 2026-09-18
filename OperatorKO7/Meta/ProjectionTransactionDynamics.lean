import OperatorKO7.Meta.ComputationalLayerCrossing
import OperatorKO7.Meta.RecordStorageForm

/-!
# Projection-Transaction Dynamics

This module strengthens the static projection-transaction story from
`SchemaOperationalIncompleteness.lean`.

The old theorem there only showed that a literally constant family is static.
The present file proves a stronger free-syntax rigidity statement:

- any stage-indexed family of projection-rank transactions on the free primitive
  duplicator already collapses to the unique counter-depth projection core; and
- with license invariance added, the induced projection-transaction family is
  static in the substantive sense, not just by constant-family tautology.
-/

namespace OperatorKO7.StepDuplicating
namespace StepDuplicatingSchema

/-- A stage-indexed projection transaction presented through a genuine
`ProjectionRank`, rather than only as a bare forgetting witness. This is the
right level for the dynamic/static question, because the free syntax admits a
uniqueness theorem for `ProjectionRank`. -/
structure RankProjectionTransaction (S : StepDuplicatingSchema) where
  rank : ProjectionRank S
  license : Prop
  licensed : license

namespace RankProjectionTransaction

/-- Forgetting-witness view of a rank-based transaction. -/
def toProjectionTransaction {S : StepDuplicatingSchema}
    (T : RankProjectionTransaction S) : ProjectionTransaction S where
  dimension := T.rank.rank
  license := T.license
  boundary := ForgettingWitness.ofProjectionRank T.rank
  licensed := T.licensed

@[simp] theorem toProjectionTransaction_dimension {S : StepDuplicatingSchema}
    (T : RankProjectionTransaction S) :
    (T.toProjectionTransaction).dimension = T.rank.rank := rfl

@[simp] theorem toProjectionTransaction_boundary {S : StepDuplicatingSchema}
    (T : RankProjectionTransaction S) :
    (T.toProjectionTransaction).boundary = ForgettingWitness.ofProjectionRank T.rank := rfl

end RankProjectionTransaction

/-- License invariance for a stage-indexed transaction family. -/
def LicenseInvariant {S : StepDuplicatingSchema}
    (τ : Nat → RankProjectionTransaction S) : Prop :=
  ∀ i, (τ i).license = (τ 0).license

/-- A stage-indexed projective-emitter transaction packages a concrete
projective emitter together with the external license used to read it as a
projection transaction. -/
structure LicensedProjectiveEmitterTransaction
    (Sys : BaseDuplicatingSystem) (b s : Sys.T) where
  emitter : BaseDuplicatingSystem.ProjectiveRecordEmitter Sys b s
  license : Prop
  licensed : license

namespace LicensedProjectiveEmitterTransaction

/-- Read a licensed projective-emitter transaction as an ordinary
`ProjectionTransaction`. -/
def toProjectionTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedProjectiveEmitterTransaction Sys b s) :
    ProjectionTransaction Sys.toStepDuplicatingSchema :=
  T.emitter.toProjectionTransaction T.license T.licensed

@[simp] theorem toProjectionTransaction_dimension
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedProjectiveEmitterTransaction Sys b s) :
    (T.toProjectionTransaction).dimension = T.emitter.projectedGeneratorCoord := rfl

@[simp] theorem toProjectionTransaction_boundary
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedProjectiveEmitterTransaction Sys b s) :
    (T.toProjectionTransaction).boundary = T.emitter.toForgettingWitness := rfl

end LicensedProjectiveEmitterTransaction

/-- Minimal strengthened form of a raw projective emitter: the projection map
itself is required to respect the step-duplicating constructors. This is the
smallest natural strengthening of `ProjectiveRecordEmitter` that blocks the
free anomalous counterexample while still staying at the projective-emitter
level rather than moving all the way down to faithful emitters plus separately
packaged semantic kernels. -/
structure CoherentProjectiveRecordEmitter
    (Sys : BaseDuplicatingSystem) (b s : Sys.T)
    extends BaseDuplicatingSystem.ProjectiveRecordEmitter Sys b s where
  project_base : project Sys.base = Sys.base
  project_succ : ∀ t, project (Sys.succ t) = Sys.succ (project t)
  project_wrap : ∀ x y, project (Sys.wrap x y) = project y
  project_recur :
    ∀ b s n, project (Sys.recur b s n) =
      Sys.recur (project b) (project s) (project n)

namespace CoherentProjectiveRecordEmitter

theorem projectedSeedZero
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (E : CoherentProjectiveRecordEmitter Sys b s) :
    E.projectedRank.rank (E.project b) = 0 := by
  simpa [BaseDuplicatingSystem.wrapChain] using E.project_terminal 0

def toSemanticProjectionKernel
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (E : CoherentProjectiveRecordEmitter Sys b s) :
    BaseDuplicatingSystem.SemanticProjectionKernel Sys where
  project := E.project
  projectedRank := E.projectedRank
  project_base := E.project_base
  project_succ := E.project_succ
  project_wrap := E.project_wrap
  project_recur := E.project_recur

end CoherentProjectiveRecordEmitter

/-- A weaker transaction layer built only from a faithful record emitter plus a
rank-level projection kernel. This is strictly less packaged than a
`LicensedProjectiveEmitterTransaction`: the projective/confession bridge is
reconstructed canonically through the computation-to-record machinery rather
than supplied up front as data. -/
structure LicensedRankKernelEmitterTransaction
    (Sys : BaseDuplicatingSystem) (b s : Sys.T) where
  emitter : BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s
  kernel : BaseDuplicatingSystem.RankLevelProjectionKernel Sys
  projectedSeedZero : kernel.projectedRank.rank (kernel.project b) = 0
  license : Prop
  licensed : license

namespace LicensedRankKernelEmitterTransaction

/-- Reconstruct the concrete projective emitter from the weaker faithful-emitter
+ rank-level-kernel data. -/
def toProjectiveRecordEmitter
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedRankKernelEmitterTransaction Sys b s) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter Sys b s :=
  (BaseDuplicatingSystem.FaithfulRecordEmitter.toConservationBasedGeneratorEmitterOfRankLevelKernel
      (E := T.emitter) T.kernel T.projectedSeedZero).toProjectedGeneratorWitness.toProjectiveRecordEmitter

/-- Read a weaker rank-kernel transaction as an ordinary licensed projective
emitter transaction. -/
def toLicensedProjectiveEmitterTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedRankKernelEmitterTransaction Sys b s) :
    LicensedProjectiveEmitterTransaction Sys b s where
  emitter := T.toProjectiveRecordEmitter
  license := T.license
  licensed := T.licensed

@[simp] theorem toLicensedProjectiveEmitterTransaction_license
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedRankKernelEmitterTransaction Sys b s) :
    T.toLicensedProjectiveEmitterTransaction.license = T.license := rfl

@[simp] theorem toLicensedProjectiveEmitterTransaction_boundary
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedRankKernelEmitterTransaction Sys b s) :
    T.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.boundary
      = T.toProjectiveRecordEmitter.toForgettingWitness := rfl

/-- The weaker rank-kernel transaction still carries the full
computation-to-confession bridge, via its canonically reconstructed projective
emitter. -/
theorem realizesComputationToConfessionBridge_of_one_le
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedRankKernelEmitterTransaction Sys b s)
    {K : Nat} (hK : 1 ≤ K) :
    T.toProjectiveRecordEmitter.RealizesComputationToConfessionBridge K := by
  exact T.toProjectiveRecordEmitter.realizesComputationToConfessionBridge_of_one_le hK

end LicensedRankKernelEmitterTransaction

/-- A semantically richer kernel-driven transaction layer built from a faithful
record emitter plus a constructor-respecting ambient projection kernel. This
does not assume a separately packaged projective emitter; that layer is
reconstructed canonically from the semantic kernel and the computation-to-record
machinery. -/
structure LicensedSemanticKernelEmitterTransaction
    (Sys : BaseDuplicatingSystem) (b s : Sys.T) where
  emitter : BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s
  kernel : BaseDuplicatingSystem.SemanticProjectionKernel Sys
  projectedSeedZero : kernel.projectedRank.rank (kernel.project b) = 0
  license : Prop
  licensed : license

namespace LicensedSemanticKernelEmitterTransaction

/-- Reconstruct the concrete projective emitter from the weaker faithful-emitter
+ semantic-kernel data. -/
def toProjectiveRecordEmitter
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticKernelEmitterTransaction Sys b s) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter Sys b s :=
  (BaseDuplicatingSystem.FaithfulRecordEmitter.toConservationBasedGeneratorEmitterOfSemanticKernel
      (E := T.emitter) T.kernel T.projectedSeedZero).toProjectedGeneratorWitness.toProjectiveRecordEmitter

/-- Read a semantic-kernel transaction as an ordinary licensed projective
emitter transaction. -/
def toLicensedProjectiveEmitterTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticKernelEmitterTransaction Sys b s) :
    LicensedProjectiveEmitterTransaction Sys b s where
  emitter := T.toProjectiveRecordEmitter
  license := T.license
  licensed := T.licensed

@[simp] theorem toLicensedProjectiveEmitterTransaction_license
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticKernelEmitterTransaction Sys b s) :
    T.toLicensedProjectiveEmitterTransaction.license = T.license := rfl

@[simp] theorem toLicensedProjectiveEmitterTransaction_boundary
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticKernelEmitterTransaction Sys b s) :
    T.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.boundary
      = T.toProjectiveRecordEmitter.toForgettingWitness := rfl

@[simp] theorem toLicensedProjectiveEmitterTransaction_dimension
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticKernelEmitterTransaction Sys b s) :
    T.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.dimension
      = fun t => T.kernel.projectedRank.rank (T.kernel.project t) := rfl

/-- The semantic-kernel transaction still carries the full
computation-to-confession bridge, via its canonically reconstructed projective
emitter. -/
theorem realizesComputationToConfessionBridge_of_one_le
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticKernelEmitterTransaction Sys b s)
    {K : Nat} (hK : 1 ≤ K) :
    T.toProjectiveRecordEmitter.RealizesComputationToConfessionBridge K := by
  exact T.toProjectiveRecordEmitter.realizesComputationToConfessionBridge_of_one_le hK

end LicensedSemanticKernelEmitterTransaction

/-- Licensed transaction layer for the minimally strengthened coherent
projective emitters. -/
structure LicensedCoherentProjectiveEmitterTransaction
    (Sys : BaseDuplicatingSystem) (b s : Sys.T) where
  emitter : CoherentProjectiveRecordEmitter Sys b s
  license : Prop
  licensed : license

namespace LicensedCoherentProjectiveEmitterTransaction

def toLicensedSemanticKernelEmitterTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedCoherentProjectiveEmitterTransaction Sys b s) :
    LicensedSemanticKernelEmitterTransaction Sys b s where
  emitter := T.emitter.toFaithfulRecordEmitter
  kernel := T.emitter.toSemanticProjectionKernel
  projectedSeedZero := T.emitter.projectedSeedZero
  license := T.license
  licensed := T.licensed

def toProjectionTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedCoherentProjectiveEmitterTransaction Sys b s) :
    ProjectionTransaction Sys.toStepDuplicatingSchema :=
  T.toLicensedSemanticKernelEmitterTransaction.toLicensedProjectiveEmitterTransaction.toProjectionTransaction

theorem realizesComputationToConfessionBridge_of_one_le
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedCoherentProjectiveEmitterTransaction Sys b s)
    {K : Nat} (hK : 1 ≤ K) :
    T.toLicensedSemanticKernelEmitterTransaction.toProjectiveRecordEmitter.RealizesComputationToConfessionBridge K := by
  exact
    T.toLicensedSemanticKernelEmitterTransaction.realizesComputationToConfessionBridge_of_one_le
      hK

end LicensedCoherentProjectiveEmitterTransaction

/-- A direct semantic route below explicit kernel packaging: a
generator-preserving emitter whose projection itself respects the constructors.
This is weaker than giving a `SemanticProjectionKernel` as separate data, but
still strong enough to recover one canonically. -/
structure LicensedSemanticGeneratorPreservingEmitterTransaction
    (Sys : BaseDuplicatingSystem) (b s : Sys.T) where
  emitter : BaseDuplicatingSystem.SemanticGeneratorPreservingRecordEmitter Sys b s
  projectedSeedZero : emitter.generatorCoord (emitter.project b) = 0
  license : Prop
  licensed : license

namespace LicensedSemanticGeneratorPreservingEmitterTransaction

def toLicensedSemanticKernelEmitterTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticGeneratorPreservingEmitterTransaction Sys b s) :
    LicensedSemanticKernelEmitterTransaction Sys b s where
  emitter := T.emitter.toFaithfulRecordEmitter
  kernel := T.emitter.toSemanticProjectionKernel
  projectedSeedZero := by
    simpa [BaseDuplicatingSystem.SemanticGeneratorPreservingRecordEmitter.toSemanticProjectionKernel,
      BaseDuplicatingSystem.GeneratorPreservingRecordEmitter.toProjectionRank]
      using T.projectedSeedZero
  license := T.license
  licensed := T.licensed

def toProjectionTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticGeneratorPreservingEmitterTransaction Sys b s) :
    ProjectionTransaction Sys.toStepDuplicatingSchema :=
  (T.toLicensedSemanticKernelEmitterTransaction).toLicensedProjectiveEmitterTransaction.toProjectionTransaction

theorem realizesComputationToConfessionBridge_of_one_le
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticGeneratorPreservingEmitterTransaction Sys b s)
    {K : Nat} (hK : 1 ≤ K) :
    T.toLicensedSemanticKernelEmitterTransaction.toProjectiveRecordEmitter.RealizesComputationToConfessionBridge K := by
  exact T.toLicensedSemanticKernelEmitterTransaction.realizesComputationToConfessionBridge_of_one_le hK

end LicensedSemanticGeneratorPreservingEmitterTransaction

/-- A weaker semantic route than the generator-preserving layer: start from the
conservation-law interface and only require semantic coherence of the ambient
projection itself. Completion objects can then be reconstructed canonically
from conservation rather than from explicitly supplied canonical/terminal
generator equations. -/
structure LicensedSemanticConservationEmitterTransaction
    (Sys : BaseDuplicatingSystem) (b s : Sys.T) where
  emitter : BaseDuplicatingSystem.SemanticConservationBasedGeneratorEmitter Sys b s
  license : Prop
  licensed : license

namespace LicensedSemanticConservationEmitterTransaction

def toLicensedSemanticKernelEmitterTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticConservationEmitterTransaction Sys b s) :
    LicensedSemanticKernelEmitterTransaction Sys b s where
  emitter := T.emitter.toFaithfulRecordEmitter
  kernel := T.emitter.toSemanticProjectionKernel
  projectedSeedZero := T.emitter.project_seed_zero
  license := T.license
  licensed := T.licensed

def toProjectionTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticConservationEmitterTransaction Sys b s) :
    ProjectionTransaction Sys.toStepDuplicatingSchema :=
  (T.toLicensedSemanticKernelEmitterTransaction).toLicensedProjectiveEmitterTransaction.toProjectionTransaction

theorem realizesComputationToConfessionBridge_of_one_le
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticConservationEmitterTransaction Sys b s)
    {K : Nat} (hK : 1 ≤ K) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter.RealizesComputationToConfessionBridge
      ((T.toLicensedSemanticKernelEmitterTransaction).toProjectiveRecordEmitter) K := by
  exact
    LicensedSemanticKernelEmitterTransaction.realizesComputationToConfessionBridge_of_one_le
      (T.toLicensedSemanticKernelEmitterTransaction) hK

end LicensedSemanticConservationEmitterTransaction

/-- A raw stage-indexed transaction equipped only with the weaker semantic
extension principle. This sits below explicit semantic-kernel packaging and
below the stronger semantic-generator-preserving layer. -/
structure LicensedStageIndexedSemanticExtensionTransaction
    (Sys : BaseDuplicatingSystem) (b s : Sys.T) where
  emitter : BaseDuplicatingSystem.StageIndexedConservationEmitter Sys b s
  extension : emitter.SemanticExtension
  license : Prop
  licensed : license

namespace LicensedStageIndexedSemanticExtensionTransaction

def toLicensedSemanticConservationEmitterTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedSemanticExtensionTransaction Sys b s) :
    LicensedSemanticConservationEmitterTransaction Sys b s where
  emitter := T.extension.toSemanticConservationBasedGeneratorEmitter
  license := T.license
  licensed := T.licensed

def toProjectionTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedSemanticExtensionTransaction Sys b s) :
    ProjectionTransaction Sys.toStepDuplicatingSchema :=
  (T.toLicensedSemanticConservationEmitterTransaction).toProjectionTransaction

theorem realizesComputationToConfessionBridge_of_one_le
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedSemanticExtensionTransaction Sys b s)
    {K : Nat} (hK : 1 ≤ K) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter.RealizesComputationToConfessionBridge
      ((LicensedSemanticConservationEmitterTransaction.toLicensedSemanticKernelEmitterTransaction
        (T.toLicensedSemanticConservationEmitterTransaction)).toProjectiveRecordEmitter) K := by
  exact
    LicensedSemanticConservationEmitterTransaction.realizesComputationToConfessionBridge_of_one_le
      (T.toLicensedSemanticConservationEmitterTransaction) hK

end LicensedStageIndexedSemanticExtensionTransaction

/-- A still-weaker transaction layer built directly from the raw stage-indexed
record-emitter interface, with no ambient kernel and no reconstructed
projective emitter. This is the right level for canonical-shadow dynamics: the
only data available is the emitted-record semantics along the canonical live
trace and the terminal record. -/
structure LicensedStageIndexedSemanticKernelTransaction
    (Sys : BaseDuplicatingSystem) (b s : Sys.T) where
  emitter : BaseDuplicatingSystem.StageIndexedConservationEmitter Sys b s
  kernel : BaseDuplicatingSystem.SemanticProjectionKernel Sys
  projectedSeedZero : kernel.projectedRank.rank (kernel.project b) = 0
  license : Prop
  licensed : license

namespace LicensedStageIndexedSemanticKernelTransaction

/-- Forget the raw stage-indexed emitter down to the faithful-emitter layer and
read the result as a semantic-kernel transaction. -/
def toLicensedSemanticKernelEmitterTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedSemanticKernelTransaction Sys b s) :
    LicensedSemanticKernelEmitterTransaction Sys b s where
  emitter := T.emitter.toFaithfulRecordEmitter
  kernel := T.kernel
  projectedSeedZero := T.projectedSeedZero
  license := T.license
  licensed := T.licensed

/-- Canonically reconstructed projective-emitter view. -/
def toProjectiveRecordEmitter
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedSemanticKernelTransaction Sys b s) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter Sys b s :=
  T.toLicensedSemanticKernelEmitterTransaction.toProjectiveRecordEmitter

/-- Licensed projective-emitter view of the same data. -/
def toLicensedProjectiveEmitterTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedSemanticKernelTransaction Sys b s) :
    LicensedProjectiveEmitterTransaction Sys b s :=
  T.toLicensedSemanticKernelEmitterTransaction.toLicensedProjectiveEmitterTransaction

@[simp] theorem toLicensedProjectiveEmitterTransaction_dimension
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedSemanticKernelTransaction Sys b s) :
    T.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.dimension
      = fun t => T.kernel.projectedRank.rank (T.kernel.project t) := rfl

theorem realizesComputationToConfessionBridge_of_one_le
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedSemanticKernelTransaction Sys b s)
    {K : Nat} (hK : 1 ≤ K) :
    T.toProjectiveRecordEmitter.RealizesComputationToConfessionBridge K := by
  exact
    T.toLicensedSemanticKernelEmitterTransaction.realizesComputationToConfessionBridge_of_one_le
      hK

end LicensedStageIndexedSemanticKernelTransaction

/-- A still-weaker transaction layer built directly from the raw stage-indexed
record-emitter interface, with no ambient kernel and no reconstructed
projective emitter. This is the right level for canonical-shadow dynamics: the
only data available is the emitted-record semantics along the canonical live
trace and the terminal record. -/
structure LicensedStageIndexedEmitterTransaction
    (Sys : BaseDuplicatingSystem) (b s : Sys.T) where
  emitter : BaseDuplicatingSystem.StageIndexedConservationEmitter Sys b s
  license : Prop
  licensed : license

namespace LicensedStageIndexedEmitterTransaction

/-- The canonical-shadow interface induced directly by the raw stage-indexed
emitter. -/
def shadowInterface
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedEmitterTransaction Sys b s) :
    BaseDuplicatingSystem.StageIndexedConservationEmitter.CanonicalShadowConservationInterface
      (Sys := Sys) :=
  T.emitter.toCanonicalShadowConservationInterface

/-- Shadow-side retained dimension. -/
def shadowDimension
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedEmitterTransaction Sys b s) :
    BaseDuplicatingSystem.StageIndexedConservationEmitter.ShadowObservation → Nat :=
  fun o => T.shadowInterface.projectedCoord o

/-- Shadow-side record coordinate. -/
def shadowRecordCoord
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedEmitterTransaction Sys b s) :
    BaseDuplicatingSystem.StageIndexedConservationEmitter.ShadowObservation → Nat :=
  fun o => T.shadowInterface.recordCoord o

end LicensedStageIndexedEmitterTransaction

/-- License invariance for the raw stage-indexed emitter transactions. -/
def StageIndexedShadowLicenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedStageIndexedEmitterTransaction Sys b s) : Prop :=
  ∀ i, (τ i).license = (τ 0).license

/-- Staticity on the canonical-shadow carrier induced directly by the raw
stage-indexed emitter interface. This is the weakest dynamic theorem currently
available in the library: it speaks only about the designated canonical shadow,
with no ambient projection kernel at all. -/
def IsCanonicalShadowStaticStageIndexedFamily
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedStageIndexedEmitterTransaction Sys b s) : Prop :=
  (∀ i o,
    (τ i).shadowDimension o = (τ 0).shadowDimension o)
    ∧ (∀ i o,
      (τ i).shadowRecordCoord o = (τ 0).shadowRecordCoord o)
    ∧ (∀ i, (τ i).license = (τ 0).license)

/-- The raw stage-indexed emitter layer already has invariant retained
dimension on the canonical shadow. -/
theorem stageIndexed_emitter_transaction_shadow_dimension_static
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedStageIndexedEmitterTransaction Sys b s) :
    ∀ i o, (τ i).shadowDimension o = (τ 0).shadowDimension o := by
  intro i o
  cases o with
  | live k j hj =>
      change ((τ i).shadowInterface).projectedCoord (.live k j hj)
        = ((τ 0).shadowInterface).projectedCoord (.live k j hj)
      rw [((τ i).shadowInterface).projected_live k j hj,
        ((τ 0).shadowInterface).projected_live k j hj]
  | terminal k =>
      change ((τ i).shadowInterface).projectedCoord (.terminal k)
        = ((τ 0).shadowInterface).projectedCoord (.terminal k)
      rw [((τ i).shadowInterface).projected_terminal k,
        ((τ 0).shadowInterface).projected_terminal k]

/-- The raw stage-indexed emitter layer also has invariant record coordinate on
the canonical shadow, because conservation plus the recovered projected
generator coordinate force the same residual value at every stage. -/
theorem stageIndexed_emitter_transaction_shadow_record_static
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedStageIndexedEmitterTransaction Sys b s) :
    ∀ i o, (τ i).shadowRecordCoord o = (τ 0).shadowRecordCoord o := by
  intro i o
  cases o with
  | live k j hj =>
      change ((τ i).shadowInterface).recordCoord (.live k j hj)
        = ((τ 0).shadowInterface).recordCoord (.live k j hj)
      have hcons_i := ((τ i).shadowInterface).conservation_live k j hj
      have hcons_0 := ((τ 0).shadowInterface).conservation_live k j hj
      rw [((τ i).shadowInterface).projected_live k j hj] at hcons_i
      rw [((τ 0).shadowInterface).projected_live k j hj] at hcons_0
      omega
  | terminal k =>
      change ((τ i).shadowInterface).recordCoord (.terminal k)
        = ((τ 0).shadowInterface).recordCoord (.terminal k)
      have hcons_i := ((τ i).shadowInterface).conservation_terminal k
      have hcons_0 := ((τ 0).shadowInterface).conservation_terminal k
      rw [((τ i).shadowInterface).projected_terminal k] at hcons_i
      rw [((τ 0).shadowInterface).projected_terminal k] at hcons_0
      omega

/-- Hence the raw stage-indexed emitter layer is already static on the
canonical shadow under license invariance, with no ambient kernel or projective
emitter package. -/
theorem stageIndexed_emitter_transaction_shadow_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedStageIndexedEmitterTransaction Sys b s)
    (hlic : StageIndexedShadowLicenseInvariant τ) :
    IsCanonicalShadowStaticStageIndexedFamily τ := by
  refine ⟨stageIndexed_emitter_transaction_shadow_dimension_static τ,
    stageIndexed_emitter_transaction_shadow_record_static τ, hlic⟩

/-- Projection-map invariance for a stage-indexed family of projective-emitter
transactions. This is the dynamic hypothesis needed in addition to generated
rank uniqueness: the external license may vary propositionally, but the actual
projection map used to read the generator coordinate must not drift across
stages. -/
def EmitterProjectionInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedProjectiveEmitterTransaction Sys b s) : Prop :=
  ∀ i, (τ i).emitter.project = (τ 0).emitter.project

/-- License invariance specialized to projective-emitter transactions. -/
def EmitterLicenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedProjectiveEmitterTransaction Sys b s) : Prop :=
  ∀ i, (τ i).license = (τ 0).license

/-- Invariance of the induced projected generator coordinate. This is weaker
than full projection-map invariance and is the right hypothesis once the actual
dynamic question is phrased at the level of the induced transaction dimension. -/
def EmitterDimensionInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedProjectiveEmitterTransaction Sys b s) : Prop :=
  ∀ i, (τ i).emitter.projectedGeneratorCoord = (τ 0).emitter.projectedGeneratorCoord

/-- Staticity restricted to the canonical live trace and terminal record image.
This is the critic-facing notion that matters for the computation-to-record
bridge: even if a family is not yet known to be globally static on the whole
ambient carrier, it may already be rigid on the designated states generated by
the canonical duplicating computation itself. -/
def IsCanonicalStaticProjectionFamily
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedProjectiveEmitterTransaction Sys b s) : Prop :=
  (∀ i k j, j ≤ k →
    (τ i).toProjectionTransaction.dimension (Sys.canonicalTrace b s k j)
      = (τ 0).toProjectionTransaction.dimension (Sys.canonicalTrace b s k j))
    ∧ (∀ i k,
      (τ i).toProjectionTransaction.dimension (Sys.wrapChain s k b)
        = (τ 0).toProjectionTransaction.dimension (Sys.wrapChain s k b))
    ∧ (∀ i, (τ i).license = (τ 0).license)
    ∧ (∀ i,
      (τ i).toProjectionTransaction.boundary = (τ 0).toProjectionTransaction.boundary)

/-- On any constructor-generated schema, every stage-wise projection rank in a
rank-based transaction family already collapses to the unique projection core. -/
theorem generated_rank_projection_transaction_rank_unique
    {S : StepDuplicatingSchema} (G : GeneratedByConstructors S)
    (τ : Nat → RankProjectionTransaction S) :
    ∀ i, (τ i).rank = (τ 0).rank := by
  intro i
  exact projectionRank_unique_of_generated G (τ i).rank (τ 0).rank

/-- Consequently, the projection-rank component of any such family is
extensionally constant on any constructor-generated schema. -/
theorem generated_rank_projection_transaction_rank_static
    {S : StepDuplicatingSchema} (G : GeneratedByConstructors S)
    (τ : Nat → RankProjectionTransaction S) :
    ∀ i, (τ i).rank = (τ 0).rank :=
  generated_rank_projection_transaction_rank_unique G τ

/-- With invariant license, every stage-indexed rank-based projection family on
any constructor-generated schema is static as a `ProjectionTransaction` family. -/
theorem generated_rank_projection_transaction_static_of_licenseInvariant
    {S : StepDuplicatingSchema} (G : GeneratedByConstructors S)
    (τ : Nat → RankProjectionTransaction S)
    (hlic : LicenseInvariant τ) :
    IsStaticProjectionFamily (fun i => (τ i).toProjectionTransaction) := by
  intro i
  refine ⟨?_, ?_, ?_⟩
  funext t
  exact congrArg (fun R : ProjectionRank S => R.rank t)
    (generated_rank_projection_transaction_rank_static G τ i)
  exact hlic i
  rw [RankProjectionTransaction.toProjectionTransaction_boundary,
    RankProjectionTransaction.toProjectionTransaction_boundary,
    generated_rank_projection_transaction_rank_static G τ i]

/-- On any constructor-generated schema, a stage-indexed family of licensed
projective emitters with invariant projection map and invariant license already
induces a static projection-transaction family. This is the critic-facing
dynamic rigidity theorem: once the projection map itself is stable, generated
rank uniqueness prevents any substantive stage-by-stage drift. -/
theorem generated_projective_emitter_transaction_static_of_invariants
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedProjectiveEmitterTransaction Sys b s)
    (hproj : EmitterProjectionInvariant τ)
    (hlic : EmitterLicenseInvariant τ) :
    IsStaticProjectionFamily (fun i => (τ i).toProjectionTransaction) := by
  have hdim : EmitterDimensionInvariant τ := by
    intro i
    funext t
    have hrank :
        (τ i).emitter.projectedRank = (τ 0).emitter.projectedRank := by
      exact projectionRank_unique_of_generated G
        (τ i).emitter.projectedRank (τ 0).emitter.projectedRank
    calc
      (τ i).emitter.projectedGeneratorCoord t
          = (τ i).emitter.projectedRank.rank ((τ i).emitter.project t) := by
              rfl
      _ = (τ 0).emitter.projectedRank.rank ((τ i).emitter.project t) := by
            exact congrArg
              (fun R : ProjectionRank Sys.toStepDuplicatingSchema =>
                R.rank ((τ i).emitter.project t)) hrank
      _ = (τ 0).emitter.projectedRank.rank ((τ 0).emitter.project t) := by
            rw [hproj i]
      _ = (τ 0).emitter.projectedGeneratorCoord t := by
            rfl
  intro i
  have hrank :
      (τ i).emitter.projectedRank = (τ 0).emitter.projectedRank := by
    exact projectionRank_unique_of_generated G
      (τ i).emitter.projectedRank (τ 0).emitter.projectedRank
  exact ⟨hdim i, hlic i, by
    rw [LicensedProjectiveEmitterTransaction.toProjectionTransaction_boundary,
      LicensedProjectiveEmitterTransaction.toProjectionTransaction_boundary,
      BaseDuplicatingSystem.ProjectiveRecordEmitter.toForgettingWitness,
      BaseDuplicatingSystem.ProjectiveRecordEmitter.toForgettingWitness,
      hrank]⟩

/-- On any constructor-generated schema, the forgetting-witness boundary part of
a projective-emitter transaction family is rigid regardless of stage. This is
the genuinely nontrivial part: once the projected rank is fixed by generated
uniqueness, the boundary cannot drift. -/
theorem generated_projective_emitter_transaction_boundary_static
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedProjectiveEmitterTransaction Sys b s) :
    ∀ i, (τ i).toProjectionTransaction.boundary = (τ 0).toProjectionTransaction.boundary := by
  intro i
  have hrank :
      (τ i).emitter.projectedRank = (τ 0).emitter.projectedRank := by
    exact projectionRank_unique_of_generated G
      (τ i).emitter.projectedRank (τ 0).emitter.projectedRank
  rw [LicensedProjectiveEmitterTransaction.toProjectionTransaction_boundary,
    LicensedProjectiveEmitterTransaction.toProjectionTransaction_boundary,
    BaseDuplicatingSystem.ProjectiveRecordEmitter.toForgettingWitness,
    BaseDuplicatingSystem.ProjectiveRecordEmitter.toForgettingWitness,
    hrank]

/-- Regardless of how the projection map itself may vary, every stage-wise
licensed projective emitter reads the same dimension on the canonical live
trace. This uses only the emitter's own canonical generator law, not any
ambient invariance hypothesis. -/
theorem projective_emitter_transaction_dimension_static_on_canonical_trace
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedProjectiveEmitterTransaction Sys b s) :
    ∀ i k j, j ≤ k →
      (τ i).toProjectionTransaction.dimension (Sys.canonicalTrace b s k j)
        = (τ 0).toProjectionTransaction.dimension (Sys.canonicalTrace b s k j) := by
  intro i k j hjk
  rw [LicensedProjectiveEmitterTransaction.toProjectionTransaction_dimension,
    LicensedProjectiveEmitterTransaction.toProjectionTransaction_dimension,
    BaseDuplicatingSystem.ProjectiveRecordEmitter.projectedGenerator_at_canonical
      (E := (τ i).emitter) k j hjk,
    BaseDuplicatingSystem.ProjectiveRecordEmitter.projectedGenerator_at_canonical
      (E := (τ 0).emitter) k j hjk]

/-- The same canonical rigidity holds at the terminal record. -/
theorem projective_emitter_transaction_dimension_static_at_terminal
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (τ : Nat → LicensedProjectiveEmitterTransaction Sys b s) :
    ∀ i k,
      (τ i).toProjectionTransaction.dimension (Sys.wrapChain s k b)
        = (τ 0).toProjectionTransaction.dimension (Sys.wrapChain s k b) := by
  intro i k
  rw [LicensedProjectiveEmitterTransaction.toProjectionTransaction_dimension,
    LicensedProjectiveEmitterTransaction.toProjectionTransaction_dimension,
    BaseDuplicatingSystem.ProjectiveRecordEmitter.projectedGenerator_at_terminal
      (E := (τ i).emitter) k,
    BaseDuplicatingSystem.ProjectiveRecordEmitter.projectedGenerator_at_terminal
      (E := (τ 0).emitter) k]

/-- On any constructor-generated schema, a stage-indexed family of licensed
projective emitters with invariant license is already static on the canonical
trace/terminal image, even without any separate dimension-invariance
hypothesis. The canonical dimension equations come for free from the emitter
laws themselves; only the forgetting boundary still needs generated uniqueness.
-/
theorem generated_projective_emitter_transaction_canonical_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedProjectiveEmitterTransaction Sys b s)
    (hlic : EmitterLicenseInvariant τ) :
    IsCanonicalStaticProjectionFamily τ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i k j hjk
    exact projective_emitter_transaction_dimension_static_on_canonical_trace τ i k j hjk
  · intro i k
    exact projective_emitter_transaction_dimension_static_at_terminal τ i k
  · exact hlic
  · exact generated_projective_emitter_transaction_boundary_static G τ

/-- The same canonical-staticity theorem already follows one layer lower, from
stage-indexed families built only from faithful emitters plus rank-level
kernels. This closes the gap between the computation-to-record bridge and the
projection-transaction layer: one does not need a separately postulated
projective emitter family to obtain canonical staticity. -/
theorem generated_rankKernel_emitter_transaction_canonical_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedRankKernelEmitterTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsCanonicalStaticProjectionFamily
      (fun i => (τ i).toLicensedProjectiveEmitterTransaction) := by
  apply generated_projective_emitter_transaction_canonical_static_of_licenseInvariant G
  intro i
  exact hlic i

/-- The same canonical-staticity theorem also follows from the semantically
stronger faithful-emitter + semantic-kernel layer. This keeps the dynamics
story aligned with the ambient semantic-kernel route already used on the
computation-to-record side. -/
theorem generated_semanticKernel_emitter_transaction_canonical_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedSemanticKernelEmitterTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsCanonicalStaticProjectionFamily
      (fun i => (τ i).toLicensedProjectiveEmitterTransaction) := by
  apply generated_projective_emitter_transaction_canonical_static_of_licenseInvariant G
  intro i
  exact hlic i

/-- On generated schemas, the semantic-kernel route already gives full ambient
staticity under license invariance alone: the semantic kernel itself is unique,
so the induced dimension cannot drift. -/
theorem generated_semanticKernel_emitter_transaction_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedSemanticKernelEmitterTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily
      (fun i => ((τ i).toLicensedProjectiveEmitterTransaction).toProjectionTransaction) := by
  have hdim :
      EmitterDimensionInvariant
        (fun i => (τ i).toLicensedProjectiveEmitterTransaction) := by
    intro i
    have hkernel :
        (τ i).kernel = (τ 0).kernel := by
      exact BaseDuplicatingSystem.SemanticProjectionKernel.unique_of_generated
        G (τ i).kernel (τ 0).kernel
    have hproj :
        (τ i).kernel.project = (τ 0).kernel.project := by
      exact congrArg BaseDuplicatingSystem.SemanticProjectionKernel.project hkernel
    have hrank :
        (τ i).kernel.projectedRank = (τ 0).kernel.projectedRank := by
      exact congrArg BaseDuplicatingSystem.SemanticProjectionKernel.projectedRank hkernel
    funext t
    calc
      (τ i).kernel.projectedRank.rank ((τ i).kernel.project t)
          = (τ 0).kernel.projectedRank.rank ((τ i).kernel.project t) := by
              exact congrArg
                (fun R : ProjectionRank Sys.toStepDuplicatingSchema =>
                  R.rank ((τ i).kernel.project t)) hrank
      _ = (τ 0).kernel.projectedRank.rank ((τ 0).kernel.project t) := by
            rw [hproj]
  intro i
  exact ⟨hdim i, hlic i,
    generated_projective_emitter_transaction_boundary_static G
      (fun j => (τ j).toLicensedProjectiveEmitterTransaction) i⟩

/-- The minimally strengthened coherent-projective route inherits the same
license-only ambient staticity theorem by canonically reconstructing the
semantic-kernel transaction layer. -/
theorem generated_coherentProjective_emitter_transaction_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedCoherentProjectiveEmitterTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily (fun i => (τ i).toProjectionTransaction) := by
  let ρ : Nat → LicensedSemanticKernelEmitterTransaction Sys b s :=
    fun i => (τ i).toLicensedSemanticKernelEmitterTransaction
  have hlicρ : ∀ i, (ρ i).license = (ρ 0).license := by
    intro i
    change (τ i).license = (τ 0).license
    exact hlic i
  simpa [ρ, LicensedCoherentProjectiveEmitterTransaction.toProjectionTransaction] using
    generated_semanticKernel_emitter_transaction_static_of_licenseInvariant
      (G := G) (τ := ρ) hlicρ

/-- Likewise, the full ambient staticity theorem under induced-dimension and
license invariance can already be driven from the weaker faithful-emitter +
rank-level-kernel layer. -/
theorem generated_rankKernel_emitter_transaction_static_of_dimension_and_license_invariants
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedRankKernelEmitterTransaction Sys b s)
    (hdim : EmitterDimensionInvariant
      (fun i => (τ i).toLicensedProjectiveEmitterTransaction))
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily
      (fun i => ((τ i).toLicensedProjectiveEmitterTransaction).toProjectionTransaction) := by
  intro i
  exact ⟨hdim i, hlic i,
    generated_projective_emitter_transaction_boundary_static G
      (fun j => (τ j).toLicensedProjectiveEmitterTransaction) i⟩

/-- The same full ambient staticity theorem also follows from the semantic
kernel route. -/
theorem generated_semanticKernel_emitter_transaction_static_of_dimension_and_license_invariants
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedSemanticKernelEmitterTransaction Sys b s)
    (hdim : EmitterDimensionInvariant
      (fun i => (τ i).toLicensedProjectiveEmitterTransaction))
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily
      (fun i => ((τ i).toLicensedProjectiveEmitterTransaction).toProjectionTransaction) := by
  intro i
  exact ⟨hdim i, hlic i,
    generated_projective_emitter_transaction_boundary_static G
      (fun j => (τ j).toLicensedProjectiveEmitterTransaction) i⟩

/-- The same canonical-staticity theorem also follows directly from the raw
stage-indexed emitter layer once an ambient semantic kernel is supplied. -/
theorem generated_stageIndexed_semanticKernel_transaction_canonical_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedStageIndexedSemanticKernelTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsCanonicalStaticProjectionFamily
      (fun i => (τ i).toLicensedProjectiveEmitterTransaction) := by
  apply generated_semanticKernel_emitter_transaction_canonical_static_of_licenseInvariant G
  intro i
  exact hlic i

/-- The same license-only ambient staticity theorem descends all the way to the
raw stage-indexed + semantic-kernel layer. -/
theorem generated_stageIndexed_semanticKernel_transaction_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedStageIndexedSemanticKernelTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily
      (fun i => ((τ i).toLicensedProjectiveEmitterTransaction).toProjectionTransaction) := by
  have hdim :
      EmitterDimensionInvariant
        (fun i => (τ i).toLicensedProjectiveEmitterTransaction) := by
    intro i
    have hkernel :
        (τ i).kernel = (τ 0).kernel := by
      exact BaseDuplicatingSystem.SemanticProjectionKernel.unique_of_generated
        G (τ i).kernel (τ 0).kernel
    have hproj :
        (τ i).kernel.project = (τ 0).kernel.project := by
      exact congrArg BaseDuplicatingSystem.SemanticProjectionKernel.project hkernel
    have hrank :
        (τ i).kernel.projectedRank = (τ 0).kernel.projectedRank := by
      exact congrArg BaseDuplicatingSystem.SemanticProjectionKernel.projectedRank hkernel
    funext t
    calc
      (τ i).kernel.projectedRank.rank ((τ i).kernel.project t)
          = (τ 0).kernel.projectedRank.rank ((τ i).kernel.project t) := by
              exact congrArg
                (fun R : ProjectionRank Sys.toStepDuplicatingSchema =>
                  R.rank ((τ i).kernel.project t)) hrank
      _ = (τ 0).kernel.projectedRank.rank ((τ 0).kernel.project t) := by
            rw [hproj]
  intro i
  exact ⟨hdim i, hlic i,
    generated_projective_emitter_transaction_boundary_static G
      (fun j => (τ j).toLicensedProjectiveEmitterTransaction) i⟩

/-- And the full ambient staticity theorem likewise descends to the raw
stage-indexed + semantic-kernel layer. -/
theorem generated_stageIndexed_semanticKernel_transaction_static_of_dimension_and_license_invariants
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedStageIndexedSemanticKernelTransaction Sys b s)
    (hdim : EmitterDimensionInvariant
      (fun i => (τ i).toLicensedProjectiveEmitterTransaction))
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily
      (fun i => ((τ i).toLicensedProjectiveEmitterTransaction).toProjectionTransaction) := by
  apply generated_semanticKernel_emitter_transaction_static_of_dimension_and_license_invariants G
  · exact hdim
  · exact hlic

/-- On a constructor-generated carrier, semantic-kernel completions are
canonical at the level of the induced transaction dimension. This makes the
remaining raw-emitter gap precise: existence of a semantic-kernel completion is
still extra data, but once such a completion exists it does not create further
non-uniqueness in the induced ambient dimension. -/
theorem generated_semanticKernel_completion_dimension_unique
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (T₁ T₂ : LicensedSemanticKernelEmitterTransaction Sys b s) :
    T₁.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.dimension
      = T₂.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.dimension := by
  let τ : Nat → LicensedSemanticKernelEmitterTransaction Sys b s
    | 0 => { emitter := T₁.emitter, kernel := T₁.kernel, projectedSeedZero := T₁.projectedSeedZero,
             license := True, licensed := trivial }
    | _ + 1 => { emitter := T₂.emitter, kernel := T₂.kernel, projectedSeedZero := T₂.projectedSeedZero,
                 license := True, licensed := trivial }
  have hstat :
      IsStaticProjectionFamily
        (fun i => ((τ i).toLicensedProjectiveEmitterTransaction).toProjectionTransaction) := by
    apply generated_semanticKernel_emitter_transaction_static_of_licenseInvariant G
    intro i
    cases i <;> rfl
  simpa [τ] using ((hstat 1).1).symm

/-- The same canonicality also holds for the induced forgetting boundary:
semantic-kernel completions on a generated carrier cannot disagree about the
confession-side boundary they induce. -/
theorem generated_semanticKernel_completion_boundary_unique
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (T₁ T₂ : LicensedSemanticKernelEmitterTransaction Sys b s) :
    T₁.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.boundary
      = T₂.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.boundary := by
  let τ : Nat → LicensedSemanticKernelEmitterTransaction Sys b s
    | 0 => { emitter := T₁.emitter, kernel := T₁.kernel, projectedSeedZero := T₁.projectedSeedZero,
             license := True, licensed := trivial }
    | _ + 1 => { emitter := T₂.emitter, kernel := T₂.kernel, projectedSeedZero := T₂.projectedSeedZero,
                 license := True, licensed := trivial }
  have hstat :
      IsStaticProjectionFamily
        (fun i => ((τ i).toLicensedProjectiveEmitterTransaction).toProjectionTransaction) := by
    apply generated_semanticKernel_emitter_transaction_static_of_licenseInvariant G
    intro i
    cases i <;> rfl
  simpa [τ] using ((hstat 1).2.2).symm

/-- The stage-indexed semantic-kernel route inherits the same completion
uniqueness at the dimension level. -/
theorem generated_stageIndexed_semanticKernel_completion_dimension_unique
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (T₁ T₂ : LicensedStageIndexedSemanticKernelTransaction Sys b s) :
    T₁.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.dimension
      = T₂.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.dimension := by
  exact generated_semanticKernel_completion_dimension_unique G
    T₁.toLicensedSemanticKernelEmitterTransaction
    T₂.toLicensedSemanticKernelEmitterTransaction

/-- The stage-indexed semantic-kernel route also inherits boundary uniqueness on
generated carriers. -/
theorem generated_stageIndexed_semanticKernel_completion_boundary_unique
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (T₁ T₂ : LicensedStageIndexedSemanticKernelTransaction Sys b s) :
    T₁.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.boundary
      = T₂.toLicensedProjectiveEmitterTransaction.toProjectionTransaction.boundary := by
  exact generated_semanticKernel_completion_boundary_unique G
    T₁.toLicensedSemanticKernelEmitterTransaction
    T₂.toLicensedSemanticKernelEmitterTransaction

/-- A semantic-kernel completion of a raw faithful emitter. This is weaker than
putting a kernel object directly in the transaction theorem statement: it only
asserts that the raw emitter admits some compatible semantic-kernel
realization. -/
structure FaithfulEmitterSemanticKernelCompletion
    (Sys : BaseDuplicatingSystem) (b s : Sys.T)
    (E : BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s) where
  kernel : BaseDuplicatingSystem.SemanticProjectionKernel Sys
  projectedSeedZero : kernel.projectedRank.rank (kernel.project b) = 0

namespace FaithfulEmitterSemanticKernelCompletion

def ofSemanticKernel
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    {E : BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s}
    (K : BaseDuplicatingSystem.SemanticProjectionKernel Sys)
    (hprojBase : K.projectedRank.rank (K.project b) = 0) :
    FaithfulEmitterSemanticKernelCompletion Sys b s E where
  kernel := K
  projectedSeedZero := hprojBase

def toLicensedSemanticKernelEmitterTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    {E : BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s}
    (C : FaithfulEmitterSemanticKernelCompletion Sys b s E)
    (license : Prop) (licensed : license) :
    LicensedSemanticKernelEmitterTransaction Sys b s where
  emitter := E
  kernel := C.kernel
  projectedSeedZero := C.projectedSeedZero
  license := license
  licensed := licensed

def toProjectionTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    {E : BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s}
    (C : FaithfulEmitterSemanticKernelCompletion Sys b s E)
    (license : Prop) (licensed : license) :
    ProjectionTransaction Sys.toStepDuplicatingSchema :=
  (C.toLicensedSemanticKernelEmitterTransaction license licensed).toLicensedProjectiveEmitterTransaction.toProjectionTransaction

/-- Canonical choice-based transaction induced by the existence of a compatible
semantic-kernel completion. -/
noncomputable def inducedProjectionTransaction
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (E : BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s)
    (hex : Nonempty (FaithfulEmitterSemanticKernelCompletion Sys b s E))
    (license : Prop) (licensed : license) :
    ProjectionTransaction Sys.toStepDuplicatingSchema :=
  (Classical.choice hex).toProjectionTransaction license licensed

/-- A semantically coherent generator-preserving emitter canonically yields a
compatible semantic-kernel completion of its underlying faithful emitter. This
makes completion existence derivable from weaker semantic data than an explicit
kernel object. -/
def ofSemanticGeneratorPreservingEmitter
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (E : BaseDuplicatingSystem.SemanticGeneratorPreservingRecordEmitter Sys b s)
    (hseed : E.generatorCoord (E.project b) = 0) :
    FaithfulEmitterSemanticKernelCompletion Sys b s E.toFaithfulRecordEmitter where
  kernel := E.toSemanticProjectionKernel
  projectedSeedZero := by
    simpa [BaseDuplicatingSystem.SemanticGeneratorPreservingRecordEmitter.toSemanticProjectionKernel,
      BaseDuplicatingSystem.GeneratorPreservingRecordEmitter.toProjectionRank]
      using hseed

/-- A constructor-recursion principle canonically yields a semantic-kernel
completion for any raw faithful emitter, because it builds the ambient
projection map and projection rank directly from the carrier structure rather
than from extra emitter-side packaging. -/
def ofConstructorRecursor
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    {E : BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s}
    (R : BaseDuplicatingSystem.ConstructorRecursor Sys)
    (hseed :
      (R.toSemanticProjectionKernel.projectedRank).rank
        ((R.toSemanticProjectionKernel.project) b) = 0) :
    FaithfulEmitterSemanticKernelCompletion Sys b s E where
  kernel := R.toSemanticProjectionKernel
  projectedSeedZero := hseed

end FaithfulEmitterSemanticKernelCompletion

/-- Generated-carrier ambient staticity for raw faithful-emitter families, with
no kernel object in the theorem statement: it is enough that each stage admits
some semantic-kernel completion. -/
theorem generated_faithful_emitter_transaction_static_of_completionExists
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s)
    (license : Nat → Prop)
    (licensed : ∀ i, license i)
    (hlic : ∀ i, license i = license 0)
    (hex : ∀ i, Nonempty (FaithfulEmitterSemanticKernelCompletion Sys b s (τ i))) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          (τ i) (hex i) (license i) (licensed i)) := by
  classical
  let κ : ∀ i, FaithfulEmitterSemanticKernelCompletion Sys b s (τ i) :=
    fun i => Classical.choice (hex i)
  let ρ : Nat → LicensedSemanticKernelEmitterTransaction Sys b s := fun i =>
    (κ i).toLicensedSemanticKernelEmitterTransaction (license i) (licensed i)
  have hstat :
      IsStaticProjectionFamily
        (fun i => (ρ i).toLicensedProjectiveEmitterTransaction.toProjectionTransaction) := by
    apply generated_semanticKernel_emitter_transaction_static_of_licenseInvariant G
    exact hlic
  simpa [FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction, κ, ρ]
    using hstat

/-- The same abstraction works directly for raw stage-indexed emitter families:
ambient staticity can be stated without exposing a kernel object, provided each
stage admits some faithful-emitter semantic-kernel completion. -/
theorem generated_stageIndexed_emitter_transaction_static_of_completionExists
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedStageIndexedEmitterTransaction Sys b s)
    (hlic : StageIndexedShadowLicenseInvariant τ)
    (hex : ∀ i, Nonempty (FaithfulEmitterSemanticKernelCompletion Sys b s ((τ i).emitter.toFaithfulRecordEmitter))) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          ((τ i).emitter.toFaithfulRecordEmitter) (hex i) (τ i).license (τ i).licensed) := by
  classical
  exact generated_faithful_emitter_transaction_static_of_completionExists
    (G := G)
    (τ := fun i => (τ i).emitter.toFaithfulRecordEmitter)
    (license := fun i => (τ i).license)
    (licensed := fun i => (τ i).licensed)
    (hlic := hlic)
    (hex := hex)

/-- The completion-existence theorem can be discharged uniformly from a single
ambient semantic kernel normalized at the base seed. This removes the need to
package a separate completion witness for each faithful emitter stage. -/
theorem generated_faithful_emitter_transaction_static_of_sharedSemanticKernel
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s)
    (license : Nat → Prop)
    (licensed : ∀ i, license i)
    (hlic : ∀ i, license i = license 0)
    (K : BaseDuplicatingSystem.SemanticProjectionKernel Sys)
    (hprojBase : K.projectedRank.rank (K.project b) = 0) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          (τ i)
          ⟨FaithfulEmitterSemanticKernelCompletion.ofSemanticKernel
            (E := τ i) K hprojBase⟩
          (license i) (licensed i)) := by
  exact generated_faithful_emitter_transaction_static_of_completionExists
    (G := G)
    (τ := τ)
    (license := license)
    (licensed := licensed)
    (hlic := hlic)
    (hex := fun i =>
      ⟨FaithfulEmitterSemanticKernelCompletion.ofSemanticKernel
        (E := τ i) K hprojBase⟩)

/-- The same shared ambient semantic kernel also suffices for raw
stage-indexed emitter families. This removes the need to postulate a
per-stage completion witness even at the weakest currently theorem-backed
ambient level. -/
theorem generated_stageIndexed_emitter_transaction_static_of_sharedSemanticKernel
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedStageIndexedEmitterTransaction Sys b s)
    (hlic : StageIndexedShadowLicenseInvariant τ)
    (K : BaseDuplicatingSystem.SemanticProjectionKernel Sys)
    (hprojBase : K.projectedRank.rank (K.project b) = 0) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          ((τ i).emitter.toFaithfulRecordEmitter)
          ⟨FaithfulEmitterSemanticKernelCompletion.ofSemanticKernel
            (E := (τ i).emitter.toFaithfulRecordEmitter) K hprojBase⟩
          (τ i).license (τ i).licensed) := by
  exact generated_stageIndexed_emitter_transaction_static_of_completionExists
    (G := G)
    (τ := τ)
    (hlic := hlic)
    (hex := fun i =>
      ⟨FaithfulEmitterSemanticKernelCompletion.ofSemanticKernel
        (E := (τ i).emitter.toFaithfulRecordEmitter) K hprojBase⟩)

/-- The same raw faithful-emitter ambient-staticity theorem can be discharged
from a genuine constructor-recursion principle on the ambient carrier. This is
the clean generic closure route once one stops asking the raw emitter data
alone to define ambient functions on `T`. -/
theorem generated_faithful_emitter_transaction_static_of_constructorRecursor
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s)
    (license : Nat → Prop)
    (licensed : ∀ i, license i)
    (hlic : ∀ i, license i = license 0)
    (R : BaseDuplicatingSystem.ConstructorRecursor Sys)
    (hprojBase :
      (R.toSemanticProjectionKernel.projectedRank).rank
        ((R.toSemanticProjectionKernel.project) b) = 0) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          (τ i)
          ⟨FaithfulEmitterSemanticKernelCompletion.ofConstructorRecursor
            (E := τ i) R hprojBase⟩
          (license i) (licensed i)) := by
  exact generated_faithful_emitter_transaction_static_of_sharedSemanticKernel
    (G := G)
    (τ := τ)
    (license := license)
    (licensed := licensed)
    (hlic := hlic)
    (K := R.toSemanticProjectionKernel)
    (hprojBase := hprojBase)

/-- Likewise for the raw stage-indexed emitter route: a constructor-recursion
principle on the ambient carrier is enough to close the theorem statement with
no separately packaged kernel object and no per-stage completion witnesses. -/
theorem generated_stageIndexed_emitter_transaction_static_of_constructorRecursor
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedStageIndexedEmitterTransaction Sys b s)
    (hlic : StageIndexedShadowLicenseInvariant τ)
    (R : BaseDuplicatingSystem.ConstructorRecursor Sys)
    (hprojBase :
      (R.toSemanticProjectionKernel.projectedRank).rank
        ((R.toSemanticProjectionKernel.project) b) = 0) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          ((τ i).emitter.toFaithfulRecordEmitter)
          ⟨FaithfulEmitterSemanticKernelCompletion.ofConstructorRecursor
            (E := (τ i).emitter.toFaithfulRecordEmitter) R hprojBase⟩
          (τ i).license (τ i).licensed) := by
  exact generated_stageIndexed_emitter_transaction_static_of_sharedSemanticKernel
    (G := G)
    (τ := τ)
    (hlic := hlic)
    (K := R.toSemanticProjectionKernel)
    (hprojBase := hprojBase)

/-- The completion-existence route can itself be discharged directly from the
weaker semantically coherent generator-preserving emitter layer. This removes
explicit kernel objects from the theorem statement while still proving full
ambient staticity on generated carriers. -/
theorem generated_semanticGeneratorPreserving_emitter_transaction_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedSemanticGeneratorPreservingEmitterTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily (fun i => (τ i).toProjectionTransaction) := by
  exact generated_semanticKernel_emitter_transaction_static_of_licenseInvariant
    (G := G)
    (τ := fun i => (τ i).toLicensedSemanticKernelEmitterTransaction)
    (hlic := by
      intro i
      simp [LicensedSemanticGeneratorPreservingEmitterTransaction.toLicensedSemanticKernelEmitterTransaction,
        hlic i])

namespace LicensedSemanticGeneratorPreservingEmitterTransaction

/-- The new semantic-generator-preserving transaction layer also canonically
produces a completion object for the underlying faithful emitter. -/
def toCompletion
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticGeneratorPreservingEmitterTransaction Sys b s) :
    FaithfulEmitterSemanticKernelCompletion Sys b s T.emitter.toFaithfulRecordEmitter :=
  FaithfulEmitterSemanticKernelCompletion.ofSemanticGeneratorPreservingEmitter
    T.emitter T.projectedSeedZero

end LicensedSemanticGeneratorPreservingEmitterTransaction

namespace LicensedSemanticConservationEmitterTransaction

/-- The weaker semantic-conservation transaction layer also canonically
produces a completion object for the underlying faithful emitter. -/
def toCompletion
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedSemanticConservationEmitterTransaction Sys b s) :
    FaithfulEmitterSemanticKernelCompletion Sys b s T.emitter.toFaithfulRecordEmitter :=
  FaithfulEmitterSemanticKernelCompletion.ofSemanticGeneratorPreservingEmitter
    T.emitter.toSemanticGeneratorPreservingRecordEmitter
    T.emitter.project_seed_zero

end LicensedSemanticConservationEmitterTransaction

namespace LicensedStageIndexedSemanticExtensionTransaction

/-- The weaker semantic raw stage-indexed extension layer also canonically
produces a completion object for the underlying faithful emitter. -/
def toCompletion
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (T : LicensedStageIndexedSemanticExtensionTransaction Sys b s) :
    FaithfulEmitterSemanticKernelCompletion Sys b s T.emitter.toFaithfulRecordEmitter :=
  (T.toLicensedSemanticConservationEmitterTransaction).toCompletion

end LicensedStageIndexedSemanticExtensionTransaction

/-- The same semantic-generator-preserving route can therefore also be viewed
as a genuine completion-existence theorem for raw faithful-emitter families. -/
theorem generated_semanticGeneratorPreserving_emitter_transaction_static_of_completionExists
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedSemanticGeneratorPreservingEmitterTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          ((τ i).emitter.toFaithfulRecordEmitter) ⟨(τ i).toCompletion⟩
          (τ i).license (τ i).licensed) := by
  exact generated_faithful_emitter_transaction_static_of_completionExists
    (G := G)
    (τ := fun i => (τ i).emitter.toFaithfulRecordEmitter)
    (license := fun i => (τ i).license)
    (licensed := fun i => (τ i).licensed)
    (hlic := hlic)
    (hex := fun i => ⟨(τ i).toCompletion⟩)

/-- The weaker semantic-conservation route also canonically yields completion
objects for the underlying faithful emitters, and therefore gives ambient
staticity with no explicit kernel object in the theorem statement. -/
theorem generated_semanticConservation_emitter_transaction_static_of_completionExists
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedSemanticConservationEmitterTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          ((τ i).emitter.toFaithfulRecordEmitter) ⟨(τ i).toCompletion⟩
          (τ i).license (τ i).licensed) := by
  exact generated_faithful_emitter_transaction_static_of_completionExists
    (G := G)
    (τ := fun i => (τ i).emitter.toFaithfulRecordEmitter)
    (license := fun i => (τ i).license)
    (licensed := fun i => (τ i).licensed)
    (hlic := hlic)
    (hex := fun i => ⟨(τ i).toCompletion⟩)

/-- The same weaker semantic-conservation route also yields direct ambient
staticity for its own induced projection-transaction family. -/
theorem generated_semanticConservation_emitter_transaction_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedSemanticConservationEmitterTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily (fun i => (τ i).toProjectionTransaction) := by
  exact generated_semanticKernel_emitter_transaction_static_of_licenseInvariant
    (G := G)
    (τ := fun i => (τ i).toLicensedSemanticKernelEmitterTransaction)
    (hlic := by
      intro i
      simp [LicensedSemanticConservationEmitterTransaction.toLicensedSemanticKernelEmitterTransaction,
        hlic i])

/-- The raw stage-indexed semantic-extension route also yields completion
objects canonically, and therefore ambient staticity with no explicit kernel
object in the theorem statement. -/
theorem generated_stageIndexed_semanticExtension_transaction_static_of_completionExists
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedStageIndexedSemanticExtensionTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          ((τ i).emitter.toFaithfulRecordEmitter) ⟨(τ i).toCompletion⟩
          (τ i).license (τ i).licensed) := by
  exact generated_faithful_emitter_transaction_static_of_completionExists
    (G := G)
    (τ := fun i => (τ i).emitter.toFaithfulRecordEmitter)
    (license := fun i => (τ i).license)
    (licensed := fun i => (τ i).licensed)
    (hlic := hlic)
    (hex := fun i => ⟨(τ i).toCompletion⟩)

/-- The same raw stage-indexed semantic-extension route also yields direct
ambient staticity for its own induced projection-transaction family. -/
theorem generated_stageIndexed_semanticExtension_transaction_static_of_licenseInvariant
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedStageIndexedSemanticExtensionTransaction Sys b s)
    (hlic : ∀ i, (τ i).license = (τ 0).license) :
    IsStaticProjectionFamily (fun i => (τ i).toProjectionTransaction) := by
  exact generated_semanticConservation_emitter_transaction_static_of_licenseInvariant
    (G := G)
    (τ := fun i => (τ i).toLicensedSemanticConservationEmitterTransaction)
    (hlic := by
      intro i
      simp [LicensedStageIndexedSemanticExtensionTransaction.toLicensedSemanticConservationEmitterTransaction,
        hlic i])

/-- With invariant induced dimension and invariant license, any stage-indexed
family of licensed projective emitters on a generated schema is already static
as a projection-transaction family. This weakens the earlier theorem by no
longer requiring the projection map itself to be frozen. -/
theorem generated_projective_emitter_transaction_static_of_dimension_and_license_invariants
    {Sys : BaseDuplicatingSystem} {b s : Sys.T}
    (G : GeneratedByConstructors Sys.toStepDuplicatingSchema)
    (τ : Nat → LicensedProjectiveEmitterTransaction Sys b s)
    (hdim : EmitterDimensionInvariant τ)
    (hlic : EmitterLicenseInvariant τ) :
    IsStaticProjectionFamily (fun i => (τ i).toProjectionTransaction) := by
  intro i
  exact ⟨hdim i, hlic i, generated_projective_emitter_transaction_boundary_static G τ i⟩

/-- On the free primitive syntax, every stage-wise projection rank is the
canonical counter-depth projection rank. -/
theorem free_rank_projection_transaction_rank_unique
    (τ : Nat → RankProjectionTransaction freeSchema) :
    ∀ i, (τ i).rank = freeProjectionRank := by
  intro i
  exact freeProjectionRank_unique ((τ i).rank)

/-- Consequently, the projection-rank component of any such family is
extensionally constant. -/
theorem free_rank_projection_transaction_rank_static
    (τ : Nat → RankProjectionTransaction freeSchema) :
    ∀ i, (τ i).rank = (τ 0).rank := by
  intro i
  rw [free_rank_projection_transaction_rank_unique τ i,
    free_rank_projection_transaction_rank_unique τ 0]

/-- With invariant license, every stage-indexed rank-based projection family on
the free primitive syntax is static as a `ProjectionTransaction` family. -/
theorem free_rank_projection_transaction_static_of_licenseInvariant
    (τ : Nat → RankProjectionTransaction freeSchema)
    (hlic : LicenseInvariant τ) :
    IsStaticProjectionFamily (fun i => (τ i).toProjectionTransaction) := by
  exact generated_rank_projection_transaction_static_of_licenseInvariant
    freeSchemaGenerated τ hlic

/-- The concrete free projective-emitter transaction is itself a rank-based
transaction. -/
def freeProjectiveRankTransaction : RankProjectionTransaction freeSchema where
  rank := freeProjectionRank
  license := True
  licensed := trivial

/-- The weaker rank-kernel transaction built from the concrete free faithful
record emitter. -/
def freeRankKernelFaithfulEmitterTransaction :
    LicensedRankKernelEmitterTransaction freeBaseSystem freeSeedX freeSeedY where
  emitter := freeFaithfulRecordEmitter
  kernel := freeRankLevelProjectionKernel
  projectedSeedZero := by
    simp [freeRankLevelProjectionKernel,
      BaseDuplicatingSystem.RankLevelProjectionKernel.ofSemanticProjectionKernel,
      freeSemanticProjectionKernel, freeProjectionRank, freeSeedX]
  license := True
  licensed := trivial

/-- The same weaker rank-kernel transaction built from the stage-indexed free
emitter after forgetting to the faithful-emitter layer. -/
def freeRankKernelStageIndexedEmitterTransaction :
    LicensedRankKernelEmitterTransaction freeBaseSystem freeSeedX freeSeedY where
  emitter := freeStageIndexedConservationEmitter.toFaithfulRecordEmitter
  kernel := freeRankLevelProjectionKernel
  projectedSeedZero := by
    simp [freeRankLevelProjectionKernel,
      BaseDuplicatingSystem.RankLevelProjectionKernel.ofSemanticProjectionKernel,
      freeSemanticProjectionKernel, freeProjectionRank, freeSeedX]
  license := True
  licensed := trivial

/-- The semantically richer transaction built from the concrete free faithful
record emitter plus the ambient semantic projection kernel. -/
def freeSemanticKernelFaithfulEmitterTransaction :
    LicensedSemanticKernelEmitterTransaction freeBaseSystem freeSeedX freeSeedY where
  emitter := freeFaithfulRecordEmitter
  kernel := freeSemanticProjectionKernel
  projectedSeedZero := by
    simp [freeSeedX, freeSemanticProjectionKernel, freeProjectionRank]
  license := True
  licensed := trivial

/-- The same semantic-kernel transaction built from the stage-indexed free
emitter after forgetting to the faithful-emitter layer. -/
def freeSemanticKernelStageIndexedEmitterTransaction :
    LicensedSemanticKernelEmitterTransaction freeBaseSystem freeSeedX freeSeedY where
  emitter := freeStageIndexedConservationEmitter.toFaithfulRecordEmitter
  kernel := freeSemanticProjectionKernel
  projectedSeedZero := by
    simp [freeSeedX, freeSemanticProjectionKernel, freeProjectionRank]
  license := True
  licensed := trivial

/-- The minimally strengthened coherent-projective transaction is realized on
the free primitive duplicator by the standard wrapper-forgetting projection. -/
def freeCoherentProjectiveEmitterTransaction :
    LicensedCoherentProjectiveEmitterTransaction freeBaseSystem freeSeedX freeSeedY where
  emitter := {
    toProjectiveRecordEmitter := freeProjectiveRecordEmitter
    project_base := by
      rfl
    project_succ := by
      intro t
      rfl
    project_wrap := by
      intro x y
      rfl
    project_recur := by
      intro b s n
      rfl
  }
  license := True
  licensed := trivial

/-- The semantically coherent generator-preserving free emitter viewed directly
through the new semantic-generator-preserving transaction layer. -/
def freeSemanticGeneratorPreservingEmitterTransaction :
    LicensedSemanticGeneratorPreservingEmitterTransaction
      freeBaseSystem freeSeedX freeSeedY where
  emitter := freeSemanticGeneratorPreservingRecordEmitter
  projectedSeedZero := by
    simp [freeSemanticGeneratorPreservingRecordEmitter,
      freeGeneratorPreservingRecordEmitter, freeSeedX]
  license := True
  licensed := trivial

/-- The weaker semantic-conservation free emitter viewed directly through the
new semantic-conservation transaction layer. -/
def freeSemanticConservationEmitterTransaction :
    LicensedSemanticConservationEmitterTransaction
      freeBaseSystem freeSeedX freeSeedY where
  emitter := freeSemanticConservationBasedGeneratorEmitter
  license := True
  licensed := trivial

/-- The raw stage-indexed free emitter equipped only with the weaker semantic
extension principle. -/
def freeStageIndexedSemanticExtensionTransaction :
    LicensedStageIndexedSemanticExtensionTransaction
      freeBaseSystem freeSeedX freeSeedY where
  emitter := freeStageIndexedConservationEmitter
  extension := freeStageIndexedSemanticExtension
  license := True
  licensed := trivial

/-- The raw stage-indexed free emitter viewed directly as a canonical-shadow
transaction, with no ambient kernel. -/
def freeStageIndexedShadowTransaction :
    LicensedStageIndexedEmitterTransaction freeBaseSystem freeSeedX freeSeedY where
  emitter := freeStageIndexedConservationEmitter
  license := True
  licensed := trivial

/-- The raw stage-indexed free emitter equipped with the ambient semantic
projection kernel. -/
def freeStageIndexedSemanticKernelTransaction :
    LicensedStageIndexedSemanticKernelTransaction freeBaseSystem freeSeedX freeSeedY where
  emitter := freeStageIndexedConservationEmitter
  kernel := freeSemanticProjectionKernel
  projectedSeedZero := by
    simp [freeSeedX, freeSemanticProjectionKernel, freeProjectionRank]
  license := True
  licensed := trivial

/-- The canonical free family is static for the substantive reason above. -/
theorem freeProjectiveRankTransaction_static :
    IsStaticProjectionFamily (fun _ => freeProjectiveRankTransaction.toProjectionTransaction) := by
  apply free_rank_projection_transaction_static_of_licenseInvariant
  intro i
  rfl

/-- The same substantive staticity holds for the canonical free projective
emitter family when read through the stronger projective-emitter interface. -/
theorem free_projective_emitter_transaction_static :
    IsStaticProjectionFamily (fun _ =>
      (LicensedProjectiveEmitterTransaction.mk
        freeProjectiveRecordEmitter True trivial).toProjectionTransaction) := by
  apply generated_projective_emitter_transaction_static_of_invariants freeSchemaGenerated
  · intro i
    rfl
  · intro i
    rfl

/-- The same free family is canonically static on the designated trace/terminal
states even without separately postulating dimension invariance. -/
theorem free_projective_emitter_transaction_canonical_static :
    IsCanonicalStaticProjectionFamily (fun _ =>
      LicensedProjectiveEmitterTransaction.mk freeProjectiveRecordEmitter True trivial) := by
  apply generated_projective_emitter_transaction_canonical_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- The weaker faithful-emitter + rank-level-kernel route already yields the
same canonical staticity on the free primitive duplicator. -/
theorem free_rankKernel_faithful_emitter_transaction_canonical_static :
    IsCanonicalStaticProjectionFamily (fun _ =>
      freeRankKernelFaithfulEmitterTransaction.toLicensedProjectiveEmitterTransaction) := by
  apply generated_rankKernel_emitter_transaction_canonical_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- The stage-indexed free emitter also inherits the same canonical staticity
through the weaker faithful-emitter + rank-level-kernel route. -/
theorem free_rankKernel_stageIndexed_emitter_transaction_canonical_static :
    IsCanonicalStaticProjectionFamily (fun _ =>
      freeRankKernelStageIndexedEmitterTransaction.toLicensedProjectiveEmitterTransaction) := by
  apply generated_rankKernel_emitter_transaction_canonical_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- The semantic-kernel route already yields the same canonical staticity on the
free primitive duplicator. -/
theorem free_semanticKernel_faithful_emitter_transaction_canonical_static :
    IsCanonicalStaticProjectionFamily (fun _ =>
      freeSemanticKernelFaithfulEmitterTransaction.toLicensedProjectiveEmitterTransaction) := by
  apply generated_semanticKernel_emitter_transaction_canonical_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- The stage-indexed free emitter inherits the same canonical staticity through
the faithful-emitter + semantic-kernel route. -/
theorem free_semanticKernel_stageIndexed_emitter_transaction_canonical_static :
    IsCanonicalStaticProjectionFamily (fun _ =>
      freeSemanticKernelStageIndexedEmitterTransaction.toLicensedProjectiveEmitterTransaction) := by
  apply generated_semanticKernel_emitter_transaction_canonical_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- On the free primitive duplicator, the semantic-kernel faithful-emitter route
is fully ambient-static under license invariance alone. -/
theorem free_semanticKernel_faithful_emitter_transaction_static :
    IsStaticProjectionFamily (fun _ =>
      freeSemanticKernelFaithfulEmitterTransaction.toLicensedProjectiveEmitterTransaction.toProjectionTransaction) := by
  apply generated_semanticKernel_emitter_transaction_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- The stage-indexed emitter inherits the same license-only ambient staticity
through the faithful-emitter + semantic-kernel route. -/
theorem free_semanticKernel_stageIndexed_emitter_transaction_static :
    IsStaticProjectionFamily (fun _ =>
      freeSemanticKernelStageIndexedEmitterTransaction.toLicensedProjectiveEmitterTransaction.toProjectionTransaction) := by
  apply generated_semanticKernel_emitter_transaction_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- The minimally strengthened coherent-projective route is likewise static on
the free primitive duplicator. -/
theorem free_coherentProjective_emitter_transaction_static :
    IsStaticProjectionFamily (fun _ =>
      freeCoherentProjectiveEmitterTransaction.toProjectionTransaction) := by
  apply generated_coherentProjective_emitter_transaction_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- The semantic-generator-preserving transaction layer is also fully
ambient-static on the free primitive duplicator under license invariance
alone. -/
theorem free_semanticGeneratorPreserving_emitter_transaction_static :
    IsStaticProjectionFamily (fun _ =>
      freeSemanticGeneratorPreservingEmitterTransaction.toProjectionTransaction) := by
  apply generated_semanticGeneratorPreserving_emitter_transaction_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- The weaker semantic-conservation transaction layer is also fully
ambient-static on the free primitive duplicator. -/
theorem free_semanticConservation_emitter_transaction_static :
    IsStaticProjectionFamily (fun _ =>
      freeSemanticConservationEmitterTransaction.toProjectionTransaction) := by
  apply generated_semanticConservation_emitter_transaction_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- The raw stage-indexed semantic-extension layer is likewise ambient-static on
the free primitive duplicator. -/
theorem free_stageIndexed_semanticExtension_transaction_static :
    IsStaticProjectionFamily (fun _ =>
      freeStageIndexedSemanticExtensionTransaction.toProjectionTransaction) := by
  apply generated_stageIndexed_semanticExtension_transaction_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- The same canonical staticity now also starts directly from the raw
stage-indexed emitter interface, once the ambient semantic kernel is supplied. -/
theorem free_stageIndexed_semanticKernel_transaction_canonical_static :
    IsCanonicalStaticProjectionFamily (fun _ =>
      freeStageIndexedSemanticKernelTransaction.toLicensedProjectiveEmitterTransaction) := by
  apply generated_stageIndexed_semanticKernel_transaction_canonical_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- And the same raw stage-indexed + semantic-kernel route is fully
ambient-static on the free primitive duplicator under license invariance alone. -/
theorem free_stageIndexed_semanticKernel_transaction_static :
    IsStaticProjectionFamily (fun _ =>
      freeStageIndexedSemanticKernelTransaction.toLicensedProjectiveEmitterTransaction.toProjectionTransaction) := by
  apply generated_stageIndexed_semanticKernel_transaction_static_of_licenseInvariant
    freeSchemaGenerated
  intro i
  rfl

/-- Direct free-carrier ambient staticity from the raw faithful-emitter
interface itself, with no ambient-kernel object in the theorem statement. -/
theorem free_faithful_emitter_transaction_static_of_licenseInvariant
    (τ : Nat → BaseDuplicatingSystem.FaithfulRecordEmitter freeBaseSystem freeSeedX freeSeedY)
    (license : Nat → Prop)
    (licensed : ∀ i, license i)
    (hlic : ∀ i, license i = license 0) :
    IsStaticProjectionFamily (fun i =>
      (((BaseDuplicatingSystem.FaithfulRecordEmitter.toFreeAmbientConservationBasedGeneratorEmitter
          (τ i)).toProjectedGeneratorWitness.toProjectiveRecordEmitter).toProjectionTransaction
            (license i) (licensed i))) := by
  let ρ : Nat → LicensedProjectiveEmitterTransaction freeBaseSystem freeSeedX freeSeedY :=
    fun j => {
      emitter :=
        (BaseDuplicatingSystem.FaithfulRecordEmitter.toFreeAmbientConservationBasedGeneratorEmitter
          (τ j)).toProjectedGeneratorWitness.toProjectiveRecordEmitter
      license := license j
      licensed := licensed j
    }
  intro i
  refine ⟨?_, hlic i, ?_⟩
  · funext t
    rfl
  · simpa [ρ] using
      generated_projective_emitter_transaction_boundary_static freeSchemaGenerated ρ i

/-- The same direct free-carrier ambient staticity theorem starts from the raw
stage-indexed emitter interface, again with no ambient-kernel object in the
theorem statement. -/
theorem free_stageIndexed_emitter_transaction_static_of_licenseInvariant
    (τ : Nat → LicensedStageIndexedEmitterTransaction freeBaseSystem freeSeedX freeSeedY)
    (hlic : StageIndexedShadowLicenseInvariant τ) :
    IsStaticProjectionFamily (fun i =>
      (((BaseDuplicatingSystem.FaithfulRecordEmitter.toFreeAmbientConservationBasedGeneratorEmitter
          ((τ i).emitter.toFaithfulRecordEmitter)).toProjectedGeneratorWitness.toProjectiveRecordEmitter).toProjectionTransaction
            (τ i).license (τ i).licensed)) := by
  let ρ : Nat → LicensedProjectiveEmitterTransaction freeBaseSystem freeSeedX freeSeedY :=
    fun j => {
      emitter :=
        (BaseDuplicatingSystem.FaithfulRecordEmitter.toFreeAmbientConservationBasedGeneratorEmitter
          ((τ j).emitter.toFaithfulRecordEmitter)).toProjectedGeneratorWitness.toProjectiveRecordEmitter
      license := (τ j).license
      licensed := (τ j).licensed
    }
  intro i
  refine ⟨?_, hlic i, ?_⟩
  · funext t
    rfl
  · simpa [ρ] using
      generated_projective_emitter_transaction_boundary_static freeSchemaGenerated ρ i

/-- The free faithful-emitter route also closes through the ambient
constructor-recursion principle alone. This is the generic constructor-recursion
closure route specialized to the primitive duplicator. -/
theorem free_faithful_emitter_transaction_static_of_constructorRecursor
    (τ : Nat → BaseDuplicatingSystem.FaithfulRecordEmitter freeBaseSystem freeSeedX freeSeedY)
    (license : Nat → Prop)
    (licensed : ∀ i, license i)
    (hlic : ∀ i, license i = license 0) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          (τ i)
          ⟨FaithfulEmitterSemanticKernelCompletion.ofConstructorRecursor
            (E := τ i) freeConstructorRecursor freeConstructorRecursor_project_seedX_zero⟩
          (license i) (licensed i)) := by
  exact generated_faithful_emitter_transaction_static_of_constructorRecursor
    (G := freeSchemaGenerated)
    (τ := τ)
    (license := license)
    (licensed := licensed)
    (hlic := hlic)
    (R := freeConstructorRecursor)
    (hprojBase := freeConstructorRecursor_project_seedX_zero)

/-- The same ambient constructor-recursion route also closes the free raw
stage-indexed family. -/
theorem free_stageIndexed_emitter_transaction_static_of_constructorRecursor
    (τ : Nat → LicensedStageIndexedEmitterTransaction freeBaseSystem freeSeedX freeSeedY)
    (hlic : StageIndexedShadowLicenseInvariant τ) :
    IsStaticProjectionFamily
      (fun i =>
        FaithfulEmitterSemanticKernelCompletion.inducedProjectionTransaction
          ((τ i).emitter.toFaithfulRecordEmitter)
          ⟨FaithfulEmitterSemanticKernelCompletion.ofConstructorRecursor
            (E := (τ i).emitter.toFaithfulRecordEmitter)
            freeConstructorRecursor freeConstructorRecursor_project_seedX_zero⟩
          (τ i).license (τ i).licensed) := by
  exact generated_stageIndexed_emitter_transaction_static_of_constructorRecursor
    (G := freeSchemaGenerated)
    (τ := τ)
    (hlic := hlic)
    (R := freeConstructorRecursor)
    (hprojBase := freeConstructorRecursor_project_seedX_zero)

/-- A concrete off-trace term used to witness that the raw projective-emitter
interface is still too weak for full ambient staticity without extra dimension
control. -/
def freeProjectiveEmitterAnomalyTerm : freeBaseSystem.T :=
  FreeTerm.wrap FreeTerm.base FreeTerm.base

/-- A modified ambient projection that agrees with the standard projection on
the canonical trace and terminal record, but differs on one off-trace term. -/
noncomputable def freeGeneratorProjectionAnomalous : freeBaseSystem.T → freeBaseSystem.T := by
  classical
  intro t
  exact if t = freeProjectiveEmitterAnomalyTerm then
    FreeTerm.succ FreeTerm.base
  else
    freeGeneratorProjection t

@[simp] theorem freeGeneratorProjectionAnomalous_on_anomaly :
    freeGeneratorProjectionAnomalous freeProjectiveEmitterAnomalyTerm
      = FreeTerm.succ FreeTerm.base := by
  classical
  simp [freeGeneratorProjectionAnomalous, freeProjectiveEmitterAnomalyTerm]

@[simp] theorem freeGeneratorProjectionAnomalous_off_anomaly
    {t : freeBaseSystem.T} (ht : t ≠ freeProjectiveEmitterAnomalyTerm) :
    freeGeneratorProjectionAnomalous t = freeGeneratorProjection t := by
  classical
  simp [freeGeneratorProjectionAnomalous, ht]

theorem freeCanonicalTrace_ne_projectiveEmitterAnomaly
    (k i : Nat) (hik : i ≤ k) :
    freeBaseSystem.canonicalTrace freeSeedX freeSeedY k i
      ≠ freeProjectiveEmitterAnomalyTerm := by
  intro h
  cases i with
  | zero =>
      simp [BaseDuplicatingSystem.canonicalTrace, freeBaseSystem, freeSchema,
        freeSeedX, freeSeedY, freeProjectiveEmitterAnomalyTerm] at h
  | succ i' =>
      simp [BaseDuplicatingSystem.canonicalTrace, BaseDuplicatingSystem.wrapChain,
        freeBaseSystem, freeSchema, freeSeedX, freeSeedY,
        freeProjectiveEmitterAnomalyTerm] at h

theorem freeWrapChain_ne_projectiveEmitterAnomaly (k : Nat) :
    freeBaseSystem.wrapChain freeSeedY k freeSeedX
      ≠ freeProjectiveEmitterAnomalyTerm := by
  intro h
  cases k with
  | zero =>
      simp [BaseDuplicatingSystem.wrapChain, freeBaseSystem, freeSchema,
        freeSeedX, freeProjectiveEmitterAnomalyTerm] at h
  | succ k' =>
      simp [BaseDuplicatingSystem.wrapChain, freeBaseSystem, freeSchema,
        freeSeedX, freeSeedY, freeProjectiveEmitterAnomalyTerm] at h

/-- A second projective emitter on the free primitive duplicator that agrees
with the canonical one on the live trace and terminal record, but differs on an
off-trace ambient term. This witnesses that raw projective-emitter data alone
does not force full ambient staticity. -/
noncomputable def freeAnomalousProjectiveRecordEmitter :
    BaseDuplicatingSystem.ProjectiveRecordEmitter freeBaseSystem freeSeedX freeSeedY where
  toFaithfulRecordEmitter := freeFaithfulRecordEmitter
  project := freeGeneratorProjectionAnomalous
  projectedRank := by
    simpa [freeBaseSystem, freeSchema] using freeProjectionRank
  project_canonical := by
    intro k i hik
    have hne :
        freeBaseSystem.canonicalTrace freeSeedX freeSeedY k i
          ≠ freeProjectiveEmitterAnomalyTerm :=
      freeCanonicalTrace_ne_projectiveEmitterAnomaly k i hik
    rw [freeGeneratorProjectionAnomalous_off_anomaly hne]
    simpa [freeBaseSystem, freeSchema] using freeProjectedRank_canonicalTrace k i hik
  project_terminal := by
    intro k
    have hne :
        freeBaseSystem.wrapChain freeSeedY k freeSeedX
          ≠ freeProjectiveEmitterAnomalyTerm :=
      freeWrapChain_ne_projectiveEmitterAnomaly k
    rw [freeGeneratorProjectionAnomalous_off_anomaly hne]
    simpa [freeBaseSystem, freeSchema] using freeProjectedRank_terminal k

/-- The anomalous free projection fails the minimal wrap-coherence law, which
is exactly why it is excluded by `CoherentProjectiveRecordEmitter`. -/
theorem freeAnomalousProjectiveRecordEmitter_not_wrapCoherent :
    ¬ ∀ x y,
      freeAnomalousProjectiveRecordEmitter.project (freeBaseSystem.wrap x y)
        = freeAnomalousProjectiveRecordEmitter.project y := by
  intro hwrap
  have h := hwrap FreeTerm.base FreeTerm.base
  change freeGeneratorProjectionAnomalous freeProjectiveEmitterAnomalyTerm
      = freeGeneratorProjectionAnomalous FreeTerm.base at h
  simp [freeGeneratorProjectionAnomalous, freeProjectiveEmitterAnomalyTerm] at h

/-- A two-stage raw projective-emitter family with invariant license but
different ambient dimension on an off-trace term. -/
noncomputable def freeRawProjectiveEmitterCounterexample :
    Nat → LicensedProjectiveEmitterTransaction freeBaseSystem freeSeedX freeSeedY
  | 0 => ⟨freeProjectiveRecordEmitter, True, trivial⟩
  | _ + 1 => ⟨freeAnomalousProjectiveRecordEmitter, True, trivial⟩

theorem freeRawProjectiveEmitterCounterexample_licenseInvariant :
    EmitterLicenseInvariant freeRawProjectiveEmitterCounterexample := by
  intro i
  cases i <;> rfl

theorem freeRawProjectiveEmitterCounterexample_not_dimensionInvariant :
    ¬ EmitterDimensionInvariant freeRawProjectiveEmitterCounterexample := by
  intro hdim
  have hdim1 := hdim 1
  have h0 :
      (freeRawProjectiveEmitterCounterexample 0).toProjectionTransaction.dimension
        freeProjectiveEmitterAnomalyTerm = 0 := by
    change freeCounterDepth (freeGeneratorProjection freeProjectiveEmitterAnomalyTerm) = 0
    simp [freeProjectiveEmitterAnomalyTerm, freeGeneratorProjection]
  have h1 :
      (freeRawProjectiveEmitterCounterexample 1).toProjectionTransaction.dimension
        freeProjectiveEmitterAnomalyTerm = 1 := by
    classical
    change freeCounterDepth (freeGeneratorProjectionAnomalous freeProjectiveEmitterAnomalyTerm) = 1
    simp [freeProjectiveEmitterAnomalyTerm, freeGeneratorProjectionAnomalous]
  have hval :
      (freeRawProjectiveEmitterCounterexample 1).toProjectionTransaction.dimension
        freeProjectiveEmitterAnomalyTerm
        =
      (freeRawProjectiveEmitterCounterexample 0).toProjectionTransaction.dimension
        freeProjectiveEmitterAnomalyTerm := by
    simpa [LicensedProjectiveEmitterTransaction.toProjectionTransaction_dimension] using
      congrArg (fun f : freeBaseSystem.T → Nat => f freeProjectiveEmitterAnomalyTerm) hdim1
  rw [h1, h0] at hval
  omega

/-- Consequently, the completely raw projective-emitter route really does need
extra ambient dimension control: license invariance alone does not force full
ambient staticity. -/
theorem freeRawProjectiveEmitterCounterexample_not_static :
    ¬ IsStaticProjectionFamily
      (fun i => (freeRawProjectiveEmitterCounterexample i).toProjectionTransaction) := by
  intro hstatic
  have h0 :
      (freeRawProjectiveEmitterCounterexample 0).toProjectionTransaction.dimension
        freeProjectiveEmitterAnomalyTerm = 0 := by
    change freeCounterDepth (freeGeneratorProjection freeProjectiveEmitterAnomalyTerm) = 0
    simp [freeProjectiveEmitterAnomalyTerm, freeGeneratorProjection]
  have h1 :
      (freeRawProjectiveEmitterCounterexample 1).toProjectionTransaction.dimension
        freeProjectiveEmitterAnomalyTerm = 1 := by
    classical
    change freeCounterDepth (freeGeneratorProjectionAnomalous freeProjectiveEmitterAnomalyTerm) = 1
    simp [freeProjectiveEmitterAnomalyTerm, freeGeneratorProjectionAnomalous]
  have hval :
      (freeRawProjectiveEmitterCounterexample 1).toProjectionTransaction.dimension
        freeProjectiveEmitterAnomalyTerm
        =
      (freeRawProjectiveEmitterCounterexample 0).toProjectionTransaction.dimension
        freeProjectiveEmitterAnomalyTerm := by
    exact congrArg
      (fun f : freeBaseSystem.T → Nat => f freeProjectiveEmitterAnomalyTerm) (hstatic 1).1
  rw [h1, h0] at hval
  omega

/-- Arbitrary-carrier obstruction used to show that the completely raw
faithful/stage-indexed emitter interfaces do not force semantic-kernel
completion. It contains the free primitive duplicator as a good fragment plus a
single bad point fixed by `succ`. -/
def obstructionBaseSystem : BaseDuplicatingSystem where
  T := Option FreeTerm
  base := some FreeTerm.base
  succ
    | some t => some (.succ t)
    | none => none
  wrap
    | some x, some y => some (.wrap x y)
    | _, _ => none
  recur
    | some b, some s, some n => some (.recur b s n)
    | _, _, _ => none
  Step := fun _ _ => True
  dup_step := by
    intro b s n
    trivial
  base_step := by
    intro b s
    trivial

def obstructionSeedX : obstructionBaseSystem.T := some FreeTerm.base
def obstructionSeedY : obstructionBaseSystem.T := some (FreeTerm.succ FreeTerm.base)

@[simp] theorem obstruction_counter_some (k : Nat) :
    obstructionBaseSystem.counter k = some (freeBaseSystem.counter k) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      change obstructionBaseSystem.succ (obstructionBaseSystem.counter k)
        = some (freeBaseSystem.succ (freeBaseSystem.counter k))
      rw [ih]
      rfl

@[simp] theorem obstruction_wrapChain_some (i : Nat) (t : FreeTerm) :
    obstructionBaseSystem.wrapChain obstructionSeedY i (some t)
      = some (freeBaseSystem.wrapChain freeSeedY i t) := by
  induction i generalizing t with
  | zero =>
      rfl
  | succ i ih =>
      change obstructionBaseSystem.wrap obstructionSeedY
          (obstructionBaseSystem.wrapChain obstructionSeedY i (some t))
        = some (freeBaseSystem.wrap freeSeedY (freeBaseSystem.wrapChain freeSeedY i t))
      rw [ih]
      rfl

@[simp] theorem obstruction_terminal_some (k : Nat) :
    obstructionBaseSystem.wrapChain obstructionSeedY k obstructionSeedX
      = some (freeBaseSystem.wrapChain freeSeedY k freeSeedX) := by
  simp [obstructionSeedX, freeSeedX]

@[simp] theorem obstruction_canonicalTrace_some (k i : Nat) (_hik : i ≤ k) :
    obstructionBaseSystem.canonicalTrace obstructionSeedX obstructionSeedY k i
      = some (freeBaseSystem.canonicalTrace freeSeedX freeSeedY k i) := by
  unfold BaseDuplicatingSystem.canonicalTrace
  rw [obstruction_counter_some]
  change obstructionBaseSystem.wrapChain obstructionSeedY i
      (some (FreeTerm.recur FreeTerm.base (FreeTerm.succ FreeTerm.base) (freeBaseSystem.counter (k - i))))
    = some (freeBaseSystem.wrapChain freeSeedY i
        (freeBaseSystem.recur freeSeedX freeSeedY (freeBaseSystem.counter (k - i))))
  rw [obstruction_wrapChain_some i
    (FreeTerm.recur FreeTerm.base (FreeTerm.succ FreeTerm.base) (freeBaseSystem.counter (k - i)))]
  rfl

/-- Raw faithful emitter on the good fragment of `obstructionBaseSystem`. -/
def obstructionFaithfulRecordEmitter :
    BaseDuplicatingSystem.FaithfulRecordEmitter
      obstructionBaseSystem obstructionSeedX obstructionSeedY where
  LiveObs := Bool
  liveObsDecEq := inferInstance
  RecordObs := Nat
  liveObs
    | some t => freeFaithfulRecordEmitter.liveObs t
    | none => false
  recordObs
    | some t => freeFaithfulRecordEmitter.recordObs t
    | none => 0
  liveToken := freeFaithfulRecordEmitter.liveToken
  terminalToken := freeFaithfulRecordEmitter.terminalToken
  decodeRecord := id
  live_at_canonical := by
    intro k i hik
    simpa [obstruction_canonicalTrace_some k i hik] using
      freeFaithfulRecordEmitter.live_at_canonical k i hik
  live_at_terminal := by
    intro k
    simpa [obstruction_terminal_some k] using
      freeFaithfulRecordEmitter.live_at_terminal k
  live_token_ne_terminal := by
    simpa using freeFaithfulRecordEmitter.live_token_ne_terminal
  decode_record_at_canonical := by
    intro k i hik
    simpa [obstruction_canonicalTrace_some k i hik] using
      freeFaithfulRecordEmitter.decode_record_at_canonical k i hik
  decode_record_at_terminal := by
    intro k
    simpa [obstruction_terminal_some k] using
      freeFaithfulRecordEmitter.decode_record_at_terminal k

/-- Raw stage-indexed emitter on the same obstructed carrier. -/
def obstructionStageIndexedConservationEmitter :
    BaseDuplicatingSystem.StageIndexedConservationEmitter
      obstructionBaseSystem obstructionSeedX obstructionSeedY where
  toFaithfulRecordEmitter := obstructionFaithfulRecordEmitter
  projectedStageCoord := BaseDuplicatingSystem.trace_ctr
  projectedTerminalCoord := fun _ => 0
  conservation_at_canonical := by
    intro k i hik
    rw [obstructionFaithfulRecordEmitter.decode_record_at_canonical k i hik]
    simp [BaseDuplicatingSystem.trace_ctr]
    omega
  conservation_at_terminal := by
    intro k
    rw [obstructionFaithfulRecordEmitter.decode_record_at_terminal k]
    omega

/-- The obstructed carrier admits no projection rank at all, because `succ none
= none` would force `rank none = rank none + 1`. -/
theorem obstructionBaseSystem_no_projectionRank :
    ¬ Nonempty (ProjectionRank obstructionBaseSystem.toStepDuplicatingSchema) := by
  intro h
  rcases h with ⟨R⟩
  have hsucc : R.rank none = R.rank none + 1 := by
    simpa [obstructionBaseSystem] using R.rank_succ none
  omega

/-- Hence the obstructed carrier admits no semantic projection kernel. -/
theorem obstructionBaseSystem_no_semanticProjectionKernel :
    ¬ Nonempty (BaseDuplicatingSystem.SemanticProjectionKernel obstructionBaseSystem) := by
  intro h
  rcases h with ⟨K⟩
  exact obstructionBaseSystem_no_projectionRank ⟨K.projectedRank⟩

/-- The same bad fixed point also blocks any genuine constructor-recursion
principle on the obstructed carrier. So the new constructor-recursion closure
route is not arbitrary: it excludes exactly the junk ambient carrier that
breaks the naive raw theorem. -/
theorem obstructionBaseSystem_no_constructorRecursor :
    ¬ Nonempty (BaseDuplicatingSystem.ConstructorRecursor obstructionBaseSystem) := by
  intro h
  rcases h with ⟨R⟩
  have hnone :
      R.fold (α := Nat) 0 (fun n => n + 1) (fun _ y => y) (fun _ _ n => n) none
        = R.fold (α := Nat) 0 (fun n => n + 1) (fun _ y => y) (fun _ _ n => n) none + 1 := by
    simpa [obstructionBaseSystem, Nat.add_comm] using
      (R.fold_succ (α := Nat) 0 (fun n => n + 1) (fun _ y => y) (fun _ _ n => n) none)
  omega

/-- Therefore the raw faithful emitter on the obstructed carrier admits no
semantic-kernel completion. -/
theorem obstructionFaithfulRecordEmitter_no_completion :
    ¬ Nonempty
      (FaithfulEmitterSemanticKernelCompletion
        obstructionBaseSystem obstructionSeedX obstructionSeedY
        obstructionFaithfulRecordEmitter) := by
  intro h
  rcases h with ⟨C⟩
  exact obstructionBaseSystem_no_semanticProjectionKernel ⟨C.kernel⟩

/-- The obstructed raw faithful emitter is still a genuine computation-to-record
crossing witness; the lack of completion is not because the emitter is
degenerate. -/
theorem obstructionFaithfulRecordEmitter_realizes_crossing {K : Nat} (hK : 1 ≤ K) :
    (obstructionFaithfulRecordEmitter.toRecordEmissionWitness).RealizesComputationToRecordCrossing K := by
  exact obstructionFaithfulRecordEmitter.realizesComputationToRecordCrossing_of_one_le hK

/-- The same failure propagates to the raw stage-indexed emitter. -/
theorem obstructionStageIndexedConservationEmitter_no_completion :
    ¬ Nonempty
      (FaithfulEmitterSemanticKernelCompletion
        obstructionBaseSystem obstructionSeedX obstructionSeedY
        obstructionStageIndexedConservationEmitter.toFaithfulRecordEmitter) := by
  intro h
  rcases h with ⟨C⟩
  exact obstructionBaseSystem_no_semanticProjectionKernel ⟨C.kernel⟩

/-- The obstructed raw stage-indexed emitter is likewise a genuine crossing
witness while still admitting no semantic-kernel completion. -/
theorem obstructionStageIndexedConservationEmitter_realizes_crossing {K : Nat} (hK : 1 ≤ K) :
    (obstructionStageIndexedConservationEmitter.toRecordEmissionWitness).RealizesComputationToRecordCrossing K := by
  exact obstructionStageIndexedConservationEmitter.realizesComputationToRecordCrossing_of_one_le hK

/-- So the naive arbitrary-carrier claim "raw faithful emitter implies
semantic-kernel completion" is formally false. -/
theorem exists_rawFaithfulEmitter_without_semanticKernelCompletion :
    ∃ (Sys : BaseDuplicatingSystem) (b s : Sys.T)
      (E : BaseDuplicatingSystem.FaithfulRecordEmitter Sys b s),
        ¬ Nonempty (FaithfulEmitterSemanticKernelCompletion Sys b s E) := by
  refine ⟨obstructionBaseSystem, obstructionSeedX, obstructionSeedY,
    obstructionFaithfulRecordEmitter, ?_⟩
  exact obstructionFaithfulRecordEmitter_no_completion

/-- Likewise for the raw stage-indexed emitter interface. -/
theorem exists_stageIndexedEmitter_without_semanticKernelCompletion :
    ∃ (Sys : BaseDuplicatingSystem) (b s : Sys.T)
      (E : BaseDuplicatingSystem.StageIndexedConservationEmitter Sys b s),
        ¬ Nonempty
          (FaithfulEmitterSemanticKernelCompletion Sys b s E.toFaithfulRecordEmitter) := by
  refine ⟨obstructionBaseSystem, obstructionSeedX, obstructionSeedY,
    obstructionStageIndexedConservationEmitter, ?_⟩
  exact obstructionStageIndexedConservationEmitter_no_completion

/-- The weaker free faithful-emitter transaction also carries the full
computation-to-confession bridge. -/
theorem free_rankKernel_faithful_emitter_transaction_realizes_bridge {K : Nat}
    (hK : 1 ≤ K) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter.RealizesComputationToConfessionBridge
      (freeRankKernelFaithfulEmitterTransaction.toProjectiveRecordEmitter) K := by
  exact freeRankKernelFaithfulEmitterTransaction.realizesComputationToConfessionBridge_of_one_le hK

/-- The weaker free stage-indexed-emitter transaction inherits the same bridge
through the faithful-emitter + rank-level-kernel route. -/
theorem free_rankKernel_stageIndexed_emitter_transaction_realizes_bridge {K : Nat}
    (hK : 1 ≤ K) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter.RealizesComputationToConfessionBridge
      (freeRankKernelStageIndexedEmitterTransaction.toProjectiveRecordEmitter) K := by
  exact freeRankKernelStageIndexedEmitterTransaction.realizesComputationToConfessionBridge_of_one_le hK

/-- The semantic-kernel faithful-emitter route also carries the full
computation-to-confession bridge. -/
theorem free_semanticKernel_faithful_emitter_transaction_realizes_bridge {K : Nat}
    (hK : 1 ≤ K) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter.RealizesComputationToConfessionBridge
      (freeSemanticKernelFaithfulEmitterTransaction.toProjectiveRecordEmitter) K := by
  exact
    freeSemanticKernelFaithfulEmitterTransaction.realizesComputationToConfessionBridge_of_one_le
      hK

/-- The semantic-kernel stage-indexed-emitter route inherits the same bridge. -/
theorem free_semanticKernel_stageIndexed_emitter_transaction_realizes_bridge {K : Nat}
    (hK : 1 ≤ K) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter.RealizesComputationToConfessionBridge
      (freeSemanticKernelStageIndexedEmitterTransaction.toProjectiveRecordEmitter) K := by
  exact
    freeSemanticKernelStageIndexedEmitterTransaction.realizesComputationToConfessionBridge_of_one_le
      hK

/-- The semantic-generator-preserving transaction layer also carries the full
computation-to-confession bridge on the free primitive duplicator. -/
theorem free_semanticGeneratorPreserving_emitter_transaction_realizes_bridge {K : Nat}
    (hK : 1 ≤ K) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter.RealizesComputationToConfessionBridge
      ((let T := freeSemanticGeneratorPreservingEmitterTransaction.toLicensedSemanticKernelEmitterTransaction
        T.toProjectiveRecordEmitter)) K := by
  let T := freeSemanticGeneratorPreservingEmitterTransaction.toLicensedSemanticKernelEmitterTransaction
  simpa [T] using T.realizesComputationToConfessionBridge_of_one_le hK

/-- The weaker semantic-conservation transaction layer also carries the full
bridge on the free primitive duplicator. -/
theorem free_semanticConservation_emitter_transaction_realizes_bridge {K : Nat}
    (hK : 1 ≤ K) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter.RealizesComputationToConfessionBridge
      ((let T := freeSemanticConservationEmitterTransaction.toLicensedSemanticKernelEmitterTransaction
        T.toProjectiveRecordEmitter)) K := by
  let T := freeSemanticConservationEmitterTransaction.toLicensedSemanticKernelEmitterTransaction
  simpa [T] using T.realizesComputationToConfessionBridge_of_one_le hK

/-- The raw stage-indexed semantic-extension layer likewise carries the full
bridge on the free primitive duplicator. -/
theorem free_stageIndexed_semanticExtension_transaction_realizes_bridge {K : Nat}
    (hK : 1 ≤ K) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter.RealizesComputationToConfessionBridge
      ((let T := freeStageIndexedSemanticExtensionTransaction.toLicensedSemanticConservationEmitterTransaction
        T.toLicensedSemanticKernelEmitterTransaction.toProjectiveRecordEmitter)) K := by
  let T := freeStageIndexedSemanticExtensionTransaction.toLicensedSemanticConservationEmitterTransaction
  simpa [T] using T.realizesComputationToConfessionBridge_of_one_le hK

/-- The raw stage-indexed + semantic-kernel route also carries the full bridge. -/
theorem free_stageIndexed_semanticKernel_transaction_realizes_bridge {K : Nat}
    (hK : 1 ≤ K) :
    BaseDuplicatingSystem.ProjectiveRecordEmitter.RealizesComputationToConfessionBridge
      (freeStageIndexedSemanticKernelTransaction.toProjectiveRecordEmitter) K := by
  exact
    freeStageIndexedSemanticKernelTransaction.realizesComputationToConfessionBridge_of_one_le
      hK

/-- Even before any ambient kernel is supplied, the raw stage-indexed free
emitter is already canonically static on its canonical shadow. -/
theorem free_stageIndexed_shadow_transaction_static :
    IsCanonicalShadowStaticStageIndexedFamily (fun _ => freeStageIndexedShadowTransaction) := by
  apply stageIndexed_emitter_transaction_shadow_static_of_licenseInvariant
  intro i
  rfl

end StepDuplicatingSchema
end OperatorKO7.StepDuplicating
