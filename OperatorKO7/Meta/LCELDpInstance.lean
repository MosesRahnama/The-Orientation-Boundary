import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.ComputationalLayerCrossing
import OperatorKO7.Meta.ProjectionTransactionDynamics

/-!
# Native DP/Emitter-Side LCEL Instance

This module builds a native non-Godel LCEL instance directly from the free
primitive-duplicator emitter / projection-transaction stack, rather than routing
through the benchmark-transport comparison object.

The goal is still artifact-honest. We do not claim the unrestricted universal
LCEL theorem stack here. We package the currently mechanized DP/emitter-side
bridge as a `FormalExternalClassicalComparisonObject`, then lift it into a
`FormalLCELInstance` and expose the resulting semantic-support surface.
-/

namespace OperatorKO7.LCELDpInstance

open OperatorKO7
open OperatorKO7.WitnessOrder
open OperatorKO7.ProofTheoreticRegister
open OperatorKO7.ClassicalAscentProfile
open OperatorKO7.ReflectionSchema
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.StepDuplicating.StepDuplicatingSchema.BaseDuplicatingSystem
open OperatorKO7.MetaOperationalIncompleteness
open OperatorKO7.LCELSchema
open OperatorKO7.LCELTypedSigmaGamma
open OperatorKO7.LCELReversibility

/-- Minimal sentence layer for the native DP/emitter-side formal LCEL instance. -/
inductive DpEmitterSentenceSemantic
  | baseSystem
  | licensedProjection
  deriving DecidableEq, Repr

/-- The projection-transaction object acts as the native stronger-framework /
reimport carrier on the free primitive duplicator. -/
abbrev DpEmitterProjectionFramework :=
  ProjectionTransaction freeBaseSystem.toStepDuplicatingSchema

/-- Native certification predicate for the DP/emitter-side projection
transaction: it uses the same forgetting witness as the concrete projective
emitter, carries the external license, and is backed by the concrete
computation-to-confession bridge at the first nontrivial depth. -/
def projectionCertified (T : DpEmitterProjectionFramework) : Prop :=
  T.boundary = freeProjectiveRecordEmitter.toForgettingWitness
    ∧ T.license
    ∧ freeProjectiveRecordEmitter.RealizesComputationToConfessionBridge 1

/-- The concrete free projection transaction satisfies the native certification
predicate. -/
theorem freeProjectionTransaction_certified :
    projectionCertified freeProjectionTransaction := by
  refine ⟨rfl, trivial, ?_⟩
  exact freeProjectiveRecordEmitter_realizes_bridge (K := 1) (by decide)

/-- Native base-theory profile on the free primitive duplicator side. -/
def dpEmitterFormalBaseTheory : FormalHistoricalBaseTheory where
  label := "free primitive duplicator base system"
  Sentence := DpEmitterSentenceSemantic
  provesBaseSystem _ := True
  witness := .baseSystem
  witness_provesBaseSystem := trivial

/-- Native obstruction profile: hidden progress exists, but the direct whole-term
witness layer remains blocked. The witness carrier is now the full
native-side semantic sentence space, so that the downstream boundary
witness space is non-singleton and the direct benchmark↔DP boundary
correspondence can be genuinely non-constant. -/
def dpEmitterFormalObstruction : FormalHistoricalObstruction where
  label := "hidden progress requires emitted record / no direct whole witness"
  Witness := DpEmitterSentenceSemantic
  isSelfObstruction _ :=
    freeFaithfulRecordEmitter.toRecordEmissionWitness.RealizesComputationToRecordCrossing 1
  blocksBase _ := ¬ HasWitness ko7Tower WLevel.directWhole
  witness := .licensedProjection
  witness_isSelfObstruction := by
    exact freeFaithfulRecordEmitter_realizes_crossing (K := 1) (by decide)
  witness_blocksBase := ko7_no_directWhole_witness

/-- Native stronger-framework profile: a licensed projection transaction on the
free primitive duplicator. -/
def dpEmitterFormalFramework : FormalHistoricalFramework where
  label := "licensed projective-emitter transaction on the free primitive duplicator"
  Framework := DpEmitterProjectionFramework
  resolves := projectionCertified
  availableWitness := freeProjectionTransaction
  resolver := freeProjectionTransaction
  resolver_resolves := freeProjectionTransaction_certified

/-- Native reimport profile: the designated licensed-projection sentence
is the reimport carrier. The admission carrier is the full semantic
sentence space, matching the obstruction content so that the annotation
functor's `annotate` map can be the identity on sentences. The
projection-certified evidence is preserved on the designated witness
via a constant-on-input certification predicate. -/
def dpEmitterFormalReimport : FormalHistoricalReimport where
  label := "projective-emitter certified forgetting reimport"
  Admission := DpEmitterSentenceSemantic
  certified _ := projectionCertified freeProjectionTransaction
  witness := .licensedProjection
  witness_certified := freeProjectionTransaction_certified

/-- Deeper sentence semantics for the native DP/emitter-side base theory. -/
def dpEmitterBaseTheoryContent : FormalBaseTheorySemantics where
  Sentence := DpEmitterSentenceSemantic
  proves
    | .baseSystem => True
    | .licensedProjection => False
  trueInReferenceModel _ := True
  baseSentence := .baseSystem
  baseSentence_proves := trivial

/-- Deeper semantic obstruction on the native DP/emitter side, with
witness carrier upgraded to the typed sentence space. The obstruction
relation is witness-equals-sentence on the typed sentence space, and
`blockedBy` is the identity on sentences. Only the designated witness
(`.licensedProjection`) carries the theorem load; non-designated
witnesses are structurally present without faking extra mathematics. -/
def dpEmitterObstructionContent :
    FormalObstructionSemantics dpEmitterBaseTheoryContent where
  Witness := DpEmitterSentenceSemantic
  obstructs w s := s = w
  selfReferential _ :=
    freeFaithfulRecordEmitter.toRecordEmissionWitness.RealizesComputationToRecordCrossing 1
  blockedBy := id
  witness := .licensedProjection
  witness_selfReferential := by
    exact freeFaithfulRecordEmitter_realizes_crossing (K := 1) (by decide)
  witness_obstructs_blocked := rfl
  blocked_not_provable := by
    simp [dpEmitterBaseTheoryContent]
  blocked_true := by
    simp [dpEmitterBaseTheoryContent]

/-- Deeper semantic reflection / framework content on the native DP/emitter
side. The stronger framework is represented by the certified projection
transaction itself. -/
def dpEmitterReflectionContent :
    FormalReflectionOperatorSemantics dpEmitterBaseTheoryContent where
  Framework := DpEmitterProjectionFramework
  extendsBase := projectionCertified
  reflects T s := projectionCertified T ∧ s = .licensedProjection
  licensedAdmission s := s = .licensedProjection
  blockedSentence := .licensedProjection
  blocked_not_provable := by
    simp [dpEmitterBaseTheoryContent]
  blocked_true := by
    simp [dpEmitterBaseTheoryContent]
  strongerFramework := freeProjectionTransaction
  stronger_extendsBase := freeProjectionTransaction_certified
  stronger_reflects_blocked := by
    exact ⟨freeProjectionTransaction_certified, rfl⟩
  blocked_licensedAdmission := rfl

/-- Deeper semantic reimport content on the native DP/emitter side,
with admission carrier upgraded to the typed sentence space. The
certification relation is `a = s` on sentences; the projection-
certified evidence is retained on the reflection-content layer (which
still uses `DpEmitterProjectionFramework` as its framework type). -/
def dpEmitterReimportContent :
    FormalReimportSemantics dpEmitterBaseTheoryContent where
  Admission := DpEmitterSentenceSemantic
  certifies a s := a = s
  importedSentence := .licensedProjection
  witness := .licensedProjection
  witness_certifies_imported := rfl
  imported_true := by
    simp [dpEmitterBaseTheoryContent]

/-- Coherence data tying the native DP/emitter-side obstruction,
reflection, and reimport layers together. After the admission-carrier
upgrade, `reimport_certifies_reflection_blocked` reduces to
`.licensedProjection = .licensedProjection` and is `rfl`. -/
def dpEmitterSemanticCoherence :
    FormalSemanticCoherence
      dpEmitterObstructionContent
      dpEmitterReflectionContent
      dpEmitterReimportContent where
  obstruction_blocked_eq_reflection_blocked := rfl
  reflection_blocked_eq_reimported := rfl
  reflection_covers_obstruction :=
    ⟨freeProjectionTransaction_certified, rfl⟩
  reimport_certifies_reflection_blocked := rfl

/-- Native DP/emitter-side formal external classical comparison object. -/
def dpEmitterFormalExternalClassicalComparisonObject :
    FormalExternalClassicalComparisonObject where
  baseSemantics := dpEmitterFormalBaseTheory
  obstructionSemantics := dpEmitterFormalObstruction
  frameworkSemantics := dpEmitterFormalFramework
  reimportSemantics := dpEmitterFormalReimport
  baseTheoryContent := dpEmitterBaseTheoryContent
  obstructionContent := dpEmitterObstructionContent
  reflectionContent := dpEmitterReflectionContent
  reimportContent := dpEmitterReimportContent
  semanticCoherence := dpEmitterSemanticCoherence
  family := AscentFamily.reflection
  profile := {
    shape := {
      hasBaseSystem := dpEmitterFormalBaseTheory.hasBaseSystem
      hasSelfObstruction := dpEmitterFormalObstruction.hasSelfObstruction
      blockedInBase := dpEmitterFormalObstruction.blockedInBase
      hasStrongerFramework := dpEmitterFormalFramework.frameworkAvailable
      resolvedInFramework := dpEmitterFormalFramework.resolvesInFramework
      licensedReimport := dpEmitterFormalReimport.licensedReimport
    }
    family := AscentFamily.reflection
  }
  profileShape := rfl
  profileFamily := rfl
  compatible := by
    rcases structural_identity with
      ⟨hBase, hSelf, hBlocked, hStronger, hResolved, hLicensed⟩
    refine ⟨?_, rfl⟩
    intro s
    cases s with
    | baseSystem =>
        exact ⟨fun _ => hBase,
          fun _ => dpEmitterFormalBaseTheory.realizesBaseSystem⟩
    | selfObstruction =>
        exact ⟨fun _ => hSelf,
          fun _ => dpEmitterFormalObstruction.realizesSelfObstruction⟩
    | blockedInBase =>
        exact ⟨fun _ => hBlocked,
          fun _ => dpEmitterFormalObstruction.realizesBlockedInBase⟩
    | strongerFramework =>
        exact ⟨fun _ => hStronger,
          fun _ => dpEmitterFormalFramework.realizesAvailability⟩
    | resolvedInFramework =>
        exact ⟨fun _ => hResolved,
          fun _ => dpEmitterFormalFramework.realizesResolution⟩
    | licensedReimport =>
        exact ⟨fun _ => hLicensed,
          fun _ => dpEmitterFormalReimport.realizesLicensedReimport⟩

/-- The native DP/emitter-side formal comparison object is theorem-backed at the
profile level. -/
theorem dpEmitterFormalExternalClassicalComparison_supported :
    RealizesSixStepShape dpEmitterFormalExternalClassicalComparisonObject.profile.shape
      ∧ dpEmitterFormalExternalClassicalComparisonObject.profile.family =
          AscentFamily.reflection
      ∧ StagewiseEquivalent
          dpEmitterFormalExternalClassicalComparisonObject.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact dpEmitterFormalExternalClassicalComparisonObject.supported

/-- The native DP/emitter-side formal comparison object has theorem-backed
semantic content. -/
theorem dpEmitterFormalExternalClassicalComparison_semanticSupported :
    dpEmitterFormalExternalClassicalComparisonObject.baseTheoryContent.hasInternalProofLayer
      ∧ dpEmitterFormalExternalClassicalComparisonObject.obstructionContent.hasSemanticObstruction
      ∧ dpEmitterFormalExternalClassicalComparisonObject.reflectionContent.hasBlockedSemanticSentence
      ∧ dpEmitterFormalExternalClassicalComparisonObject.reflectionContent.hasReflectionOperator
      ∧ dpEmitterFormalExternalClassicalComparisonObject.reflectionContent.resolvesBlockedSemantically
      ∧ dpEmitterFormalExternalClassicalComparisonObject.reflectionContent.hasLicensedAdmission
      ∧ dpEmitterFormalExternalClassicalComparisonObject.reimportContent.hasSemanticReimport := by
  exact dpEmitterFormalExternalClassicalComparisonObject.semanticSupported

/-- The native DP/emitter-side formal comparison object also has theorem-backed
transfer from obstruction to reflection and from reflection to reimport. -/
theorem dpEmitterFormalExternalClassicalComparison_transferSupported :
    dpEmitterFormalExternalClassicalComparisonObject.semanticCoherence.obstructionTransfersToReflection
      ∧ dpEmitterFormalExternalClassicalComparisonObject.semanticCoherence.reflectionTransfersToReimport := by
  exact dpEmitterFormalExternalClassicalComparisonObject.semanticTransferSupported

/-- Native DP/emitter-side boundary object for the LCEL boundary slot. -/
def dpEmitterLCELBoundaryObject :
    LCELBoundaryObject dpEmitterFormalExternalClassicalComparisonObject.baseTheoryContent where
  BoundaryWitness :=
    dpEmitterFormalExternalClassicalComparisonObject.obstructionContent.Witness
  boundarySentence :=
    dpEmitterFormalExternalClassicalComparisonObject.obstructionContent.blockedBy
  designated := dpEmitterFormalExternalClassicalComparisonObject.obstructionContent.witness
  designated_not_provable := by
    simpa using
      dpEmitterFormalExternalClassicalComparisonObject.obstructionContent.blocked_not_provable
  designated_true := by
    simpa using
      dpEmitterFormalExternalClassicalComparisonObject.obstructionContent.blocked_true

/-- Native DP/emitter-side annotation functor for the LCEL annotation
slot. After the reimport-content admission-carrier upgrade, the
admission space and the annotation space both coincide with the typed
sentence space, so `annotate` is the identity on sentences rather than
a constant landing on the designated imported sentence. -/
def dpEmitterLCELAnnotationFunctor :
    LCELAnnotationFunctor
      dpEmitterFormalExternalClassicalComparisonObject.baseTheoryContent
      dpEmitterFormalExternalClassicalComparisonObject.reimportContent where
  Annotation :=
    dpEmitterFormalExternalClassicalComparisonObject.baseTheoryContent.Sentence
  annotate := id
  decode := id
  witness_decodes_to_imported := rfl
  witness_certifies_decoded := rfl
  witness_decoded_true := by
    simpa using
      dpEmitterFormalExternalClassicalComparisonObject.reimportContent.imported_true

/-- Native DP/emitter-side typed external-license object for the LCEL slot
`Σ`. -/
def dpEmitterLCELExternalLicenseObject :
    LCELExternalLicenseObject
      dpEmitterFormalExternalClassicalComparisonObject.baseTheoryContent
      dpEmitterFormalExternalClassicalComparisonObject.reflectionContent :=
  defaultExternalLicenseObject dpEmitterFormalExternalClassicalComparisonObject

/-- Native DP/emitter-side typed reimport-class object for the LCEL slot
`Γ'`. -/
def dpEmitterLCELReimportClassObject :
    LCELReimportClassObject
      dpEmitterFormalExternalClassicalComparisonObject.baseTheoryContent
      dpEmitterFormalExternalClassicalComparisonObject.reimportContent :=
  defaultReimportClassObject dpEmitterFormalExternalClassicalComparisonObject

/-- Native DP/emitter-side LCEL instance. -/
def dpEmitterLCELInstance : FormalLCELInstance where
  comparison := dpEmitterFormalExternalClassicalComparisonObject
  boundaryObject := dpEmitterLCELBoundaryObject
  boundaryMatchesProfile := by
    constructor
    · intro _
      have hObs :
          dpEmitterFormalExternalClassicalComparisonObject.obstructionSemantics.hasSelfObstruction := by
        exact
          dpEmitterFormalExternalClassicalComparisonObject.obstructionSemantics.realizesSelfObstruction
      have hEq :
          dpEmitterFormalExternalClassicalComparisonObject.profile.shape.hasSelfObstruction =
            dpEmitterFormalExternalClassicalComparisonObject.obstructionSemantics.hasSelfObstruction := by
        rw [dpEmitterFormalExternalClassicalComparisonObject.profileShape]
      exact hEq.symm ▸ hObs
    · intro _
      exact dpEmitterLCELBoundaryObject.designated_realizes
  externalLicenseObject := dpEmitterLCELExternalLicenseObject
  externalLicenseWitness :=
    dpEmitterFormalExternalClassicalComparisonObject.reflectionContent.hasReflectionOperator
  externalLicenseHolds := by
    rcases dpEmitterFormalExternalClassicalComparison_semanticSupported with
      ⟨_, _, _, hReflect, _, _, _⟩
    exact hReflect
  externalLicenseMatchesWitness := by
    simpa [dpEmitterLCELExternalLicenseObject] using
      defaultExternalLicenseObject_realized_iff_hasReflectionOperator
        dpEmitterFormalExternalClassicalComparisonObject
  reimportClassObject := dpEmitterLCELReimportClassObject
  reimportClassWitness :=
    dpEmitterFormalExternalClassicalComparisonObject.reimportContent.hasSemanticReimport
  reimportClassHolds := by
    rcases dpEmitterFormalExternalClassicalComparison_semanticSupported with
      ⟨_, _, _, _, _, _, hReimport⟩
    exact hReimport
  reimportClassMatchesWitness := by
    simpa [dpEmitterLCELReimportClassObject] using
      defaultReimportClassObject_realized_iff_hasSemanticReimport
        dpEmitterFormalExternalClassicalComparisonObject
  annotationFunctor := dpEmitterLCELAnnotationFunctor
  annotationMatchesProfile := by
    constructor
    · intro _
      have hAnn :
          dpEmitterFormalExternalClassicalComparisonObject.reimportSemantics.licensedReimport := by
        exact
          dpEmitterFormalExternalClassicalComparisonObject.reimportSemantics.realizesLicensedReimport
      have hEq :
          dpEmitterFormalExternalClassicalComparisonObject.profile.shape.licensedReimport =
            dpEmitterFormalExternalClassicalComparisonObject.reimportSemantics.licensedReimport := by
        rw [dpEmitterFormalExternalClassicalComparisonObject.profileShape]
      exact hEq.symm ▸ hAnn
    · intro _
      exact dpEmitterLCELAnnotationFunctor.witness_realizes

/-- The native DP/emitter-side LCEL instance realizes the six-clause LCEL
schema. -/
theorem dpEmitterLCELInstance_realizesSchema :
    RealizesLCELSchema dpEmitterLCELInstance.toSlotProfile := by
  exact
    dpEmitterLCELInstance.realizesLCELSchema_of_supported
      dpEmitterFormalExternalClassicalComparison_supported

/-- The current theorem-backed base-layer support on the native DP/emitter-side
LCEL instance. -/
theorem dpEmitter_semanticBaseLayerSupport :
    SemanticBaseLayerSupport dpEmitterLCELInstance := by
  rcases dpEmitterFormalExternalClassicalComparison_semanticSupported with
    ⟨hBase, _, _, _, _, _, _⟩
  simpa [SemanticBaseLayerSupport, dpEmitterLCELInstance] using hBase

/-- The current theorem-backed obstruction-to-license transfer support on the
native DP/emitter-side LCEL instance. -/
theorem dpEmitter_semanticLicenseTransferSupport :
    SemanticLicenseTransferSupport dpEmitterLCELInstance := by
  rcases dpEmitterFormalExternalClassicalComparison_transferSupported with
    ⟨hTransfer, _⟩
  simpa [SemanticLicenseTransferSupport, dpEmitterLCELInstance] using hTransfer

/-- The current theorem-backed reflection-to-reimport transfer support on the
native DP/emitter-side LCEL instance. -/
theorem dpEmitter_semanticReimportTransferSupport :
    SemanticReimportTransferSupport dpEmitterLCELInstance := by
  rcases dpEmitterFormalExternalClassicalComparison_transferSupported with
    ⟨_, hTransfer⟩
  simpa [SemanticReimportTransferSupport, dpEmitterLCELInstance] using hTransfer

/-- Stronger native DP/emitter-side base support package assembled from the
typed LCEL carrier and the current semantic base-layer theorem. -/
def dpEmitterBaseReversibilitySupport :
    BaseReversibilitySupport dpEmitterLCELInstance :=
  baseReversibilitySupport_of_semanticBase
    dpEmitter_semanticBaseLayerSupport

/-- Stronger native DP/emitter-side license-side support package assembled from
the typed LCEL carrier and the current semantic transfer theorem. -/
def dpEmitterLicenseIrreversibilitySupport :
    LicenseIrreversibilitySupport dpEmitterLCELInstance :=
  licenseIrreversibilitySupport_of_semanticTransfer
    dpEmitter_semanticLicenseTransferSupport

/-- Stronger native DP/emitter-side reimport-side support package assembled
from the typed LCEL carrier and the current semantic transfer theorem. -/
def dpEmitterReimportReversibilitySupport :
    ReimportReversibilitySupport dpEmitterLCELInstance :=
  reimportReversibilitySupport_of_semanticTransfer
    dpEmitter_semanticReimportTransferSupport

/-- Stronger native DP/emitter-side factorization support package assembled
from the stronger visible and sensitive substrate layers. -/
def dpEmitterBoundaryFactorizationSupport :
    BoundaryFactorizationSupport dpEmitterLCELInstance :=
  boundaryFactorizationSupport_of_supports
    dpEmitterReimportReversibilitySupport
    dpEmitterLicenseIrreversibilitySupport

/-- Native DP/emitter-side LCEL reversibility-asymmetry package assembled from
the current semantic-support surface. -/
def dpEmitterLCELReversibilityAsymmetry :
    LCELReversibilityAsymmetry dpEmitterLCELInstance :=
  lcelReversibilityAsymmetry_of_semanticSupports
    dpEmitter_semanticBaseLayerSupport
    dpEmitter_semanticLicenseTransferSupport
    dpEmitter_semanticReimportTransferSupport

/-- Native DP/emitter-side LCEL boundary-factorization package assembled from
the current semantic-support surface. -/
def dpEmitterLCELBoundaryFactorization :
    LCELBoundaryFactorization dpEmitterLCELInstance :=
  lcelBoundaryFactorization_of_semanticSupports
    dpEmitter_semanticReimportTransferSupport
    dpEmitter_semanticLicenseTransferSupport

/-- Stronger native DP/emitter-side LCEL asymmetry package assembled from the
proof-carrying substrate support records. -/
def dpEmitterLCELReversibilityAsymmetryFromSupport :
    LCELReversibilityAsymmetry dpEmitterLCELInstance :=
  lcelReversibilityAsymmetry_of_strongerSupports
    dpEmitterBaseReversibilitySupport
    dpEmitterLicenseIrreversibilitySupport
    dpEmitterReimportReversibilitySupport

/-- Stronger native DP/emitter-side LCEL boundary-factorization package
assembled from the proof-carrying substrate support record. -/
def dpEmitterLCELBoundaryFactorizationFromSupport :
    LCELBoundaryFactorization dpEmitterLCELInstance :=
  lcelBoundaryFactorization_of_strongerSupport
    dpEmitterBoundaryFactorizationSupport

end OperatorKO7.LCELDpInstance
