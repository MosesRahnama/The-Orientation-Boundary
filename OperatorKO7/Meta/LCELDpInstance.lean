import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.ComputationalLayerCrossing
import OperatorKO7.Meta.ProjectionTransactionDynamics

/-!
# Finite DP/emitter-side LCEL fixture

This module combines a concrete projection-certification theorem with a finite two-sentence LCEL
fixture. The base profile uses a constant `True` predicate, the reference-model predicate is
constant `True`, and several obstruction, annotation, and reimport maps are equality or identity
maps. The resulting support theorems certify the fields of the constructed records. They do not
supply an external LCEL interpretation or an unrestricted semantic correspondence.
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

/-- Two tags used as the sentence carrier of the finite fixture. -/
inductive DpEmitterSentenceSemantic
  | baseSystem
  | licensedProjection
  deriving DecidableEq, Repr

/-- Projection transactions over the free primitive-duplicator schema. -/
abbrev DpEmitterProjectionFramework :=
  ProjectionTransaction freeBaseSystem.toStepDuplicatingSchema

/-- A transaction is certified when its boundary is the designated forgetting witness, its license
field holds, and the fixed free emitter realizes its bridge at depth one. -/
def projectionCertified (T : DpEmitterProjectionFramework) : Prop :=
  T.boundary = freeProjectiveRecordEmitter.toForgettingWitness
    ∧ T.license
    ∧ freeProjectiveRecordEmitter.RealizesComputationToConfessionBridge 1

/-- The designated free projection transaction satisfies `projectionCertified`. -/
theorem freeProjectionTransaction_certified :
    projectionCertified freeProjectionTransaction := by
  refine ⟨rfl, trivial, ?_⟩
  exact freeProjectiveRecordEmitter_realizes_bridge (K := 1) (by decide)

/-- Base-profile record whose proof predicate is `True` for both sentence tags. -/
def dpEmitterFormalBaseTheory : FormalHistoricalBaseTheory where
  label := "free primitive duplicator base system"
  Sentence := DpEmitterSentenceSemantic
  provesBaseSystem _ := True
  witness := .baseSystem
  witness_provesBaseSystem := trivial

/-- Obstruction-profile record on the two sentence tags. Both predicates ignore their tag: the
self-obstruction field is the fixed depth-one emitter proposition and the blocking field is the
imported absence of a direct whole witness. The designated tag is `licensedProjection`. -/
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

/-- Framework-profile record using `projectionCertified` and the designated free transaction. -/
def dpEmitterFormalFramework : FormalHistoricalFramework where
  label := "licensed projective-emitter transaction on the free primitive duplicator"
  Framework := DpEmitterProjectionFramework
  resolves := projectionCertified
  availableWitness := freeProjectionTransaction
  resolver := freeProjectionTransaction
  resolver_resolves := freeProjectionTransaction_certified

/-- Reimport-profile record on the two sentence tags. Its certification predicate ignores the
admission value and repeats certification of the designated free transaction. -/
def dpEmitterFormalReimport : FormalHistoricalReimport where
  label := "projective-emitter certified forgetting reimport"
  Admission := DpEmitterSentenceSemantic
  certified _ := projectionCertified freeProjectionTransaction
  witness := .licensedProjection
  witness_certified := freeProjectionTransaction_certified

/-- Sentence semantics in which `baseSystem` is provable, `licensedProjection` is not, and both tags
are declared true in the reference model. -/
def dpEmitterBaseTheoryContent : FormalBaseTheorySemantics where
  Sentence := DpEmitterSentenceSemantic
  proves
    | .baseSystem => True
    | .licensedProjection => False
  trueInReferenceModel _ := True
  baseSentence := .baseSystem
  baseSentence_proves := trivial

/-- Obstruction-content record whose relation is sentence equality and whose `blockedBy` map is the
identity. The self-reference proposition is independent of the witness tag; the designated witness
is `licensedProjection`. -/
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

/-- Reflection-content record in which reflection means that a transaction is certified and the
sentence equals `licensedProjection`. -/
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

/-- Reimport-content record whose admission carrier is the sentence type and whose certification
relation is equality. -/
def dpEmitterReimportContent :
    FormalReimportSemantics dpEmitterBaseTheoryContent where
  Admission := DpEmitterSentenceSemantic
  certifies a s := a = s
  importedSentence := .licensedProjection
  witness := .licensedProjection
  witness_certifies_imported := rfl
  imported_true := by
    simp [dpEmitterBaseTheoryContent]

/-- Coherence record for the three fixture layers. Its two sentence identifications and reimport
certification field reduce to reflexive equalities; reflection coverage uses the designated
transaction's certification theorem. -/
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

/-- Package the finite profiles, content records, coherence record, and reflection-family tag. -/
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

/-- Project the six-step shape, reflection-family tag, and stagewise-equivalence fields supplied by
the constructed comparison object. -/
theorem dpEmitterFormalExternalClassicalComparison_supported :
    RealizesSixStepShape dpEmitterFormalExternalClassicalComparisonObject.profile.shape
      ∧ dpEmitterFormalExternalClassicalComparisonObject.profile.family =
          AscentFamily.reflection
      ∧ StagewiseEquivalent
          dpEmitterFormalExternalClassicalComparisonObject.profile.shape
          dpAsClassicalAscentProfile.shape := by
  exact dpEmitterFormalExternalClassicalComparisonObject.supported

/-- Project the seven named support predicates generated from the constructed content records. -/
theorem dpEmitterFormalExternalClassicalComparison_semanticSupported :
    dpEmitterFormalExternalClassicalComparisonObject.baseTheoryContent.hasInternalProofLayer
      ∧ dpEmitterFormalExternalClassicalComparisonObject.obstructionContent.hasSemanticObstruction
      ∧ dpEmitterFormalExternalClassicalComparisonObject.reflectionContent.hasBlockedSemanticSentence
      ∧ dpEmitterFormalExternalClassicalComparisonObject.reflectionContent.hasReflectionOperator
      ∧ dpEmitterFormalExternalClassicalComparisonObject.reflectionContent.resolvesBlockedSemantically
      ∧ dpEmitterFormalExternalClassicalComparisonObject.reflectionContent.hasLicensedAdmission
      ∧ dpEmitterFormalExternalClassicalComparisonObject.reimportContent.hasSemanticReimport := by
  exact dpEmitterFormalExternalClassicalComparisonObject.semanticSupported

/-- Project the two transfer predicates generated by `dpEmitterSemanticCoherence`. -/
theorem dpEmitterFormalExternalClassicalComparison_transferSupported :
    dpEmitterFormalExternalClassicalComparisonObject.semanticCoherence.obstructionTransfersToReflection
      ∧ dpEmitterFormalExternalClassicalComparisonObject.semanticCoherence.reflectionTransfersToReimport := by
  exact dpEmitterFormalExternalClassicalComparisonObject.semanticTransferSupported

/-- Boundary-slot object using the obstruction witness type, identity blocked-sentence map, and
designated `licensedProjection` witness. -/
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

/-- Annotation-slot object with the sentence type as its annotation carrier and identity maps for
both annotation and decoding. -/
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

/-- Default external-license object derived from the constructed comparison object. -/
def dpEmitterLCELExternalLicenseObject :
    LCELExternalLicenseObject
      dpEmitterFormalExternalClassicalComparisonObject.baseTheoryContent
      dpEmitterFormalExternalClassicalComparisonObject.reflectionContent :=
  defaultExternalLicenseObject dpEmitterFormalExternalClassicalComparisonObject

/-- Default reimport-class object derived from the constructed comparison object. -/
def dpEmitterLCELReimportClassObject :
    LCELReimportClassObject
      dpEmitterFormalExternalClassicalComparisonObject.baseTheoryContent
      dpEmitterFormalExternalClassicalComparisonObject.reimportContent :=
  defaultReimportClassObject dpEmitterFormalExternalClassicalComparisonObject

/-- Assemble the boundary, license, reimport, and annotation objects into a `FormalLCELInstance`. -/
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

/-- The constructed slot profile satisfies `RealizesLCELSchema` via the comparison object's support
theorem. This is a theorem about the finite fixture. -/
theorem dpEmitterLCELInstance_realizesSchema :
    RealizesLCELSchema dpEmitterLCELInstance.toSlotProfile := by
  exact
    dpEmitterLCELInstance.realizesLCELSchema_of_supported
      dpEmitterFormalExternalClassicalComparison_supported

/-- Base-layer support projected from the comparison object's `hasInternalProofLayer` field. -/
theorem dpEmitter_semanticBaseLayerSupport :
    SemanticBaseLayerSupport dpEmitterLCELInstance := by
  rcases dpEmitterFormalExternalClassicalComparison_semanticSupported with
    ⟨hBase, _, _, _, _, _, _⟩
  simpa [SemanticBaseLayerSupport, dpEmitterLCELInstance] using hBase

/-- License-transfer support projected from the first coherence transfer predicate. -/
theorem dpEmitter_semanticLicenseTransferSupport :
    SemanticLicenseTransferSupport dpEmitterLCELInstance := by
  rcases dpEmitterFormalExternalClassicalComparison_transferSupported with
    ⟨hTransfer, _⟩
  simpa [SemanticLicenseTransferSupport, dpEmitterLCELInstance] using hTransfer

/-- Reimport-transfer support projected from the second coherence transfer predicate. -/
theorem dpEmitter_semanticReimportTransferSupport :
    SemanticReimportTransferSupport dpEmitterLCELInstance := by
  rcases dpEmitterFormalExternalClassicalComparison_transferSupported with
    ⟨_, hTransfer⟩
  simpa [SemanticReimportTransferSupport, dpEmitterLCELInstance] using hTransfer

/-- Construct a `BaseReversibilitySupport` record from the preceding base-layer predicate. -/
def dpEmitterBaseReversibilitySupport :
    BaseReversibilitySupport dpEmitterLCELInstance :=
  baseReversibilitySupport_of_semanticBase
    dpEmitter_semanticBaseLayerSupport

/-- Construct a `LicenseIrreversibilitySupport` record from the license-transfer predicate. -/
def dpEmitterLicenseIrreversibilitySupport :
    LicenseIrreversibilitySupport dpEmitterLCELInstance :=
  licenseIrreversibilitySupport_of_semanticTransfer
    dpEmitter_semanticLicenseTransferSupport

/-- Construct a `ReimportReversibilitySupport` record from the reimport-transfer predicate. -/
def dpEmitterReimportReversibilitySupport :
    ReimportReversibilitySupport dpEmitterLCELInstance :=
  reimportReversibilitySupport_of_semanticTransfer
    dpEmitter_semanticReimportTransferSupport

/-- Construct a `BoundaryFactorizationSupport` record from the reimport and license support records. -/
def dpEmitterBoundaryFactorizationSupport :
    BoundaryFactorizationSupport dpEmitterLCELInstance :=
  boundaryFactorizationSupport_of_supports
    dpEmitterReimportReversibilitySupport
    dpEmitterLicenseIrreversibilitySupport

/-- Construct an `LCELReversibilityAsymmetry` record from the three support predicates. -/
def dpEmitterLCELReversibilityAsymmetry :
    LCELReversibilityAsymmetry dpEmitterLCELInstance :=
  lcelReversibilityAsymmetry_of_semanticSupports
    dpEmitter_semanticBaseLayerSupport
    dpEmitter_semanticLicenseTransferSupport
    dpEmitter_semanticReimportTransferSupport

/-- Construct an `LCELBoundaryFactorization` record from the two transfer predicates. -/
def dpEmitterLCELBoundaryFactorization :
    LCELBoundaryFactorization dpEmitterLCELInstance :=
  lcelBoundaryFactorization_of_semanticSupports
    dpEmitter_semanticReimportTransferSupport
    dpEmitter_semanticLicenseTransferSupport

/-- Construct the same asymmetry-record type from the three intermediate support records. -/
def dpEmitterLCELReversibilityAsymmetryFromSupport :
    LCELReversibilityAsymmetry dpEmitterLCELInstance :=
  lcelReversibilityAsymmetry_of_strongerSupports
    dpEmitterBaseReversibilitySupport
    dpEmitterLicenseIrreversibilitySupport
    dpEmitterReimportReversibilitySupport

/-- Construct the factorization-record type from `dpEmitterBoundaryFactorizationSupport`. -/
def dpEmitterLCELBoundaryFactorizationFromSupport :
    LCELBoundaryFactorization dpEmitterLCELInstance :=
  lcelBoundaryFactorization_of_strongerSupport
    dpEmitterBoundaryFactorizationSupport

end OperatorKO7.LCELDpInstance
