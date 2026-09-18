import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity

/-!
# Typed LCEL slot maps and weak preservation records

This module defines maps between selected carrier types and propositions of two
`FormalLCELInstance`s. The basic records require only designated-witness equalities or forward and
backward functions between propositions. The strengthened records add one-way preservation fields.
They do not require injectivity, inverse laws, source dependence, reflection, or naturality.

The canonical Godel-to-benchmark and Godel-to-DP maps are constant to target-designated values. Their
preservation proofs use target support fields and may ignore both the source value and source proof.
Consequently, these records establish the stated typed equations and implications, not a faithful
semantic correspondence between the instances.
-/

namespace OperatorKO7.LCELSemanticCorrespondence

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.ReflectionSchema

/-! ## Boundary-object correspondence -/

/-- A map between boundary-witness types that sends the designated source witness to the designated
target witness. No injectivity, inverse, or preservation law for other witnesses is required. -/
structure BoundaryObjectCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  /-- Translation of boundary witnesses from `L₁` to `L₂`. -/
  translate :
    L₁.boundaryObject.BoundaryWitness → L₂.boundaryObject.BoundaryWitness
  /-- The designated witness on `L₁` translates to the designated witness
  on `L₂`. -/
  translate_designated :
    translate L₁.boundaryObject.designated = L₂.boundaryObject.designated

namespace BoundaryObjectCorrespondence

/-- The translated designated witness satisfies the target's two stored boundary facts after
rewriting by `translate_designated`. -/
theorem translate_designated_realizes
    {L₁ L₂ : FormalLCELInstance}
    (C : BoundaryObjectCorrespondence L₁ L₂) :
    ¬ L₂.comparison.baseTheoryContent.proves
        (L₂.boundaryObject.boundarySentence
          (C.translate L₁.boundaryObject.designated))
      ∧ L₂.comparison.baseTheoryContent.trueInReferenceModel
        (L₂.boundaryObject.boundarySentence
          (C.translate L₁.boundaryObject.designated)) := by
  refine ⟨?_, ?_⟩
  · rw [C.translate_designated]
    exact L₂.boundaryObject.designated_not_provable
  · rw [C.translate_designated]
    exact L₂.boundaryObject.designated_true

end BoundaryObjectCorrespondence

/-! ## External-license correspondence -/

/-- Forward and backward functions between two external-license propositions. This data is
equivalent to an `Iff`; no law relates the two functions. -/
structure ExternalLicenseCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  /-- Transport a source external-license witness to a target witness. -/
  forward : L₁.externalLicenseWitness → L₂.externalLicenseWitness
  /-- Transport a target external-license witness to a source witness. -/
  backward : L₂.externalLicenseWitness → L₁.externalLicenseWitness

namespace ExternalLicenseCorrespondence

/-- An external-license correspondence induces a biconditional on the slot
propositions. -/
theorem toIff
    {L₁ L₂ : FormalLCELInstance}
    (C : ExternalLicenseCorrespondence L₁ L₂) :
    L₁.externalLicenseWitness ↔ L₂.externalLicenseWitness :=
  ⟨C.forward, C.backward⟩

end ExternalLicenseCorrespondence

/-! ## Reimport-class correspondence -/

/-- Forward and backward functions between two reimport-class propositions. No inverse law is
required. -/
structure ReimportClassCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  /-- Transport a source reimport-class witness to a target witness. -/
  forward : L₁.reimportClassWitness → L₂.reimportClassWitness
  /-- Transport a target reimport-class witness to a source witness. -/
  backward : L₂.reimportClassWitness → L₁.reimportClassWitness

namespace ReimportClassCorrespondence

/-- A reimport-class correspondence induces a biconditional on the slot
propositions. -/
theorem toIff
    {L₁ L₂ : FormalLCELInstance}
    (C : ReimportClassCorrespondence L₁ L₂) :
    L₁.reimportClassWitness ↔ L₂.reimportClassWitness :=
  ⟨C.forward, C.backward⟩

end ReimportClassCorrespondence

/-! ## Annotation-functor correspondence -/

/-- A map between annotation carriers that agrees with the target annotation on the single
designated source annotation. No law constrains other source annotations. -/
structure AnnotationFunctorCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  /-- Translation of annotations from `L₁` to `L₂`. -/
  translateAnnotation :
    L₁.annotationFunctor.Annotation → L₂.annotationFunctor.Annotation
  /-- The annotation of the designated derivation on `L₁` translates to the
  annotation of the designated derivation on `L₂`. -/
  translate_annotate_witness :
    translateAnnotation
      (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness)
      = L₂.annotationFunctor.annotate L₂.comparison.reimportContent.witness

namespace AnnotationFunctorCorrespondence

/-- At the designated annotation, rewrite by `translate_annotate_witness` and project the target
annotation functor's certification and truth fields. -/
theorem translate_annotate_witness_certified
    {L₁ L₂ : FormalLCELInstance}
    (C : AnnotationFunctorCorrespondence L₁ L₂) :
    L₂.comparison.reimportContent.certifies
        L₂.comparison.reimportContent.witness
        (L₂.annotationFunctor.decode
          (C.translateAnnotation
            (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness)))
      ∧ L₂.comparison.baseTheoryContent.trueInReferenceModel
        (L₂.annotationFunctor.decode
          (C.translateAnnotation
            (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness))) := by
  refine ⟨?_, ?_⟩
  · rw [C.translate_annotate_witness]
    exact L₂.annotationFunctor.witness_certifies_decoded
  · rw [C.translate_annotate_witness]
    exact L₂.annotationFunctor.witness_decoded_true

end AnnotationFunctorCorrespondence

/-! ## Packaged semantic slot correspondence -/

/-- Bundle the four weak slot-map records. -/
structure LCELSemanticSlotCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  boundary : BoundaryObjectCorrespondence L₁ L₂
  externalLicense : ExternalLicenseCorrespondence L₁ L₂
  reimportClass : ReimportClassCorrespondence L₁ L₂
  annotation : AnnotationFunctorCorrespondence L₁ L₂

namespace LCELSemanticSlotCorrespondence

/-- The external-license biconditional induced by the external-license slot
correspondence via its explicit forward / backward transport functions. -/
theorem externalLicense_iff
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELSemanticSlotCorrespondence L₁ L₂) :
    L₁.externalLicenseWitness ↔ L₂.externalLicenseWitness :=
  C.externalLicense.toIff

/-- The reimport-class biconditional induced by the reimport-class slot
correspondence via its explicit forward / backward transport functions. -/
theorem reimportClass_iff
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELSemanticSlotCorrespondence L₁ L₂) :
    L₁.reimportClassWitness ↔ L₂.reimportClassWitness :=
  C.reimportClass.toIff

end LCELSemanticSlotCorrespondence

/-! ## From slot maps to a comparison witness

The boundary and annotation maps are not used by the constructor below. Stagewise profile
equivalence is supplied separately, while the two proposition-map pairs produce the license and
reimport biconditionals.
-/

/-- Build an `LCELComparisonWitness` from supplied stagewise equivalence and the two proposition-map
pairs in `C`. -/
def LCELComparisonWitness.ofSemanticSlotCorrespondence
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELSemanticSlotCorrespondence L₁ L₂)
    (hShape :
      StagewiseEquivalent L₁.comparison.profile.shape L₂.comparison.profile.shape) :
    LCELComparisonWitness L₁ L₂ where
  comparisonStagewise := hShape
  externalLicenseEquivalent := C.externalLicense.toIff
  reimportClassEquivalent := C.reimportClass.toIff

/-! ## Canonical constant-target slot maps

For both fixed pairs, boundary and annotation maps discard the source and return the target's
designated value. License and reimport maps likewise discard their proof arguments and return stored
inhabitants from the destination instance.
-/

/-- Gödel-to-benchmark boundary correspondence: the constant map sending every
source boundary witness to the target's designated witness. -/
def godel_benchmark_boundaryCorrespondence :
    BoundaryObjectCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  translate _ := benchmarkTransportLCELInstance.boundaryObject.designated
  translate_designated := rfl

/-- Gödel-to-benchmark annotation correspondence: the constant map sending
every source annotation to the target's designated-derivation annotation. -/
def godel_benchmark_annotationCorrespondence :
    AnnotationFunctorCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  translateAnnotation _ :=
    benchmarkTransportLCELInstance.annotationFunctor.annotate
      benchmarkTransportLCELInstance.comparison.reimportContent.witness
  translate_annotate_witness := rfl

/-- Gödel-to-benchmark external-license correspondence. -/
def godel_benchmark_externalLicenseCorrespondence :
    ExternalLicenseCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  forward _ := benchmarkTransportLCELInstance.externalLicenseHolds
  backward _ := godel1931LCELInstance.externalLicenseHolds

/-- Gödel-to-benchmark reimport-class correspondence. -/
def godel_benchmark_reimportClassCorrespondence :
    ReimportClassCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  forward _ := benchmarkTransportLCELInstance.reimportClassHolds
  backward _ := godel1931LCELInstance.reimportClassHolds

/-- Package the four constant-target Godel-to-benchmark slot maps. -/
def godel_benchmark_semanticSlotCorrespondence :
    LCELSemanticSlotCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  boundary := godel_benchmark_boundaryCorrespondence
  externalLicense := godel_benchmark_externalLicenseCorrespondence
  reimportClass := godel_benchmark_reimportClassCorrespondence
  annotation := godel_benchmark_annotationCorrespondence

/-- Gödel-to-DP boundary correspondence. -/
def godel_dp_boundaryCorrespondence :
    BoundaryObjectCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  translate _ := dpEmitterLCELInstance.boundaryObject.designated
  translate_designated := rfl

/-- Gödel-to-DP annotation correspondence. -/
def godel_dp_annotationCorrespondence :
    AnnotationFunctorCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  translateAnnotation _ :=
    dpEmitterLCELInstance.annotationFunctor.annotate
      dpEmitterLCELInstance.comparison.reimportContent.witness
  translate_annotate_witness := rfl

/-- Gödel-to-DP external-license correspondence. -/
def godel_dp_externalLicenseCorrespondence :
    ExternalLicenseCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  forward _ := dpEmitterLCELInstance.externalLicenseHolds
  backward _ := godel1931LCELInstance.externalLicenseHolds

/-- Gödel-to-DP reimport-class correspondence. -/
def godel_dp_reimportClassCorrespondence :
    ReimportClassCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  forward _ := dpEmitterLCELInstance.reimportClassHolds
  backward _ := godel1931LCELInstance.reimportClassHolds

/-- Package the four constant-target Godel-to-DP slot maps. -/
def godel_dp_semanticSlotCorrespondence :
    LCELSemanticSlotCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  boundary := godel_dp_boundaryCorrespondence
  externalLicense := godel_dp_externalLicenseCorrespondence
  reimportClass := godel_dp_reimportClassCorrespondence
  annotation := godel_dp_annotationCorrespondence

/-! ## Boundary maps with one-way preservation fields

`StrongBoundaryObjectCorrespondence` adds implications for non-provability and reference-model
truth. The canonical maps remain constant: their proofs ignore the source premises and use the
target designated witness's stored facts. Thus the record does not enforce source-sensitive
preservation.
-/

/-- Extend a boundary map with one-way implications for non-provability and reference-model truth. -/
structure StrongBoundaryObjectCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type
    extends BoundaryObjectCorrespondence L₁ L₂ where
  /-- The translation preserves non-provability of the boundary sentence. -/
  translate_preserves_not_provable :
    ∀ w : L₁.boundaryObject.BoundaryWitness,
      (¬ L₁.comparison.baseTheoryContent.proves
            (L₁.boundaryObject.boundarySentence w))
        → ¬ L₂.comparison.baseTheoryContent.proves
            (L₂.boundaryObject.boundarySentence (translate w))
  /-- The translation preserves truth in the reference model. -/
  translate_preserves_true :
    ∀ w : L₁.boundaryObject.BoundaryWitness,
      L₁.comparison.baseTheoryContent.trueInReferenceModel
          (L₁.boundaryObject.boundarySentence w)
        → L₂.comparison.baseTheoryContent.trueInReferenceModel
            (L₂.boundaryObject.boundarySentence (translate w))

namespace StrongBoundaryObjectCorrespondence

/-- Apply the two stored implications to a source witness carrying both source-side premises. -/
theorem translate_realizes
    {L₁ L₂ : FormalLCELInstance}
    (C : StrongBoundaryObjectCorrespondence L₁ L₂)
    (w : L₁.boundaryObject.BoundaryWitness)
    (hNotProvable :
      ¬ L₁.comparison.baseTheoryContent.proves
          (L₁.boundaryObject.boundarySentence w))
    (hTrue :
      L₁.comparison.baseTheoryContent.trueInReferenceModel
        (L₁.boundaryObject.boundarySentence w)) :
    (¬ L₂.comparison.baseTheoryContent.proves
        (L₂.boundaryObject.boundarySentence (C.translate w)))
      ∧ L₂.comparison.baseTheoryContent.trueInReferenceModel
        (L₂.boundaryObject.boundarySentence (C.translate w)) :=
  ⟨C.translate_preserves_not_provable w hNotProvable,
    C.translate_preserves_true w hTrue⟩

end StrongBoundaryObjectCorrespondence

/-- Constant Godel-to-DP boundary map whose preservation proofs ignore the source witness and
premises and return the DP designated witness's stored facts. -/
def godel_dp_strongBoundaryCorrespondence :
    StrongBoundaryObjectCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  toBoundaryObjectCorrespondence := godel_dp_boundaryCorrespondence
  translate_preserves_not_provable := by
    intro _ _
    exact dpEmitterLCELInstance.boundaryObject.designated_not_provable
  translate_preserves_true := by
    intro _ _
    exact dpEmitterLCELInstance.boundaryObject.designated_true

/-- Constant Godel-to-benchmark boundary map using the benchmark designated witness's stored facts. -/
def godel_benchmark_strongBoundaryCorrespondence :
    StrongBoundaryObjectCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  toBoundaryObjectCorrespondence := godel_benchmark_boundaryCorrespondence
  translate_preserves_not_provable := by
    intro _ _
    exact benchmarkTransportLCELInstance.boundaryObject.designated_not_provable
  translate_preserves_true := by
    intro _ _
    exact benchmarkTransportLCELInstance.boundaryObject.designated_true

/-! ## External-license maps with target-support fields

`StrongExternalLicenseCorrespondence` adds functions from a source license proof to two target
facts. The canonical Godel-to-DP implementation ignores the source proof and returns facts stored by
the target instance.
-/

/-- Extend license proposition maps with target non-provability and reflection functions. -/
structure StrongExternalLicenseCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type
    extends ExternalLicenseCorrespondence L₁ L₂ where
  /-- The forward transport certifies that the target's reflection content
  has a blocked sentence that is not provable in the target base theory. -/
  forward_preserves_blocked_not_provable :
    L₁.externalLicenseWitness →
      ¬ L₂.comparison.baseTheoryContent.proves
          L₂.comparison.reflectionContent.blockedSentence
  /-- The forward transport certifies that the target's reflection content
  has a blocked sentence that the target stronger framework reflects. -/
  forward_preserves_stronger_reflects :
    L₁.externalLicenseWitness →
      L₂.comparison.reflectionContent.reflects
        L₂.comparison.reflectionContent.strongerFramework
        L₂.comparison.reflectionContent.blockedSentence

namespace StrongExternalLicenseCorrespondence

/-- Pair the two target facts returned by a strong external-license record. -/
theorem forward_preserves_licenseExtendsBase
    {L₁ L₂ : FormalLCELInstance}
    (C : StrongExternalLicenseCorrespondence L₁ L₂)
    (h : L₁.externalLicenseWitness) :
    (¬ L₂.comparison.baseTheoryContent.proves
        L₂.comparison.reflectionContent.blockedSentence)
      ∧ L₂.comparison.reflectionContent.reflects
          L₂.comparison.reflectionContent.strongerFramework
          L₂.comparison.reflectionContent.blockedSentence :=
  ⟨C.forward_preserves_blocked_not_provable h,
    C.forward_preserves_stronger_reflects h⟩

end StrongExternalLicenseCorrespondence

/-- Godel-to-DP license record whose added functions ignore the source proof and project target
reflection-content facts. -/
def godel_dp_strongExternalLicenseCorrespondence :
    StrongExternalLicenseCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  toExternalLicenseCorrespondence := godel_dp_externalLicenseCorrespondence
  forward_preserves_blocked_not_provable := by
    intro _
    exact dpEmitterLCELInstance.comparison.reflectionContent.blocked_not_provable
  forward_preserves_stronger_reflects := by
    intro _
    exact dpEmitterLicenseIrreversibilitySupport.strongerFrameworkReflectsBlocked

/-! ## Reimport maps with target-support fields

The added functions return certification and truth facts about the target's designated imported
sentence. They need not depend on the source proof.
-/

/-- Strengthened reimport-class correspondence. -/
structure StrongReimportClassCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type
    extends ReimportClassCorrespondence L₁ L₂ where
  /-- The forward transport certifies that the target reimport witness
  certifies the target imported sentence. -/
  forward_preserves_witness_certifies_imported :
    L₁.reimportClassWitness →
      L₂.comparison.reimportContent.certifies
        L₂.comparison.reimportContent.witness
        L₂.comparison.reimportContent.importedSentence
  /-- The forward transport certifies that the target imported sentence
  is true in the target reference model. -/
  forward_preserves_imported_true :
    L₁.reimportClassWitness →
      L₂.comparison.baseTheoryContent.trueInReferenceModel
        L₂.comparison.reimportContent.importedSentence

/-- Godel-to-DP reimport record whose added functions ignore the source proof and return target
support fields. -/
def godel_dp_strongReimportClassCorrespondence :
    StrongReimportClassCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  toReimportClassCorrespondence := godel_dp_reimportClassCorrespondence
  forward_preserves_witness_certifies_imported := by
    intro _
    exact dpEmitterReimportReversibilitySupport.witnessCertifiesImported
  forward_preserves_imported_true := by
    intro _
    exact dpEmitterReimportReversibilitySupport.importedTrue

/-! ## Annotation maps with designated-target laws

The added fields concern only the translation of the designated source annotation. They do not
constrain any other source annotation.
-/

/-- Strengthened annotation-functor correspondence. -/
structure StrongAnnotationFunctorCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type
    extends AnnotationFunctorCorrespondence L₁ L₂ where
  /-- The target reimport witness certifies the translated annotation's
  decode. -/
  translate_preserves_witness_certifies_decoded :
    L₂.comparison.reimportContent.certifies
        L₂.comparison.reimportContent.witness
        (L₂.annotationFunctor.decode
          (translateAnnotation
            (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness)))
  /-- The translated annotation's decode is true in the target reference
  model. -/
  translate_preserves_decoded_true :
    L₂.comparison.baseTheoryContent.trueInReferenceModel
      (L₂.annotationFunctor.decode
        (translateAnnotation
          (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness)))
  /-- The decoded translation of the designated source annotation equals the target imported
  sentence. -/
  translate_preserves_decodes_to_imported :
    L₂.annotationFunctor.decode
        (translateAnnotation
          (L₁.annotationFunctor.annotate L₁.comparison.reimportContent.witness))
      = L₂.comparison.reimportContent.importedSentence

/-- Constant Godel-to-DP annotation map with laws copied from the target annotation functor. -/
def godel_dp_strongAnnotationFunctorCorrespondence :
    StrongAnnotationFunctorCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  toAnnotationFunctorCorrespondence := godel_dp_annotationCorrespondence
  translate_preserves_witness_certifies_decoded :=
    dpEmitterLCELInstance.annotationFunctor.witness_certifies_decoded
  translate_preserves_decoded_true :=
    dpEmitterLCELInstance.annotationFunctor.witness_decoded_true
  translate_preserves_decodes_to_imported :=
    dpEmitterLCELInstance.annotationFunctor.witness_decodes_to_imported

/-! ## Base-sentence maps with one-way provability

`BaseSentenceCorrespondence` contains a sentence map and an implication from source provability to
target provability. It does not require reflection, injectivity, or dependence on the source
sentence.
-/

/-- A sentence map with a one-way provability implication. -/
structure BaseSentenceCorrespondence (L₁ L₂ : FormalLCELInstance) : Type where
  /-- Translate a source base-theory sentence to a target base-theory sentence. -/
  translateProvedSentence :
    L₁.comparison.baseTheoryContent.Sentence →
    L₂.comparison.baseTheoryContent.Sentence
  /-- Provability of a source sentence transports to provability of the
  translated target sentence. -/
  translateProvedSentence_preserves_provable :
    ∀ s : L₁.comparison.baseTheoryContent.Sentence,
      L₁.comparison.baseTheoryContent.proves s →
      L₂.comparison.baseTheoryContent.proves (translateProvedSentence s)

/-- Constant Godel-to-DP sentence map. Its implication ignores the source sentence and source proof
and returns the target support record's stored proof. -/
def godel_dp_baseSentenceCorrespondence :
    BaseSentenceCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  translateProvedSentence _ :=
    dpEmitterBaseReversibilitySupport.internalSentence
  translateProvedSentence_preserves_provable := by
    intro _ _
    exact dpEmitterBaseReversibilitySupport.internalSentenceProved

/-- Constant Godel-to-benchmark sentence map using the target support record's stored proof. -/
def godel_benchmark_baseSentenceCorrespondence :
    BaseSentenceCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  translateProvedSentence _ :=
    benchmarkTransportBaseReversibilitySupport.internalSentence
  translateProvedSentence_preserves_provable := by
    intro _ _
    exact benchmarkTransportBaseReversibilitySupport.internalSentenceProved

/-! ## Packaged slot maps with preservation fields

The package collects the four extended records and the base-sentence map. Downgrading drops the
added implication fields and base-sentence component.
-/

/-- Bundle the four extended slot records and the one-way base-sentence map. -/
structure LCELStrongSemanticSlotCorrespondence
    (L₁ L₂ : FormalLCELInstance) : Type where
  boundary : StrongBoundaryObjectCorrespondence L₁ L₂
  externalLicense : StrongExternalLicenseCorrespondence L₁ L₂
  reimportClass : StrongReimportClassCorrespondence L₁ L₂
  annotation : StrongAnnotationFunctorCorrespondence L₁ L₂
  baseSentence : BaseSentenceCorrespondence L₁ L₂

namespace LCELStrongSemanticSlotCorrespondence

/-- Downgrade to the plain semantic slot correspondence. -/
def toSlotCorrespondence
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELStrongSemanticSlotCorrespondence L₁ L₂) :
    LCELSemanticSlotCorrespondence L₁ L₂ where
  boundary := C.boundary.toBoundaryObjectCorrespondence
  externalLicense := C.externalLicense.toExternalLicenseCorrespondence
  reimportClass := C.reimportClass.toReimportClassCorrespondence
  annotation := C.annotation.toAnnotationFunctorCorrespondence

end LCELStrongSemanticSlotCorrespondence

/-- Package the constant-target Godel-to-DP components in the extended record. -/
def godel_dp_strongSemanticSlotCorrespondence :
    LCELStrongSemanticSlotCorrespondence
      godel1931LCELInstance
      dpEmitterLCELInstance where
  boundary := godel_dp_strongBoundaryCorrespondence
  externalLicense := godel_dp_strongExternalLicenseCorrespondence
  reimportClass := godel_dp_strongReimportClassCorrespondence
  annotation := godel_dp_strongAnnotationFunctorCorrespondence
  baseSentence := godel_dp_baseSentenceCorrespondence

/-! ## Extended constant-target maps for the Godel-to-benchmark pair

These records use the benchmark target's stored reflection, reimport, annotation, and base support
facts. Their maps and implications may ignore the source values and proofs.
-/

/-- Godel-to-benchmark license record using target support fields. -/
def godel_benchmark_strongExternalLicenseCorrespondence :
    StrongExternalLicenseCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  toExternalLicenseCorrespondence :=
    godel_benchmark_externalLicenseCorrespondence
  forward_preserves_blocked_not_provable := by
    intro _
    exact benchmarkTransportLCELInstance.comparison.reflectionContent.blocked_not_provable
  forward_preserves_stronger_reflects := by
    intro _
    exact benchmarkTransportLicenseIrreversibilitySupport.strongerFrameworkReflectsBlocked

/-- Godel-to-benchmark reimport record using target support fields. -/
def godel_benchmark_strongReimportClassCorrespondence :
    StrongReimportClassCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  toReimportClassCorrespondence := godel_benchmark_reimportClassCorrespondence
  forward_preserves_witness_certifies_imported := by
    intro _
    exact benchmarkTransportReimportReversibilitySupport.witnessCertifiesImported
  forward_preserves_imported_true := by
    intro _
    exact benchmarkTransportReimportReversibilitySupport.importedTrue

/-- Constant Godel-to-benchmark annotation map using target annotation fields. -/
def godel_benchmark_strongAnnotationFunctorCorrespondence :
    StrongAnnotationFunctorCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  toAnnotationFunctorCorrespondence := godel_benchmark_annotationCorrespondence
  translate_preserves_witness_certifies_decoded :=
    benchmarkTransportLCELInstance.annotationFunctor.witness_certifies_decoded
  translate_preserves_decoded_true :=
    benchmarkTransportLCELInstance.annotationFunctor.witness_decoded_true
  translate_preserves_decodes_to_imported :=
    benchmarkTransportLCELInstance.annotationFunctor.witness_decodes_to_imported

/-- Package the constant-target Godel-to-benchmark components in the extended record. -/
def godel_benchmark_strongSemanticSlotCorrespondence :
    LCELStrongSemanticSlotCorrespondence
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  boundary := godel_benchmark_strongBoundaryCorrespondence
  externalLicense := godel_benchmark_strongExternalLicenseCorrespondence
  reimportClass := godel_benchmark_strongReimportClassCorrespondence
  annotation := godel_benchmark_strongAnnotationFunctorCorrespondence
  baseSentence := godel_benchmark_baseSentenceCorrespondence

end OperatorKO7.LCELSemanticCorrespondence
