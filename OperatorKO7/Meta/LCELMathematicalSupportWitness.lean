import OperatorKO7.Meta.LCELSchema
import OperatorKO7.Meta.LCELReversibility
import OperatorKO7.Meta.LCELDpInstance
import OperatorKO7.Meta.LCELStructuralIdentity
import OperatorKO7.Meta.LCELSemanticCorrespondence
import OperatorKO7.Meta.LCELSubstrateMathematics
import OperatorKO7.Meta.LCELBenchmarkDpComparison

/-!
This module assembles mathematical-support records from supplied translation maps, target facts,
admissibility, and coherence equations. The resulting theorems certify those record fields.
Independent semantic transport from source theorems requires a separately proved correspondence.





























-/

namespace OperatorKO7.LCELMathematical

open OperatorKO7.LCELSchema
open OperatorKO7.LCELReversibility
open OperatorKO7.LCELStructuralIdentity
open OperatorKO7.LCELDpInstance
open OperatorKO7.LCELSemanticCorrespondence
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELBenchmarkDpComparison

/-! Declarations for the section below. -/

/-- Data record whose requirements are the fields displayed below.










-/
structure LCELMathematicalSupportWitness
    (L₁ L₂ : FormalLCELInstance)
    extends LCELSupportComparisonWitness L₁ L₂ where
  /-- Field requirements are given by the displayed type.



-/
  slotCorrespondence : LCELStrongSemanticSlotCorrespondence L₁ L₂
  /-- Field requirements are given by the displayed type.
-/
  externalLicense_fromCorrespondence :
    externalLicenseEquivalent =
      slotCorrespondence.externalLicense.toExternalLicenseCorrespondence.toIff
  /-- Field requirements are given by the displayed type.
-/
  reimportClass_fromCorrespondence :
    reimportClassEquivalent =
      slotCorrespondence.reimportClass.toReimportClassCorrespondence.toIff
  /-- Field requirements are given by the displayed type. -/
  sourceBaseTheorem : BaseReversibilityTheorem L₁
  /-- Field requirements are given by the displayed type. -/
  targetBaseTheorem : BaseReversibilityTheorem L₂
  /-- Field requirements are given by the displayed type.
-/
  sourceBaseTheorem_fromSupport :
    sourceBaseTheorem = baseReversibilityTheorem_of_support sourceBaseSupport
  /-- Field requirements are given by the displayed type.
-/
  targetBaseTheorem_fromSupport :
    targetBaseTheorem = baseReversibilityTheorem_of_support targetBaseSupport
  /-- Field requirements are given by the displayed type. -/
  sourceLicenseTheorem : LicenseIrreversibilityTheorem L₁
  /-- Field requirements are given by the displayed type. -/
  targetLicenseTheorem : LicenseIrreversibilityTheorem L₂
  /-- Field requirements are given by the displayed type.
-/
  sourceLicenseTheorem_fromSupport :
    sourceLicenseTheorem =
      licenseIrreversibilityTheorem_of_support sourceLicenseSupport
  /-- Field requirements are given by the displayed type.
-/
  targetLicenseTheorem_fromSupport :
    targetLicenseTheorem =
      licenseIrreversibilityTheorem_of_support targetLicenseSupport
  /-- Field requirements are given by the displayed type. -/
  sourceReimportTheorem : ReimportReversibilityTheorem L₁
  /-- Field requirements are given by the displayed type. -/
  targetReimportTheorem : ReimportReversibilityTheorem L₂
  /-- Field requirements are given by the displayed type.
-/
  sourceReimportTheorem_fromSupport :
    sourceReimportTheorem =
      reimportReversibilityTheorem_of_support sourceReimportSupport
  /-- Field requirements are given by the displayed type.
-/
  targetReimportTheorem_fromSupport :
    targetReimportTheorem =
      reimportReversibilityTheorem_of_support targetReimportSupport
  /-- Field requirements are given by the displayed type. -/
  sourceBoundaryTheorem : BoundaryFactorizationTheorem L₁
  /-- Field requirements are given by the displayed type. -/
  targetBoundaryTheorem : BoundaryFactorizationTheorem L₂
  /-- Field requirements are given by the displayed type.
-/
  sourceBoundaryTheorem_fromSupport :
    sourceBoundaryTheorem =
      boundaryFactorizationTheorem_of_support sourceBoundarySupport
  /-- Field requirements are given by the displayed type.
-/
  targetBoundaryTheorem_fromSupport :
    targetBoundaryTheorem =
      boundaryFactorizationTheorem_of_support targetBoundarySupport
  /-- Field requirements are given by the displayed type.



-/
  transportBase :
    BaseReversibilityTheorem L₁ → BaseReversibilityTheorem L₂
  /-- Field requirements are given by the displayed type.



-/
  transportBase_source :
    transportBase sourceBaseTheorem = targetBaseTheorem
  /-- Field requirements are given by the displayed type.
-/
  transportLicense :
    LicenseIrreversibilityTheorem L₁ → LicenseIrreversibilityTheorem L₂
  /-- Field requirements are given by the displayed type. -/
  transportLicense_source :
    transportLicense sourceLicenseTheorem = targetLicenseTheorem
  /-- Field requirements are given by the displayed type.
-/
  transportReimport :
    ReimportReversibilityTheorem L₁ → ReimportReversibilityTheorem L₂
  /-- Field requirements are given by the displayed type. -/
  transportReimport_source :
    transportReimport sourceReimportTheorem = targetReimportTheorem
  /-- Field requirements are given by the displayed type.
-/
  transportBoundary :
    BoundaryFactorizationTheorem L₁ → BoundaryFactorizationTheorem L₂
  /-- Field requirements are given by the displayed type. -/
  transportBoundary_source :
    transportBoundary sourceBoundaryTheorem = targetBoundaryTheorem

namespace LCELMathematicalSupportWitness

/-- Definition with formal content given by the displayed type and body. -/
def toStrongSemanticSlotCorrespondence
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LCELStrongSemanticSlotCorrespondence L₁ L₂ :=
  W.slotCorrespondence

/-- Definition with formal content given by the displayed type and body.
-/
def toSemanticSlotCorrespondence
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LCELSemanticSlotCorrespondence L₁ L₂ :=
  W.slotCorrespondence.toSlotCorrespondence

/-- Definition with formal content given by the displayed type and body. -/
def toSourceBaseReversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BaseReversibilityTheorem L₁ :=
  W.sourceBaseTheorem

/-- Definition with formal content given by the displayed type and body. -/
def toTargetBaseReversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BaseReversibilityTheorem L₂ :=
  W.targetBaseTheorem

/-- Definition with formal content given by the displayed type and body.
-/
def toSourceLicenseIrreversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LicenseIrreversibilityTheorem L₁ :=
  W.sourceLicenseTheorem

/-- Definition with formal content given by the displayed type and body.
-/
def toTargetLicenseIrreversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LicenseIrreversibilityTheorem L₂ :=
  W.targetLicenseTheorem

/-- Definition with formal content given by the displayed type and body.
-/
def toSourceReimportReversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    ReimportReversibilityTheorem L₁ :=
  W.sourceReimportTheorem

/-- Definition with formal content given by the displayed type and body.
-/
def toTargetReimportReversibilityTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    ReimportReversibilityTheorem L₂ :=
  W.targetReimportTheorem

/-- Definition with formal content given by the displayed type and body.
-/
def toSourceBoundaryFactorizationTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BoundaryFactorizationTheorem L₁ :=
  W.sourceBoundaryTheorem

/-- Definition with formal content given by the displayed type and body.
-/
def toTargetBoundaryFactorizationTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BoundaryFactorizationTheorem L₂ :=
  W.targetBoundaryTheorem

/-! Declarations for the section below.







-/

/-- Definition with formal content given by the displayed type and body. -/
def transportedTargetBaseTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BaseReversibilityTheorem L₂ :=
  W.transportBase W.sourceBaseTheorem

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem transportedTargetBaseTheorem_eq
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportedTargetBaseTheorem = W.targetBaseTheorem :=
  W.transportBase_source

/-- Definition with formal content given by the displayed type and body. -/
def transportedTargetLicenseTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LicenseIrreversibilityTheorem L₂ :=
  W.transportLicense W.sourceLicenseTheorem

theorem transportedTargetLicenseTheorem_eq
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportedTargetLicenseTheorem = W.targetLicenseTheorem :=
  W.transportLicense_source

/-- Definition with formal content given by the displayed type and body. -/
def transportedTargetReimportTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    ReimportReversibilityTheorem L₂ :=
  W.transportReimport W.sourceReimportTheorem

theorem transportedTargetReimportTheorem_eq
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportedTargetReimportTheorem = W.targetReimportTheorem :=
  W.transportReimport_source

/-- Definition with formal content given by the displayed type and body. -/
def transportedTargetBoundaryTheorem
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    BoundaryFactorizationTheorem L₂ :=
  W.transportBoundary W.sourceBoundaryTheorem

theorem transportedTargetBoundaryTheorem_eq
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    W.transportedTargetBoundaryTheorem = W.targetBoundaryTheorem :=
  W.transportBoundary_source

end LCELMathematicalSupportWitness

/-! Declarations for the section below.













































-/

open OperatorKO7.ReflectionSchema in
/-- Definition with formal content given by the displayed type and body.








-/
def baseReversibilityTheorem_transport_viaStrongSlot
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELStrongSemanticSlotCorrespondence L₁ L₂)
    (T : BaseReversibilityTheorem L₁) :
    BaseReversibilityTheorem L₂ where
  provedSentence := C.baseSentence.translateProvedSentence T.provedSentence
  provedSentence_proved :=
    C.baseSentence.translateProvedSentence_preserves_provable
      T.provedSentence T.provedSentence_proved
  unprovedSentence :=
    L₂.boundaryObject.boundarySentence
      (C.boundary.translate L₁.boundaryObject.designated)
  unprovedSentence_eq := by
    rw [C.boundary.translate_designated]
  unprovedSentence_not_provable :=
    C.boundary.translate_preserves_not_provable
      L₁.boundaryObject.designated
      L₁.boundaryObject.designated_not_provable
  unprovedSentence_true :=
    C.boundary.translate_preserves_true
      L₁.boundaryObject.designated
      L₁.boundaryObject.designated_true
  distinct := by
    intro h
    apply C.boundary.translate_preserves_not_provable
      L₁.boundaryObject.designated
      L₁.boundaryObject.designated_not_provable
    rw [← h]
    exact C.baseSentence.translateProvedSentence_preserves_provable
      T.provedSentence T.provedSentence_proved

/-- Definition with formal content given by the displayed type and body.







-/
def licenseIrreversibilityTheorem_transport_viaStrongSlot
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELStrongSemanticSlotCorrespondence L₁ L₂)
    (targetLicensedAdmission :
      L₂.comparison.reflectionContent.licensedAdmission
        L₂.comparison.reflectionContent.blockedSentence)
    (T : LicenseIrreversibilityTheorem L₁) :
    LicenseIrreversibilityTheorem L₂ where
  blockedSentence := L₂.comparison.reflectionContent.blockedSentence
  blockedSentence_eq := rfl
  blocked_not_provable :=
    C.externalLicense.forward_preserves_blocked_not_provable T.externalLicenseHolds
  blocked_true :=
    L₂.comparison.reflectionContent.blocked_true
  stronger_reflects_blocked :=
    C.externalLicense.forward_preserves_stronger_reflects T.externalLicenseHolds
  externalLicenseHolds :=
    C.externalLicense.toExternalLicenseCorrespondence.forward T.externalLicenseHolds
  blocked_licensedAdmission := targetLicensedAdmission
  licenseExtendsBase :=
    ⟨C.externalLicense.forward_preserves_blocked_not_provable T.externalLicenseHolds,
      C.externalLicense.forward_preserves_stronger_reflects T.externalLicenseHolds⟩

/-- Definition with formal content given by the displayed type and body.







-/
def reimportReversibilityTheorem_transport_viaStrongSlot
    {L₁ L₂ : FormalLCELInstance}
    (C : LCELStrongSemanticSlotCorrespondence L₁ L₂)
    (T : ReimportReversibilityTheorem L₁) :
    ReimportReversibilityTheorem L₂ where
  importedSentence := L₂.comparison.reimportContent.importedSentence
  importedSentence_eq := rfl
  imported_true :=
    C.reimportClass.forward_preserves_imported_true T.reimportClassHolds
  witness_certifies_imported :=
    C.reimportClass.forward_preserves_witness_certifies_imported T.reimportClassHolds
  reimportClassHolds :=
    C.reimportClass.toReimportClassCorrespondence.forward T.reimportClassHolds
  annotationDecodes_imported := by
    --
    --
    --
    --
    have h := C.annotation.toAnnotationFunctorCorrespondence.translate_annotate_witness
    have pres := C.annotation.translate_preserves_decodes_to_imported
    rw [h] at pres
    exact pres
  annotationCertifiesDecoded := by
    --
    --
    --
    --
    --
    have h := C.annotation.toAnnotationFunctorCorrespondence.translate_annotate_witness
    have pres := C.annotation.translate_preserves_witness_certifies_decoded
    rw [h] at pres
    exact pres

/-- Definition with formal content given by the displayed type and body.




-/
def boundaryFactorizationTheorem_transport
    {L₁ L₂ : FormalLCELInstance}
    (reimportTransport :
      ReimportReversibilityTheorem L₁ → ReimportReversibilityTheorem L₂)
    (licenseTransport :
      LicenseIrreversibilityTheorem L₁ → LicenseIrreversibilityTheorem L₂)
    (targetObstructionBlockedEqReflectionBlocked :
      L₂.comparison.obstructionContent.blockedBy
          L₂.comparison.obstructionContent.witness
        = L₂.comparison.reflectionContent.blockedSentence)
    (targetReflectionBlockedEqImported :
      L₂.comparison.reflectionContent.blockedSentence
        = L₂.comparison.reimportContent.importedSentence)
    (targetBoundaryRealized : L₂.boundaryObject.realized)
    (T : BoundaryFactorizationTheorem L₁) :
    BoundaryFactorizationTheorem L₂ where
  visible := reimportTransport T.visible
  sensitive := licenseTransport T.sensitive
  obstructionBlockedEqReflectionBlocked :=
    targetObstructionBlockedEqReflectionBlocked
  reflectionBlockedEqImported := targetReflectionBlockedEqImported
  boundaryRealized := targetBoundaryRealized

/-! Declarations for the section below.












-/

/-- Definition with formal content given by the displayed type and body.
-/
def godel_benchmark_lcelMathematicalSupportWitness :
    LCELMathematicalSupportWitness
      godel1931LCELInstance
      benchmarkTransportLCELInstance where
  toLCELSupportComparisonWitness :=
    { godel_benchmark_lcelSupportComparisonWitness with
      externalLicenseEquivalent :=
        godel_benchmark_strongSemanticSlotCorrespondence.externalLicense.toExternalLicenseCorrespondence.toIff
      reimportClassEquivalent :=
        godel_benchmark_strongSemanticSlotCorrespondence.reimportClass.toReimportClassCorrespondence.toIff }
  slotCorrespondence := godel_benchmark_strongSemanticSlotCorrespondence
  externalLicense_fromCorrespondence := rfl
  reimportClass_fromCorrespondence := rfl
  sourceBaseTheorem := godel1931BaseReversibilityTheorem
  targetBaseTheorem := benchmarkTransportBaseReversibilityTheorem
  sourceBaseTheorem_fromSupport := rfl
  targetBaseTheorem_fromSupport := rfl
  sourceLicenseTheorem := godel1931LicenseIrreversibilityTheorem
  targetLicenseTheorem := benchmarkTransportLicenseIrreversibilityTheorem
  sourceLicenseTheorem_fromSupport := rfl
  targetLicenseTheorem_fromSupport := rfl
  sourceReimportTheorem := godel1931ReimportReversibilityTheorem
  targetReimportTheorem := benchmarkTransportReimportReversibilityTheorem
  sourceReimportTheorem_fromSupport := rfl
  targetReimportTheorem_fromSupport := rfl
  sourceBoundaryTheorem := godel1931BoundaryFactorizationTheorem
  targetBoundaryTheorem := benchmarkTransportBoundaryFactorizationTheorem
  sourceBoundaryTheorem_fromSupport := rfl
  targetBoundaryTheorem_fromSupport := rfl
  transportBase := fun T =>
    baseReversibilityTheorem_transport_viaStrongSlot
      godel_benchmark_strongSemanticSlotCorrespondence T
  transportBase_source := rfl
  transportLicense := fun T =>
    licenseIrreversibilityTheorem_transport_viaStrongSlot
      godel_benchmark_strongSemanticSlotCorrespondence
      benchmarkTransportLicenseIrreversibilitySupport.blockedLicensedAdmission
      T
  transportLicense_source := rfl
  transportReimport := fun T =>
    reimportReversibilityTheorem_transport_viaStrongSlot
      godel_benchmark_strongSemanticSlotCorrespondence T
  transportReimport_source := rfl
  transportBoundary := fun T =>
    boundaryFactorizationTheorem_transport
      (fun T' =>
        reimportReversibilityTheorem_transport_viaStrongSlot
          godel_benchmark_strongSemanticSlotCorrespondence T')
      (fun T' =>
        licenseIrreversibilityTheorem_transport_viaStrongSlot
          godel_benchmark_strongSemanticSlotCorrespondence
          benchmarkTransportLicenseIrreversibilitySupport.blockedLicensedAdmission
          T')
      benchmarkTransportBoundaryFactorizationSupport.obstructionBlockedEqReflectionBlocked
      benchmarkTransportBoundaryFactorizationSupport.reflectionBlockedEqImported
      benchmarkTransportBoundaryFactorizationSupport.boundaryRealized
      T
  transportBoundary_source := rfl

/-- Definition with formal content given by the displayed type and body.
-/
def godel_dp_lcelMathematicalSupportWitness :
    LCELMathematicalSupportWitness
      godel1931LCELInstance
      dpEmitterLCELInstance where
  toLCELSupportComparisonWitness :=
    { godel_dpEmitter_lcelSupportComparisonWitness with
      externalLicenseEquivalent :=
        godel_dp_strongSemanticSlotCorrespondence.externalLicense.toExternalLicenseCorrespondence.toIff
      reimportClassEquivalent :=
        godel_dp_strongSemanticSlotCorrespondence.reimportClass.toReimportClassCorrespondence.toIff }
  slotCorrespondence := godel_dp_strongSemanticSlotCorrespondence
  externalLicense_fromCorrespondence := rfl
  reimportClass_fromCorrespondence := rfl
  sourceBaseTheorem := godel1931BaseReversibilityTheorem
  targetBaseTheorem := dpEmitterBaseReversibilityTheorem
  sourceBaseTheorem_fromSupport := rfl
  targetBaseTheorem_fromSupport := rfl
  sourceLicenseTheorem := godel1931LicenseIrreversibilityTheorem
  targetLicenseTheorem := dpEmitterLicenseIrreversibilityTheorem
  sourceLicenseTheorem_fromSupport := rfl
  targetLicenseTheorem_fromSupport := rfl
  sourceReimportTheorem := godel1931ReimportReversibilityTheorem
  targetReimportTheorem := dpEmitterReimportReversibilityTheorem
  sourceReimportTheorem_fromSupport := rfl
  targetReimportTheorem_fromSupport := rfl
  sourceBoundaryTheorem := godel1931BoundaryFactorizationTheorem
  targetBoundaryTheorem := dpEmitterBoundaryFactorizationTheorem
  sourceBoundaryTheorem_fromSupport := rfl
  targetBoundaryTheorem_fromSupport := rfl
  transportBase := fun T =>
    baseReversibilityTheorem_transport_viaStrongSlot
      godel_dp_strongSemanticSlotCorrespondence T
  transportBase_source := rfl
  transportLicense := fun T =>
    licenseIrreversibilityTheorem_transport_viaStrongSlot
      godel_dp_strongSemanticSlotCorrespondence
      dpEmitterLicenseIrreversibilitySupport.blockedLicensedAdmission
      T
  transportLicense_source := rfl
  transportReimport := fun T =>
    reimportReversibilityTheorem_transport_viaStrongSlot
      godel_dp_strongSemanticSlotCorrespondence T
  transportReimport_source := rfl
  transportBoundary := fun T =>
    boundaryFactorizationTheorem_transport
      (fun T' =>
        reimportReversibilityTheorem_transport_viaStrongSlot
          godel_dp_strongSemanticSlotCorrespondence T')
      (fun T' =>
        licenseIrreversibilityTheorem_transport_viaStrongSlot
          godel_dp_strongSemanticSlotCorrespondence
          dpEmitterLicenseIrreversibilitySupport.blockedLicensedAdmission
          T')
      dpEmitterBoundaryFactorizationSupport.obstructionBlockedEqReflectionBlocked
      dpEmitterBoundaryFactorizationSupport.reflectionBlockedEqImported
      dpEmitterBoundaryFactorizationSupport.boundaryRealized
      T
  transportBoundary_source := rfl

end OperatorKO7.LCELMathematical
