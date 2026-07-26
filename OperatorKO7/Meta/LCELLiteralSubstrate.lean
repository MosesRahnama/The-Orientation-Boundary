import OperatorKO7.Meta.LCELSubstrateMathematics
import OperatorKO7.Meta.LCELMathematicalSupportWitness

/-!
This module packages LCEL-carrier propositions and projects their fields. Godel-labelled values
are internal carrier instances. Sentence-level transport is represented by a separate
factorization record with supplied correspondence.












-/

namespace OperatorKO7.LCELLiteralSubstrate

open OperatorKO7.LCELSchema
open OperatorKO7.LCELSubstrateMathematics
open OperatorKO7.LCELMathematical

/-- Definition with formal content given by the displayed type and body.
-/
def LiteralBaseReversibility (L : FormalLCELInstance) : Prop :=
  ∃ provedSentence unprovedSentence : L.comparison.baseTheoryContent.Sentence,
    L.comparison.baseTheoryContent.proves provedSentence ∧
    unprovedSentence =
      L.boundaryObject.boundarySentence L.boundaryObject.designated ∧
    ¬ L.comparison.baseTheoryContent.proves unprovedSentence ∧
    L.comparison.baseTheoryContent.trueInReferenceModel unprovedSentence ∧
    provedSentence ≠ unprovedSentence

/-- Definition with formal content given by the displayed type and body.
-/
def LiteralLicenseIrreversibility (L : FormalLCELInstance) : Prop :=
  ∃ blockedSentence : L.comparison.baseTheoryContent.Sentence,
    blockedSentence = L.comparison.reflectionContent.blockedSentence ∧
    ¬ L.comparison.baseTheoryContent.proves blockedSentence ∧
    L.comparison.baseTheoryContent.trueInReferenceModel blockedSentence ∧
    L.comparison.reflectionContent.reflects
      L.comparison.reflectionContent.strongerFramework
      blockedSentence ∧
    L.externalLicenseWitness ∧
    L.comparison.reflectionContent.licensedAdmission blockedSentence

/-- Definition with formal content given by the displayed type and body.
-/
def LiteralReimportReversibility (L : FormalLCELInstance) : Prop :=
  ∃ importedSentence : L.comparison.baseTheoryContent.Sentence,
    importedSentence = L.comparison.reimportContent.importedSentence ∧
    L.comparison.baseTheoryContent.trueInReferenceModel importedSentence ∧
    L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      importedSentence ∧
    L.reimportClassWitness ∧
    L.annotationFunctor.decode
        (L.annotationFunctor.annotate L.comparison.reimportContent.witness)
      = importedSentence ∧
    L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      (L.annotationFunctor.decode
        (L.annotationFunctor.annotate L.comparison.reimportContent.witness))

/-- Definition with formal content given by the displayed type and body.

-/
def SentenceLevelBoundaryFactorization (L : FormalLCELInstance) : Prop :=
  ∃ blockedSentence importedSentence : L.comparison.baseTheoryContent.Sentence,
    L.comparison.obstructionContent.blockedBy
        L.comparison.obstructionContent.witness
      = blockedSentence ∧
    blockedSentence = importedSentence ∧
    ¬ L.comparison.baseTheoryContent.proves blockedSentence ∧
    L.comparison.baseTheoryContent.trueInReferenceModel blockedSentence ∧
    L.comparison.reflectionContent.reflects
      L.comparison.reflectionContent.strongerFramework
      blockedSentence ∧
    L.externalLicenseWitness ∧
    L.comparison.reflectionContent.licensedAdmission blockedSentence ∧
    importedSentence = L.comparison.reimportContent.importedSentence ∧
    L.comparison.baseTheoryContent.trueInReferenceModel importedSentence ∧
    L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      importedSentence ∧
    L.reimportClassWitness ∧
    L.annotationFunctor.decode
        (L.annotationFunctor.annotate L.comparison.reimportContent.witness)
      = importedSentence ∧
    L.comparison.reimportContent.certifies
      L.comparison.reimportContent.witness
      (L.annotationFunctor.decode
        (L.annotationFunctor.annotate L.comparison.reimportContent.witness)) ∧
    L.boundaryObject.realized

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem literalBaseReversibility_of_theorem
    {L : FormalLCELInstance}
    (T : BaseReversibilityTheorem L) :
    LiteralBaseReversibility L := by
  refine ⟨T.provedSentence, T.unprovedSentence, T.provedSentence_proved, ?_⟩
  refine ⟨T.unprovedSentence_eq, T.unprovedSentence_not_provable, ?_⟩
  exact ⟨T.unprovedSentence_true, T.distinct⟩

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem literalLicenseIrreversibility_of_theorem
    {L : FormalLCELInstance}
    (T : LicenseIrreversibilityTheorem L) :
    LiteralLicenseIrreversibility L := by
  refine ⟨T.blockedSentence, T.blockedSentence_eq, T.blocked_not_provable, ?_⟩
  refine ⟨T.blocked_true, T.stronger_reflects_blocked, ?_⟩
  exact ⟨T.externalLicenseHolds, T.blocked_licensedAdmission⟩

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem literalReimportReversibility_of_theorem
    {L : FormalLCELInstance}
    (T : ReimportReversibilityTheorem L) :
    LiteralReimportReversibility L := by
  refine ⟨T.importedSentence, T.importedSentence_eq, T.imported_true, ?_⟩
  refine ⟨T.witness_certifies_imported, T.reimportClassHolds, ?_⟩
  exact ⟨T.annotationDecodes_imported, T.annotationCertifiesDecoded⟩

namespace BoundaryFactorizationTheorem

/-- The displayed proposition follows from the stated hypotheses. -/
theorem sensitiveBlocked_eq_visibleImported
    {L : FormalLCELInstance}
    (T : BoundaryFactorizationTheorem L) :
    T.sensitive.blockedSentence = T.visible.importedSentence := by
  rw [T.sensitive.blockedSentence_eq, T.reflectionBlockedEqImported,
    T.visible.importedSentence_eq.symm]

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem obstructionBlocked_eq_sensitiveBlocked
    {L : FormalLCELInstance}
    (T : BoundaryFactorizationTheorem L) :
    L.comparison.obstructionContent.blockedBy
        L.comparison.obstructionContent.witness
      = T.sensitive.blockedSentence := by
  rw [T.sensitive.blockedSentence_eq]
  exact T.obstructionBlockedEqReflectionBlocked

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem obstructionBlocked_eq_visibleImported
    {L : FormalLCELInstance}
    (T : BoundaryFactorizationTheorem L) :
    L.comparison.obstructionContent.blockedBy
        L.comparison.obstructionContent.witness
      = T.visible.importedSentence := by
  exact (obstructionBlocked_eq_sensitiveBlocked T).trans
    (sensitiveBlocked_eq_visibleImported T)

end BoundaryFactorizationTheorem

/-- The displayed proposition follows from the stated hypotheses.
-/
theorem sentenceLevelBoundaryFactorization_of_theorem
    {L : FormalLCELInstance}
    (T : BoundaryFactorizationTheorem L) :
    SentenceLevelBoundaryFactorization L := by
  refine ⟨T.sensitive.blockedSentence, T.visible.importedSentence, ?_⟩
  refine ⟨BoundaryFactorizationTheorem.obstructionBlocked_eq_sensitiveBlocked T,
    BoundaryFactorizationTheorem.sensitiveBlocked_eq_visibleImported T,
    T.sensitive.blocked_not_provable, ?_⟩
  refine ⟨T.sensitive.blocked_true, T.sensitive.stronger_reflects_blocked, ?_⟩
  refine ⟨T.sensitive.externalLicenseHolds, T.sensitive.blocked_licensedAdmission,
    T.visible.importedSentence_eq, ?_⟩
  refine ⟨T.visible.imported_true, T.visible.witness_certifies_imported,
    T.visible.reimportClassHolds, ?_⟩
  refine ⟨T.visible.annotationDecodes_imported,
    T.visible.annotationCertifiesDecoded, T.boundaryRealized⟩

/-! Declarations for the section below. -/

theorem godel1931LiteralBaseReversibility :
    LiteralBaseReversibility godel1931LCELInstance :=
  literalBaseReversibility_of_theorem godel1931BaseReversibilityTheorem

theorem benchmarkTransportLiteralBaseReversibility :
    LiteralBaseReversibility benchmarkTransportLCELInstance :=
  literalBaseReversibility_of_theorem benchmarkTransportBaseReversibilityTheorem

theorem dpEmitterLiteralBaseReversibility :
  LiteralBaseReversibility OperatorKO7.LCELDpInstance.dpEmitterLCELInstance :=
  literalBaseReversibility_of_theorem dpEmitterBaseReversibilityTheorem

theorem godel1931LiteralLicenseIrreversibility :
    LiteralLicenseIrreversibility godel1931LCELInstance :=
  literalLicenseIrreversibility_of_theorem
    godel1931LicenseIrreversibilityTheorem

theorem benchmarkTransportLiteralLicenseIrreversibility :
    LiteralLicenseIrreversibility benchmarkTransportLCELInstance :=
  literalLicenseIrreversibility_of_theorem
    benchmarkTransportLicenseIrreversibilityTheorem

theorem dpEmitterLiteralLicenseIrreversibility :
    LiteralLicenseIrreversibility OperatorKO7.LCELDpInstance.dpEmitterLCELInstance :=
  literalLicenseIrreversibility_of_theorem
    dpEmitterLicenseIrreversibilityTheorem

theorem godel1931LiteralReimportReversibility :
    LiteralReimportReversibility godel1931LCELInstance :=
  literalReimportReversibility_of_theorem
    godel1931ReimportReversibilityTheorem

theorem benchmarkTransportLiteralReimportReversibility :
    LiteralReimportReversibility benchmarkTransportLCELInstance :=
  literalReimportReversibility_of_theorem
    benchmarkTransportReimportReversibilityTheorem

theorem dpEmitterLiteralReimportReversibility :
    LiteralReimportReversibility OperatorKO7.LCELDpInstance.dpEmitterLCELInstance :=
  literalReimportReversibility_of_theorem
    dpEmitterReimportReversibilityTheorem

theorem godel1931SentenceLevelBoundaryFactorization :
    SentenceLevelBoundaryFactorization godel1931LCELInstance :=
  sentenceLevelBoundaryFactorization_of_theorem
    godel1931BoundaryFactorizationTheorem

theorem benchmarkTransportSentenceLevelBoundaryFactorization :
    SentenceLevelBoundaryFactorization benchmarkTransportLCELInstance :=
  sentenceLevelBoundaryFactorization_of_theorem
    benchmarkTransportBoundaryFactorizationTheorem

theorem dpEmitterSentenceLevelBoundaryFactorization :
    SentenceLevelBoundaryFactorization OperatorKO7.LCELDpInstance.dpEmitterLCELInstance :=
  sentenceLevelBoundaryFactorization_of_theorem
    dpEmitterBoundaryFactorizationTheorem

/-! Declarations for the section below. -/

theorem sourceLiteralBaseReversibility
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LiteralBaseReversibility L₁ :=
  literalBaseReversibility_of_theorem W.sourceBaseTheorem

theorem targetLiteralBaseReversibility
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LiteralBaseReversibility L₂ :=
  literalBaseReversibility_of_theorem W.targetBaseTheorem

theorem transportedTargetLiteralBaseReversibility
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LiteralBaseReversibility L₂ :=
  literalBaseReversibility_of_theorem (W.transportBase W.sourceBaseTheorem)

theorem sourceLiteralLicenseIrreversibility
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LiteralLicenseIrreversibility L₁ :=
  literalLicenseIrreversibility_of_theorem W.sourceLicenseTheorem

theorem targetLiteralLicenseIrreversibility
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LiteralLicenseIrreversibility L₂ :=
  literalLicenseIrreversibility_of_theorem W.targetLicenseTheorem

theorem transportedTargetLiteralLicenseIrreversibility
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LiteralLicenseIrreversibility L₂ :=
  literalLicenseIrreversibility_of_theorem
    (W.transportLicense W.sourceLicenseTheorem)

theorem sourceLiteralReimportReversibility
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LiteralReimportReversibility L₁ :=
  literalReimportReversibility_of_theorem W.sourceReimportTheorem

theorem targetLiteralReimportReversibility
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LiteralReimportReversibility L₂ :=
  literalReimportReversibility_of_theorem W.targetReimportTheorem

theorem transportedTargetLiteralReimportReversibility
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    LiteralReimportReversibility L₂ :=
  literalReimportReversibility_of_theorem
    (W.transportReimport W.sourceReimportTheorem)

theorem sourceSentenceLevelBoundaryFactorization
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    SentenceLevelBoundaryFactorization L₁ :=
  sentenceLevelBoundaryFactorization_of_theorem W.sourceBoundaryTheorem

theorem targetSentenceLevelBoundaryFactorization
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    SentenceLevelBoundaryFactorization L₂ :=
  sentenceLevelBoundaryFactorization_of_theorem W.targetBoundaryTheorem

theorem transportedTargetSentenceLevelBoundaryFactorization
    {L₁ L₂ : FormalLCELInstance}
    (W : LCELMathematicalSupportWitness L₁ L₂) :
    SentenceLevelBoundaryFactorization L₂ :=
  sentenceLevelBoundaryFactorization_of_theorem
    (W.transportBoundary W.sourceBoundaryTheorem)

end OperatorKO7.LCELLiteralSubstrate
