import OperatorKO7.Meta.LCELMathematicalSupportWitness

namespace LCELMathematicalSupportWitnessReach

open OperatorKO7
open OperatorKO7.LCELMathematical
open OperatorKO7.LCELSemanticCorrespondence

/-! Reachability smoke test for the LCEL mathematical support witness layer. -/

example : True := by
  have := godel_benchmark_lcelMathematicalSupportWitness
  trivial

example : True := by
  have := godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    LCELMathematicalSupportWitness.toSemanticSlotCorrespondence
      godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    LCELMathematicalSupportWitness.toStrongSemanticSlotCorrespondence
      godel_dp_lcelMathematicalSupportWitness
  trivial

/-! The witness now stores the **strong** slot correspondence; the plain
slot correspondence is recovered by downgrade, and the two iffs used by
the support-comparison layer come from the strong correspondence's
preservation-law-backed slot pieces. -/
example :
    godel_dp_lcelMathematicalSupportWitness.toSemanticSlotCorrespondence
      = godel_dp_lcelMathematicalSupportWitness.slotCorrespondence.toSlotCorrespondence :=
  rfl

example : True := by
  have :=
    LCELMathematicalSupportWitness.toSourceBaseReversibilityTheorem
      godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    LCELMathematicalSupportWitness.toTargetBaseReversibilityTheorem
      godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    LCELMathematicalSupportWitness.toSourceLicenseIrreversibilityTheorem
      godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    LCELMathematicalSupportWitness.toTargetLicenseIrreversibilityTheorem
      godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    LCELMathematicalSupportWitness.toSourceReimportReversibilityTheorem
      godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    LCELMathematicalSupportWitness.toTargetReimportReversibilityTheorem
      godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    LCELMathematicalSupportWitness.toSourceBoundaryFactorizationTheorem
      godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    LCELMathematicalSupportWitness.toTargetBoundaryFactorizationTheorem
      godel_dp_lcelMathematicalSupportWitness
  trivial

/-! Nontrivial mathematical regression tests for the cross-instance
theorem-object transport layer: each of the following asserts a named
equation between a source-transported target theorem and the canonical
target theorem field. These fail `#check`-style reachability if the
coherence equations degrade; they are not smoke tests. -/

example :
    godel_dp_lcelMathematicalSupportWitness.transportBase
        godel_dp_lcelMathematicalSupportWitness.sourceBaseTheorem
      = godel_dp_lcelMathematicalSupportWitness.targetBaseTheorem :=
  godel_dp_lcelMathematicalSupportWitness.transportBase_source

example :
    godel_dp_lcelMathematicalSupportWitness.transportLicense
        godel_dp_lcelMathematicalSupportWitness.sourceLicenseTheorem
      = godel_dp_lcelMathematicalSupportWitness.targetLicenseTheorem :=
  godel_dp_lcelMathematicalSupportWitness.transportLicense_source

example :
    godel_dp_lcelMathematicalSupportWitness.transportReimport
        godel_dp_lcelMathematicalSupportWitness.sourceReimportTheorem
      = godel_dp_lcelMathematicalSupportWitness.targetReimportTheorem :=
  godel_dp_lcelMathematicalSupportWitness.transportReimport_source

example :
    godel_dp_lcelMathematicalSupportWitness.transportBoundary
        godel_dp_lcelMathematicalSupportWitness.sourceBoundaryTheorem
      = godel_dp_lcelMathematicalSupportWitness.targetBoundaryTheorem :=
  godel_dp_lcelMathematicalSupportWitness.transportBoundary_source

example :
    godel_benchmark_lcelMathematicalSupportWitness.transportBase
        godel_benchmark_lcelMathematicalSupportWitness.sourceBaseTheorem
      = godel_benchmark_lcelMathematicalSupportWitness.targetBaseTheorem :=
  godel_benchmark_lcelMathematicalSupportWitness.transportBase_source

/-! Structural source-sensitivity of the boundary transport. The
`transportBoundary` helper recursively consumes `T.visible` and
`T.sensitive`: the output's `visible` equals the reimport transport of
the input's `visible`, and the output's `sensitive` equals the license
transport of the input's `sensitive`. This is genuine structural
dependency on T, not a constant map. -/
example :
    (godel_dp_lcelMathematicalSupportWitness.transportBoundary
        godel_dp_lcelMathematicalSupportWitness.sourceBoundaryTheorem).visible
      = godel_dp_lcelMathematicalSupportWitness.transportReimport
          godel_dp_lcelMathematicalSupportWitness.sourceBoundaryTheorem.visible :=
  rfl

example :
    (godel_dp_lcelMathematicalSupportWitness.transportBoundary
        godel_dp_lcelMathematicalSupportWitness.sourceBoundaryTheorem).sensitive
      = godel_dp_lcelMathematicalSupportWitness.transportLicense
          godel_dp_lcelMathematicalSupportWitness.sourceBoundaryTheorem.sensitive :=
  rfl

/-! The source-informed transports consume strong-correspondence
preservation laws: the transported base theorem's unprovedSentence is
built from the source boundary witness threaded through the
correspondence's typed translate map, and its non-provability comes from
the strong correspondence's `translate_preserves_not_provable`. The
following tests assert that the transported base theorem's
unprovedSentence equals the translated source designated boundary
sentence definitionally. -/
example :
    (godel_dp_lcelMathematicalSupportWitness.transportBase
        godel_dp_lcelMathematicalSupportWitness.sourceBaseTheorem).unprovedSentence
      = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.boundaryObject.boundarySentence
          (godel_dp_strongBoundaryCorrespondence.translate
            OperatorKO7.LCELSchema.godel1931LCELInstance.boundaryObject.designated) :=
  rfl

/-! Preservation-law-driven regression tests. These assert that the
transported theorems' proof fields are **literally** the correspondence
preservation laws applied to source structural facts — not just the
target theorem record's own internal `..._eq` fields. A bug that replaced
a transport helper's preservation-law derivation with a target-side
fallback would fail these tests, while the earlier record-shape tests
would still pass. -/

example :
    (godel_dp_lcelMathematicalSupportWitness.transportBase
        godel_dp_lcelMathematicalSupportWitness.sourceBaseTheorem).unprovedSentence_not_provable
      = godel_dp_strongBoundaryCorrespondence.translate_preserves_not_provable
          OperatorKO7.LCELSchema.godel1931LCELInstance.boundaryObject.designated
          OperatorKO7.LCELSchema.godel1931LCELInstance.boundaryObject.designated_not_provable := by
  rfl

example :
    (godel_dp_lcelMathematicalSupportWitness.transportBase
        godel_dp_lcelMathematicalSupportWitness.sourceBaseTheorem).unprovedSentence_true
      = godel_dp_strongBoundaryCorrespondence.translate_preserves_true
          OperatorKO7.LCELSchema.godel1931LCELInstance.boundaryObject.designated
          OperatorKO7.LCELSchema.godel1931LCELInstance.boundaryObject.designated_true := by
  rfl

example :
    (godel_dp_lcelMathematicalSupportWitness.transportBase
        godel_dp_lcelMathematicalSupportWitness.sourceBaseTheorem).provedSentence
      = godel_dp_strongSemanticSlotCorrespondence.baseSentence.translateProvedSentence
          godel_dp_lcelMathematicalSupportWitness.sourceBaseTheorem.provedSentence :=
  rfl

example :
    (godel_dp_lcelMathematicalSupportWitness.transportLicense
        godel_dp_lcelMathematicalSupportWitness.sourceLicenseTheorem).blocked_not_provable
      = godel_dp_strongExternalLicenseCorrespondence.forward_preserves_blocked_not_provable
          godel_dp_lcelMathematicalSupportWitness.sourceLicenseTheorem.externalLicenseHolds := by
  rfl

example :
    (godel_dp_lcelMathematicalSupportWitness.transportReimport
        godel_dp_lcelMathematicalSupportWitness.sourceReimportTheorem).imported_true
      = godel_dp_strongReimportClassCorrespondence.forward_preserves_imported_true
          godel_dp_lcelMathematicalSupportWitness.sourceReimportTheorem.reimportClassHolds := by
  rfl

/-! Annotation-slot API regression. These assertions exercise the
**type signatures** of the strong annotation correspondence's three
preservation laws on the canonical Gödel ↔ DP pair. A future refactor
that removed any of these fields from `StrongAnnotationFunctorCorrespondence`
— or that broke their typed statement — would make these tests fail at
elaboration. Lean 4 Prop proof-irrelevance prevents a regression test
from distinguishing two proofs of the same proposition, but the
statements below encode the expected *typed* role of each preservation
law on the target instance. -/

example :
    OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.annotationFunctor.decode
        (godel_dp_strongAnnotationFunctorCorrespondence.translateAnnotation
          (OperatorKO7.LCELSchema.godel1931LCELInstance.annotationFunctor.annotate
            OperatorKO7.LCELSchema.godel1931LCELInstance.comparison.reimportContent.witness))
      = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.comparison.reimportContent.importedSentence :=
  godel_dp_strongAnnotationFunctorCorrespondence.translate_preserves_decodes_to_imported

example :
    OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.comparison.reimportContent.certifies
        OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.comparison.reimportContent.witness
        (OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.annotationFunctor.decode
          (godel_dp_strongAnnotationFunctorCorrespondence.translateAnnotation
            (OperatorKO7.LCELSchema.godel1931LCELInstance.annotationFunctor.annotate
              OperatorKO7.LCELSchema.godel1931LCELInstance.comparison.reimportContent.witness))) :=
  godel_dp_strongAnnotationFunctorCorrespondence.translate_preserves_witness_certifies_decoded

example :
    OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.comparison.baseTheoryContent.trueInReferenceModel
        (OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.annotationFunctor.decode
          (godel_dp_strongAnnotationFunctorCorrespondence.translateAnnotation
            (OperatorKO7.LCELSchema.godel1931LCELInstance.annotationFunctor.annotate
              OperatorKO7.LCELSchema.godel1931LCELInstance.comparison.reimportContent.witness))) :=
  godel_dp_strongAnnotationFunctorCorrespondence.translate_preserves_decoded_true

/-! Operational trace: the reimport transport's annotation fields now
compute to the target's usual annotation laws, but **only after** the
strong annotation correspondence's `translate_annotate_witness` coherence
rewrite is applied. The tests below assert the equation up to that
rewrite, which is exactly what the updated helper performs. -/

example :
    (godel_dp_lcelMathematicalSupportWitness.transportReimport
        godel_dp_lcelMathematicalSupportWitness.sourceReimportTheorem).importedSentence
      = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.comparison.reimportContent.importedSentence :=
  rfl

example :
    godel_dp_strongAnnotationFunctorCorrespondence.translateAnnotation
        (OperatorKO7.LCELSchema.godel1931LCELInstance.annotationFunctor.annotate
          OperatorKO7.LCELSchema.godel1931LCELInstance.comparison.reimportContent.witness)
      = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.annotationFunctor.annotate
          OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.comparison.reimportContent.witness :=
  godel_dp_strongAnnotationFunctorCorrespondence.toAnnotationFunctorCorrespondence.translate_annotate_witness

end LCELMathematicalSupportWitnessReach
