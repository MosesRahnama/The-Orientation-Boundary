import OperatorKO7.Meta.LCELStructuralIdentity

namespace LCELDpInstanceReach

open OperatorKO7
open OperatorKO7.LCELDpInstance

example : True := by
  have := dpEmitterFormalExternalClassicalComparison_supported
  trivial

example : True := by
  have := dpEmitterFormalExternalClassicalComparison_semanticSupported
  trivial

example : True := by
  have := dpEmitterFormalExternalClassicalComparison_transferSupported
  trivial

example : True := by
  have := dpEmitterLCELInstance_realizesSchema
  trivial

example : True := by
  have := dpEmitter_semanticBaseLayerSupport
  trivial

example : True := by
  have := dpEmitter_semanticLicenseTransferSupport
  trivial

example : True := by
  have := dpEmitter_semanticReimportTransferSupport
  trivial

example : True := by
  have := dpEmitterLCELReversibilityAsymmetry
  trivial

example : True := by
  have := dpEmitterLCELBoundaryFactorization
  trivial

example :
    dpEmitterLCELInstance.externalLicenseObject.licensedSentence
        dpEmitterLCELInstance.externalLicenseObject.designated
      = dpEmitterLCELInstance.comparison.reflectionContent.blockedSentence :=
  dpEmitterLCELInstance.externalLicenseObject.designated_sentence_eq_blocked

example :
    dpEmitterLCELInstance.comparison.reimportContent.certifies
        (dpEmitterLCELInstance.reimportClassObject.admission
          dpEmitterLCELInstance.reimportClassObject.designated)
        (dpEmitterLCELInstance.reimportClassObject.importedSentence
          dpEmitterLCELInstance.reimportClassObject.designated) :=
  dpEmitterLCELInstance.reimportClassObject.designated_certifies

example : True := by
  have := OperatorKO7.LCELStructuralIdentity.godel_dpEmitter_lcelComparisonWitness
  trivial

example : True := by
  have := OperatorKO7.LCELStructuralIdentity.godel_dpEmitter_lcelSemanticComparisonWitness
  trivial

example : True := by
  have := OperatorKO7.LCELStructuralIdentity.godel_dpEmitter_lcelSupportComparisonWitness
  trivial

example : True := by
  have := OperatorKO7.LCELStructuralIdentity.godel_to_dpEmitter_lcelReversibilityAsymmetryFromSupport_via_semanticComparison
  trivial

example : True := by
  have := OperatorKO7.LCELStructuralIdentity.dpEmitter_to_godel_lcelReversibilityAsymmetryFromSupport_via_semanticComparison
  trivial

example : True := by
  have := OperatorKO7.LCELStructuralIdentity.godel_to_dpEmitter_lcelBoundaryFactorizationFromSupport_via_semanticComparison
  trivial

example : True := by
  have := OperatorKO7.LCELStructuralIdentity.dpEmitter_to_godel_lcelBoundaryFactorizationFromSupport_via_semanticComparison
  trivial

example : True := by
  have := OperatorKO7.LCELStructuralIdentity.godel_dp_lcel_structural_identity
  trivial

end LCELDpInstanceReach
