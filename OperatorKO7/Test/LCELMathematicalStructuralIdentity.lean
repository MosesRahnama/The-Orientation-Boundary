import OperatorKO7.Meta.LCELMathematicalStructuralIdentity

namespace LCELMathematicalStructuralIdentityReach

open OperatorKO7
open OperatorKO7.LCELMathematicalStructuralIdentity

/-! Reachability smoke test for the strong restricted structural-identity
theorem (Workstream D). -/

example : True := by
  have := godel_dp_mathematical_universal_quasiFunctor
  trivial

example : True := by
  have := godel_dp_mathematical_universal_structural_identity
  trivial

example : True := by
  have := godel_benchmark_mathematical_universal_quasiFunctor
  trivial

example : True := by
  have := godel_benchmark_mathematical_universal_structural_identity
  trivial

example : True := by
  have :=
    lcel_structural_identity_of_mathematicalComparison
      (A₁ := OperatorKO7.LCELUniversalTheorem.godel1931AdmissibleLCELInstance)
      (A₂ := OperatorKO7.LCELUniversalTheorem.dpEmitterAdmissibleLCELInstance)
      OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    lcel_universal_structural_identity_of_mathematicalComparison_via_earlier
      (A₁ := OperatorKO7.LCELUniversalTheorem.godel1931AdmissibleLCELInstance)
      (A₂ := OperatorKO7.LCELUniversalTheorem.dpEmitterAdmissibleLCELInstance)
      OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness
  trivial

example : True := by
  have :=
    lcelUniversalQuasiFunctor_ofMathematicalComparison_viaSupportDowngrade
      (A₁ := OperatorKO7.LCELUniversalTheorem.godel1931AdmissibleLCELInstance)
      (A₂ := OperatorKO7.LCELUniversalTheorem.dpEmitterAdmissibleLCELInstance)
      OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness
  trivial

/-! Nontrivial mathematical regression tests for the Workstream D
transport coherence lemmas. Each example asserts a named equation that
fails if the transport coherence is lost; these are not reachability
tests. -/

example :
    (OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness.transportBase
        OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness.sourceBaseTheorem).unprovedSentence
      = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.boundaryObject.boundarySentence
          OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.boundaryObject.designated :=
  transportBase_unprovedSentence_eq_targetDesignatedBoundary
    OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness

example :
    (OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness.transportLicense
        OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness.sourceLicenseTheorem).blockedSentence
      = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.comparison.reflectionContent.blockedSentence :=
  transportLicense_blockedSentence_eq_targetReflectionBlocked
    OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness

example :
    (OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness.transportReimport
        OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness.sourceReimportTheorem).importedSentence
      = OperatorKO7.LCELDpInstance.dpEmitterLCELInstance.comparison.reimportContent.importedSentence :=
  transportReimport_importedSentence_eq_targetReimportImported
    OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness

example :
    OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness.transportBoundary
        OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness.sourceBoundaryTheorem
      = OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness.targetBoundaryTheorem :=
  transportBoundary_canonical
    OperatorKO7.LCELMathematical.godel_dp_lcelMathematicalSupportWitness

end LCELMathematicalStructuralIdentityReach
