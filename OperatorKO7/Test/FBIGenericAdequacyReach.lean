import OperatorKO7.Meta.FBI_GenericAdequacy
import OperatorKO7.Meta.FBI_AdequacyBoundary

namespace FBIGenericAdequacyReach

open OperatorKO7
open OperatorKO7.FBIGenericAdequacy
open OperatorKO7.FBIAdequacyBoundary

#check FBIAdmissibleComparisonWitness
#check fbi_admissible_comparison_witness
#check FBIGenericForwardAdequacyClass
#check FBIGenericBackwardAdequacyClass
#check fbi_no_outside_catalog_method
#check fbi_generic_forward_adequacy_universal_unconditional
#check fbi_generic_backward_adequacy_universal_unconditional
#check fbi_generic_adequacy_universal_unconditional
#check OperatorKO7.FBIAdequacyBoundary.fbi_no_outside_catalog_method
#check OperatorKO7.FBIAdequacyBoundary.fbi_generic_forward_adequacy_universal_unconditional
#check OperatorKO7.FBIAdequacyBoundary.fbi_generic_backward_adequacy_universal_unconditional
#check OperatorKO7.FBIAdequacyBoundary.fbi_generic_adequacy_universal_unconditional

example : FBIAdmissibleComparisonWitness directForwardFBIMethod.comparisonWitness := by
  exact fbi_admissible_comparison_witness _

example : OperatorKO7.FBIGenericAdequacy.FBIGenericForwardAdequacyClass directForwardFBIMethod := by
  exact ⟨rfl, fbi_admissible_comparison_witness _⟩

example : OperatorKO7.FBIGenericAdequacy.FBIGenericBackwardAdequacyClass importedWholeFBIMethod := by
  exact ⟨rfl, fbi_admissible_comparison_witness _⟩

example : OperatorKO7.FBIGenericAdequacy.FBIFinalCoverage directForwardFBIMethod := by
  exact (OperatorKO7.FBIGenericAdequacy.fbi_forward_directional_coverage
    directForwardFBIMethod rfl).2.2

example : OperatorKO7.FBIGenericAdequacy.FBIFinalCoverage importedWholeFBIMethod := by
  exact (OperatorKO7.FBIGenericAdequacy.fbi_backward_directional_coverage
    importedWholeFBIMethod rfl).2.2

example : directForwardFBIMethod.successSemantics.closureStatus ∈ OperatorKO7.FBIClassification.fbiClosureStatuses := by
  exact (OperatorKO7.FBIGenericAdequacy.fbi_no_outside_catalog_method directForwardFBIMethod).1

example : OperatorKO7.FBIAdequacyBoundary.FBIFinalCoverage directForwardFBIMethod := by
  exact (OperatorKO7.FBIGenericAdequacy.fbi_directional_coverage
    .forward directForwardFBIMethod
      (by
        simp [directForwardFBIMethod, FBIMethod.matchesDirection,
          FBIInstantiation.matchesDirection, FBIInstantiation.directions])).2

example : OperatorKO7.FBIAdequacyBoundary.FBIFinalCoverage transformedCallFBIMethod := by
  exact (OperatorKO7.FBIGenericAdequacy.fbi_directional_coverage
    .backward transformedCallFBIMethod
      (by
        simp [transformedCallFBIMethod, FBIMethod.matchesDirection,
          FBIInstantiation.matchesDirection, FBIInstantiation.directions])).2

/-! ## Direction-indexed coverage: new public anchors (WP-3 item A) -/

#check fbi_forward_directional_coverage
#check fbi_backward_directional_coverage
#check fbi_directional_coverage
#check fbi_directional_row_classified

#print axioms fbi_forward_directional_coverage
#print axioms fbi_backward_directional_coverage
#print axioms fbi_directional_coverage
#print axioms fbi_directional_row_classified

/-- The direction-indexed forward theorem consumes its premise on the direct fixture. -/
example :
    (OperatorKO7.FBIClassification.fbiDirectionalRow directForwardFBIMethod).1 =
        FBIInstantiation.forwardOnly ∧
      FBIDirection.forward ∈
        (OperatorKO7.FBIClassification.fbiDirectionalRow directForwardFBIMethod).1.directions ∧
      OperatorKO7.FBIGenericAdequacy.FBIFinalCoverage directForwardFBIMethod :=
  fbi_forward_directional_coverage directForwardFBIMethod rfl

end FBIGenericAdequacyReach

/-! ## LASOT 18.2 reach/axiom parity completion (supervisor validation 2026-08-10):
every checked anchor above now carries a paired axiom print; opens replicated for print-scope resolution. -/

section LasotParityCompletion
open FBIGenericAdequacyReach
open OperatorKO7
open OperatorKO7.FBIGenericAdequacy
open OperatorKO7.FBIAdequacyBoundary

#print axioms fbi_admissible_comparison_witness
#print axioms fbi_generic_adequacy_universal_unconditional
#print axioms fbi_generic_backward_adequacy_universal_unconditional
#print axioms fbi_generic_forward_adequacy_universal_unconditional
#print axioms fbi_no_outside_catalog_method
#print axioms FBIAdmissibleComparisonWitness
#print axioms FBIGenericBackwardAdequacyClass
#print axioms FBIGenericForwardAdequacyClass
#print axioms OperatorKO7.FBIAdequacyBoundary.fbi_generic_adequacy_universal_unconditional
#print axioms OperatorKO7.FBIAdequacyBoundary.fbi_generic_backward_adequacy_universal_unconditional
#print axioms OperatorKO7.FBIAdequacyBoundary.fbi_generic_forward_adequacy_universal_unconditional
#print axioms OperatorKO7.FBIAdequacyBoundary.fbi_no_outside_catalog_method
end LasotParityCompletion
