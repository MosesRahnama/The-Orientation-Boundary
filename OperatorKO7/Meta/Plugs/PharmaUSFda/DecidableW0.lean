import OperatorKO7.Meta.Plugs.PharmaUSFda.Routes
import OperatorKO7.Meta.Universal.ClassifyUniversal

/-!
# PharmaUSFda decidable W0 classifier

This module defines eight labeled cases, assigns each case a one-row finite
information matrix, and compares the universal classifier with explicitly
stated results. The finite carrier is a declared example surface; the file does
not establish that it exhausts FDA evidence pathways or their legal meaning.
-/

namespace OperatorKO7.Meta.Universal.ClassifyUniversal

deriving instance DecidableEq for FiniteInformationMatrix
deriving instance DecidableEq for RowWitness
deriving instance DecidableEq for ClassificationResult

end OperatorKO7.Meta.Universal.ClassifyUniversal

namespace OperatorKO7.Meta.Plugs.PharmaUSFda.DecidableW0

open OperatorKO7.Meta.Plugs.PharmaUSFda
open OperatorKO7.Meta.Universal.ClassifyUniversal

/-- Eight labels used by this finite W0 classifier instance. -/
inductive PharmaUSFdaW0Carrier
  | TraditionalNdaSubstantialEvidenceCase
  | AcceleratedApprovalSurrogateCase
  | BreakthroughTherapyExpeditedCase
  | ExpandedAccessIndividualPatientCase
  | RightToTryEligibleInvestigationalDrugCase
  | AdvisoryCommitteeRecommendationEscapeCase
  | OffLabelDiscretionUnderFdcaSection1006Case
  | AndaSuitabilityPetitionWithCitizenPetitionCase
  deriving DecidableEq, Repr

/-- The per-plug W0 carrier is finite and constructor-discrete. -/
instance : DecidableEq PharmaUSFdaW0Carrier := inferInstance

/-- One-row finite-information matrices assigned to the eight carrier values.
The strings are data tokens; no legal interpretation of them is proved here. -/
def pharmaUSFdaW0Matrix : PharmaUSFdaW0Carrier → FiniteInformationMatrix
  | .TraditionalNdaSubstantialEvidenceCase =>
      { rows := [("fda_traditional_nda", ["21_USC_355_b"])] }
  | .AcceleratedApprovalSurrogateCase =>
      { rows := [("fda_accelerated_approval", ["21_CFR_314_500_subpart_H"])] }
  | .BreakthroughTherapyExpeditedCase =>
      { rows := [("fda_breakthrough_therapy", ["21_USC_356_a"])] }
  | .ExpandedAccessIndividualPatientCase =>
      { rows := [("fda_expanded_access", ["21_USC_360bbb_0a"])] }
  | .RightToTryEligibleInvestigationalDrugCase =>
      { rows := [("fda_right_to_try", ["21_USC_360bbb_0a_note_PL_115_176"])] }
  | .AdvisoryCommitteeRecommendationEscapeCase =>
      { rows :=
          [("fda_advisory_committee_escape",
            ["21_USC_355_b", "advisory_committee_recommendation"])] }
  | .OffLabelDiscretionUnderFdcaSection1006Case =>
      { rows :=
          [("fda_off_label_escape",
            ["FDCA_1006", "off_label_clinical_discretion"])] }
  | .AndaSuitabilityPetitionWithCitizenPetitionCase =>
      { rows :=
          [("fda_anda_suitability_escape",
            ["21_CFR_314_93", "citizen_petition_overlay"])] }

/-- The per-plug W0 classifier specializes the universal finite-information
matrix scan to the PharmaUSFda carrier. -/
def pharmaUSFdaW0Classifier (c : PharmaUSFdaW0Carrier) : ClassificationResult :=
  classifyUniversal (pharmaUSFdaW0Matrix c)

/-- Expected concrete classification result for each of the eight evidence
framework cases. This is stated without invoking the classifier itself. -/
def pharmaUSFdaExpectedW0Result : PharmaUSFdaW0Carrier → ClassificationResult
  | .TraditionalNdaSubstantialEvidenceCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "fda_traditional_nda"
             rules := ["21_USC_355_b"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .AcceleratedApprovalSurrogateCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "fda_accelerated_approval"
             rules := ["21_CFR_314_500_subpart_H"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .BreakthroughTherapyExpeditedCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "fda_breakthrough_therapy"
             rules := ["21_USC_356_a"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .ExpandedAccessIndividualPatientCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "fda_expanded_access"
             rules := ["21_USC_360bbb_0a"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .RightToTryEligibleInvestigationalDrugCase =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "fda_right_to_try"
             rules := ["21_USC_360bbb_0a_note_PL_115_176"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .AdvisoryCommitteeRecommendationEscapeCase =>
      { worstClass := CardinalityClass.ambiguityDuplication
        rowWitnesses :=
          [{ fact := "fda_advisory_committee_escape"
             rules := ["21_USC_355_b", "advisory_committee_recommendation"]
             cls := CardinalityClass.ambiguityDuplication }]
        blocked := true }
  | .OffLabelDiscretionUnderFdcaSection1006Case =>
      { worstClass := CardinalityClass.ambiguityDuplication
        rowWitnesses :=
          [{ fact := "fda_off_label_escape"
             rules := ["FDCA_1006", "off_label_clinical_discretion"]
             cls := CardinalityClass.ambiguityDuplication }]
        blocked := true }
  | .AndaSuitabilityPetitionWithCitizenPetitionCase =>
      { worstClass := CardinalityClass.ambiguityDuplication
        rowWitnesses :=
          [{ fact := "fda_anda_suitability_escape"
             rules := ["21_CFR_314_93", "citizen_petition_overlay"]
             cls := CardinalityClass.ambiguityDuplication }]
        blocked := true }

/-- Decidability of the per-plug W0 classifier against its concrete expected
classification result, derived from carrier-level finite equality. -/
instance pharmaUSFdaW0Decidable :
    (c : PharmaUSFdaW0Carrier) →
      Decidable (pharmaUSFdaW0Classifier c = pharmaUSFdaExpectedW0Result c)
  | _ => inferInstance

/-- The classifier agrees with the explicit comparison result on all eight
constructors of `PharmaUSFdaW0Carrier`. -/
theorem pharmaEvidenceEightCases :
    pharmaUSFdaW0Classifier .TraditionalNdaSubstantialEvidenceCase =
      pharmaUSFdaExpectedW0Result .TraditionalNdaSubstantialEvidenceCase ∧
    pharmaUSFdaW0Classifier .AcceleratedApprovalSurrogateCase =
      pharmaUSFdaExpectedW0Result .AcceleratedApprovalSurrogateCase ∧
    pharmaUSFdaW0Classifier .BreakthroughTherapyExpeditedCase =
      pharmaUSFdaExpectedW0Result .BreakthroughTherapyExpeditedCase ∧
    pharmaUSFdaW0Classifier .ExpandedAccessIndividualPatientCase =
      pharmaUSFdaExpectedW0Result .ExpandedAccessIndividualPatientCase ∧
    pharmaUSFdaW0Classifier .RightToTryEligibleInvestigationalDrugCase =
      pharmaUSFdaExpectedW0Result .RightToTryEligibleInvestigationalDrugCase ∧
    pharmaUSFdaW0Classifier .AdvisoryCommitteeRecommendationEscapeCase =
      pharmaUSFdaExpectedW0Result .AdvisoryCommitteeRecommendationEscapeCase ∧
    pharmaUSFdaW0Classifier .OffLabelDiscretionUnderFdcaSection1006Case =
      pharmaUSFdaExpectedW0Result .OffLabelDiscretionUnderFdcaSection1006Case ∧
    pharmaUSFdaW0Classifier .AndaSuitabilityPetitionWithCitizenPetitionCase =
      pharmaUSFdaExpectedW0Result .AndaSuitabilityPetitionWithCitizenPetitionCase := by
  decide

/-- Excluded-middle decidability and pointwise agreement of the classifier with
the explicit comparison result on `PharmaUSFdaW0Carrier`. -/
theorem pharmaEvidenceDecidableW0 :
    (∀ c : PharmaUSFdaW0Carrier,
      (pharmaUSFdaW0Classifier c = pharmaUSFdaExpectedW0Result c) ∨
        ¬ (pharmaUSFdaW0Classifier c = pharmaUSFdaExpectedW0Result c)) ∧
    (∀ c : PharmaUSFdaW0Carrier,
      pharmaUSFdaW0Classifier c = pharmaUSFdaExpectedW0Result c) := by
  refine ⟨?_, ?_⟩
  · intro c
    exact Or.inl (by cases c <;> decide)
  intro c
  cases c <;> decide

def pharma_evidence_decidable_w0_anchor : String :=
  "OperatorKO7.Meta.Plugs.PharmaUSFda.DecidableW0.pharmaEvidenceDecidableW0"

def pharma_evidence_eight_cases_anchor : String :=
  "OperatorKO7.Meta.Plugs.PharmaUSFda.DecidableW0.pharmaEvidenceEightCases"

end OperatorKO7.Meta.Plugs.PharmaUSFda.DecidableW0
