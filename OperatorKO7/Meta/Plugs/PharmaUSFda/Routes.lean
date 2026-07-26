/-!
This module defines two local finite enums and proves their list lengths, distinctness, and
constructor membership. Correspondence with an external catalog or regulatory pathway requires a
separate generated check.





-/

namespace OperatorKO7.Meta.Plugs.PharmaUSFda

/-- Carrier with the constructors displayed below.
-/
inductive PharmaUSFdaW1Route
  | TraditionalNdaSubstantialEvidence
  | AcceleratedApprovalSurrogate
  | BreakthroughTherapyExpedited
  | ExpandedAccessIndividualPatient
  | RightToTryEligibleInvestigationalDrug
  deriving DecidableEq, Repr

/-- Carrier with the constructors displayed below.
-/
inductive PharmaUSFdaW2Route
  | AdvisoryCommitteeRecommendationEscape
  | OffLabelDiscretionUnderFdcaSection1006
  | AndaSuitabilityPetitionWithCitizenPetition
  deriving DecidableEq, Repr

/-- Definition with formal content given by the displayed type and body. -/
def pharmaUSFdaW1Routes : List PharmaUSFdaW1Route :=
  [ .TraditionalNdaSubstantialEvidence
  , .AcceleratedApprovalSurrogate
  , .BreakthroughTherapyExpedited
  , .ExpandedAccessIndividualPatient
  , .RightToTryEligibleInvestigationalDrug
  ]

/-- Definition with formal content given by the displayed type and body. -/
def pharmaUSFdaW2Routes : List PharmaUSFdaW2Route :=
  [ .AdvisoryCommitteeRecommendationEscape
  , .OffLabelDiscretionUnderFdcaSection1006
  , .AndaSuitabilityPetitionWithCitizenPetition
  ]

theorem pharmaUSFdaW1Routes_length :
    pharmaUSFdaW1Routes.length = 5 := by decide

theorem pharmaUSFdaW2Routes_length :
    pharmaUSFdaW2Routes.length = 3 := by decide

theorem pharmaUSFdaW1Routes_nodup :
    pharmaUSFdaW1Routes.Nodup := by decide

theorem pharmaUSFdaW2Routes_nodup :
    pharmaUSFdaW2Routes.Nodup := by decide

theorem pharmaUSFdaW1Routes_complete_exact (r : PharmaUSFdaW1Route) :
    r ∈ pharmaUSFdaW1Routes ↔
      r = .TraditionalNdaSubstantialEvidence ∨
      r = .AcceleratedApprovalSurrogate ∨
      r = .BreakthroughTherapyExpedited ∨
      r = .ExpandedAccessIndividualPatient ∨
      r = .RightToTryEligibleInvestigationalDrug := by
  cases r <;> decide

theorem pharmaUSFdaW2Routes_complete_exact (r : PharmaUSFdaW2Route) :
    r ∈ pharmaUSFdaW2Routes ↔
      r = .AdvisoryCommitteeRecommendationEscape ∨
      r = .OffLabelDiscretionUnderFdcaSection1006 ∨
      r = .AndaSuitabilityPetitionWithCitizenPetition := by
  cases r <;> decide

end OperatorKO7.Meta.Plugs.PharmaUSFda
