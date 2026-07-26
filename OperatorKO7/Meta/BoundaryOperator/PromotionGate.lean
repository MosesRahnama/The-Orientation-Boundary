import OperatorKO7.Meta.BoundaryOperator.TransportCard

/-!
# Claim-language promotion matrix

`permittedStrengths` gives the transport-strength constructors admitted for each claim-language
constructor. `StrengthSufficient` is list membership in that matrix, and
`claimLanguagePermitted` is its Boolean decision procedure. Isomorphism language admits the
`arsIsomorphism` strength. These declarations classify supplied strength labels; transport evidence
is carried separately by transport cards.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryOperator

inductive ClaimLanguage
  | sameShape
  | forwardStepTransport
  | forwardReachTransport
  | galoisConnection
  | stepLifting
  | bisimulationOnImage
  | reductionEquivalence
  | isomorphism
  deriving DecidableEq, Repr

def permittedStrengths : ClaimLanguage -> List TransportStrength
  | .sameShape =>
      [ .commonCarrier, .forwardStepSimulation, .forwardReachSimulation,
        .galoisConnection, .stepLifting, .bisimulationOnImage,
        .reductionEquivalence, .arsIsomorphism ]
  | .forwardStepTransport =>
      [ .forwardStepSimulation, .stepLifting, .bisimulationOnImage,
        .arsIsomorphism ]
  | .forwardReachTransport =>
      [ .forwardStepSimulation, .forwardReachSimulation, .stepLifting,
        .bisimulationOnImage, .reductionEquivalence, .arsIsomorphism ]
  | .galoisConnection => [ .galoisConnection, .arsIsomorphism ]
  | .stepLifting => [ .stepLifting, .bisimulationOnImage, .arsIsomorphism ]
  | .bisimulationOnImage => [ .bisimulationOnImage, .arsIsomorphism ]
  | .reductionEquivalence => [ .reductionEquivalence, .arsIsomorphism ]
  | .isomorphism => [ .arsIsomorphism ]

def StrengthSufficient (strength : TransportStrength)
    (language : ClaimLanguage) : Prop :=
  strength ∈ permittedStrengths language

instance strengthSufficient_decidable
    (strength : TransportStrength) (language : ClaimLanguage) :
    Decidable (StrengthSufficient strength language) := by
  unfold StrengthSufficient
  infer_instance

def claimLanguagePermitted (strength : TransportStrength)
    (language : ClaimLanguage) : Bool :=
  decide (StrengthSufficient strength language)

theorem claim_language_permitted_iff_strength_sufficient
    (strength : TransportStrength) (language : ClaimLanguage) :
    claimLanguagePermitted strength language = true ↔
      StrengthSufficient strength language := by
  simp [claimLanguagePermitted]

theorem isomorphism_language_permitted_iff
    (strength : TransportStrength) :
    StrengthSufficient strength .isomorphism ↔
      strength = .arsIsomorphism := by
  cases strength <;> simp [StrengthSufficient, permittedStrengths]

theorem common_carrier_forbids_forward_transport :
    ¬ StrengthSufficient .commonCarrier .forwardStepTransport := by
  simp [StrengthSufficient, permittedStrengths]

theorem common_carrier_same_shape_fixture :
    claimLanguagePermitted .commonCarrier .sameShape = true := by
  decide

#check claim_language_permitted_iff_strength_sufficient
#check isomorphism_language_permitted_iff
#check common_carrier_forbids_forward_transport
#check common_carrier_same_shape_fixture
#print axioms claim_language_permitted_iff_strength_sufficient
#print axioms isomorphism_language_permitted_iff
#print axioms common_carrier_forbids_forward_transport
#print axioms common_carrier_same_shape_fixture

end OperatorKO7.Meta.BoundaryOperator
