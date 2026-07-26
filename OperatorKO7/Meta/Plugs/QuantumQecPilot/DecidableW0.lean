import OperatorKO7.Meta.Plugs.QuantumQecPilot.Routes
import OperatorKO7.Meta.Universal.ClassifyUniversal

/-!
# QuantumQecPilot decidable W0 classifier

Finite string-matrix fixture for four QuantumQecPilot method labels. The
carrier is finite and constructor-discrete, so equality with each assigned
classification is decidable by case analysis.

The four fixture labels are:

1. Abstention-Aware Decoder
2. Wald-SPRT Adaptive Syndrome
3. Offset-Conservation Leakage Detector
4. Sym_n Gauged Stabilizer
-/

namespace OperatorKO7.Meta.Plugs.QuantumQecPilot.DecidableW0

open OperatorKO7.Meta.Plugs.QuantumQecPilot
open OperatorKO7.Meta.Universal.ClassifyUniversal

/-- Four method labels used by the finite W0 fixture. -/
inductive QuantumQecPilotW0Carrier
  | AbstentionAwareDecoder
  | WaldSPRTAdaptiveSyndrome
  | OffsetConservationLeakageDetector
  | SymNGaugedStabilizer
  deriving DecidableEq, Repr

/-- The per-plug W0 carrier is finite and constructor-discrete. -/
instance : DecidableEq QuantumQecPilotW0Carrier := inferInstance

/-- Canonical finite support for the four QuantumQecPilot method routes. -/
def quantumQecPilotFourMethodRouteSupport : List QuantumQecPilotW0Carrier :=
  [ .AbstentionAwareDecoder
  , .WaldSPRTAdaptiveSyndrome
  , .OffsetConservationLeakageDetector
  , .SymNGaugedStabilizer
  ]

/-- Membership characterization for the four fixture labels. -/
theorem quantumQecPilotFourMethodRoutes :
    quantumQecPilotFourMethodRouteSupport.length = 4 ∧
    quantumQecPilotFourMethodRouteSupport.Nodup ∧
    (∀ route : QuantumQecPilotW0Carrier,
      route ∈ quantumQecPilotFourMethodRouteSupport ↔
        route = .AbstentionAwareDecoder ∨
        route = .WaldSPRTAdaptiveSyndrome ∨
        route = .OffsetConservationLeakageDetector ∨
        route = .SymNGaugedStabilizer) := by
  refine ⟨rfl, by decide, ?_⟩
  intro route
  cases route <;> decide

/-- Manually authored finite-information matrices keyed by the four method
labels. The row strings and cardinalities are fixture data; adapters from the
corresponding QEC theorems require separate declarations. -/
def quantumQecPilotW0Matrix : QuantumQecPilotW0Carrier → FiniteInformationMatrix
  | .AbstentionAwareDecoder =>
      { rows := [("QEC_AbstentionAwareDecoder", [])] }
  | .WaldSPRTAdaptiveSyndrome =>
      { rows :=
          [("QEC_WaldSPRT_AdaptiveSyndrome",
            ["wald_sprt_round_expectation"])] }
  | .OffsetConservationLeakageDetector =>
      { rows :=
          [("QEC_OffsetConservation_LeakageDetector",
            ["offset_conservation_invariant", "leakage_detector_invariant"])] }
  | .SymNGaugedStabilizer =>
      { rows :=
          [("QEC_SymN_GaugedStabilizer",
            ["sym_n_gauge_invariance", "gauged_stabilizer_license"])] }

/-- The per-plug W0 classifier specializes the universal finite-information
matrix scan to the QuantumQecPilot four-method carrier. -/
def quantumQecPilotW0Classifier : QuantumQecPilotW0Carrier → ClassificationResult
  | c => classifyUniversal (quantumQecPilotW0Matrix c)

/-- Assigned classification result for each of the four fixture labels. -/
def quantumQecPilotExpectedW0Result :
    QuantumQecPilotW0Carrier → ClassificationResult
  | .AbstentionAwareDecoder =>
      { worstClass := CardinalityClass.noMapping
        rowWitnesses :=
          [{ fact := "QEC_AbstentionAwareDecoder"
             rules := []
             cls := CardinalityClass.noMapping }]
        blocked := true }
  | .WaldSPRTAdaptiveSyndrome =>
      { worstClass := CardinalityClass.plainTextApplication
        rowWitnesses :=
          [{ fact := "QEC_WaldSPRT_AdaptiveSyndrome"
             rules := ["wald_sprt_round_expectation"]
             cls := CardinalityClass.plainTextApplication }]
        blocked := false }
  | .OffsetConservationLeakageDetector =>
      { worstClass := CardinalityClass.ambiguityDuplication
        rowWitnesses :=
          [{ fact := "QEC_OffsetConservation_LeakageDetector"
             rules := ["offset_conservation_invariant", "leakage_detector_invariant"]
             cls := CardinalityClass.ambiguityDuplication }]
        blocked := true }
  | .SymNGaugedStabilizer =>
      { worstClass := CardinalityClass.ambiguityDuplication
        rowWitnesses :=
          [{ fact := "QEC_SymN_GaugedStabilizer"
             rules := ["sym_n_gauge_invariance", "gauged_stabilizer_license"]
             cls := CardinalityClass.ambiguityDuplication }]
        blocked := true }

/-- Decidability of the per-plug W0 classifier against its concrete expected
classification result, derived by finite carrier case analysis. -/
instance quantumQecPilotW0Decidable :
    (c : QuantumQecPilotW0Carrier) →
      Decidable (quantumQecPilotW0Classifier c = quantumQecPilotExpectedW0Result c)
  | .AbstentionAwareDecoder => isTrue rfl
  | .WaldSPRTAdaptiveSyndrome => isTrue rfl
  | .OffsetConservationLeakageDetector => isTrue rfl
  | .SymNGaugedStabilizer => isTrue rfl

/-- Casewise equality between the classifier computation and the assigned
result on the four-label fixture. -/
theorem quantumQecPilotFourMethodCases :
    quantumQecPilotW0Classifier .AbstentionAwareDecoder =
      quantumQecPilotExpectedW0Result .AbstentionAwareDecoder ∧
    quantumQecPilotW0Classifier .WaldSPRTAdaptiveSyndrome =
      quantumQecPilotExpectedW0Result .WaldSPRTAdaptiveSyndrome ∧
    quantumQecPilotW0Classifier .OffsetConservationLeakageDetector =
      quantumQecPilotExpectedW0Result .OffsetConservationLeakageDetector ∧
    quantumQecPilotW0Classifier .SymNGaugedStabilizer =
      quantumQecPilotExpectedW0Result .SymNGaugedStabilizer := by
  decide

/-- Package decidability and casewise classification equality for the finite
four-label fixture. -/
theorem quantumQecPilotDecidableW0 :
    (∀ c : QuantumQecPilotW0Carrier,
      ∃ _ : Decidable (quantumQecPilotW0Classifier c = quantumQecPilotExpectedW0Result c), True) ∧
    (∀ c : QuantumQecPilotW0Carrier,
      quantumQecPilotW0Classifier c = quantumQecPilotExpectedW0Result c) := by
  constructor
  · intro c
    exact ⟨quantumQecPilotW0Decidable c, trivial⟩
  · intro c
    cases c <;> rfl

/-- String reference to the finite-fixture decidability theorem. -/
def quantum_qec_pilot_decidable_w0_anchor : String :=
  "OperatorKO7.Meta.Plugs.QuantumQecPilot.DecidableW0.quantumQecPilotDecidableW0"

/-- String reference to the finite-fixture classification theorem. -/
def quantum_qec_pilot_four_method_routes_anchor : String :=
  "OperatorKO7.Meta.Plugs.QuantumQecPilot.DecidableW0.quantumQecPilotFourMethodRoutes"

end OperatorKO7.Meta.Plugs.QuantumQecPilot.DecidableW0
