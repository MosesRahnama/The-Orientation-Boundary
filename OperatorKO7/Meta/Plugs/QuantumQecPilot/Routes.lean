/-!
# QuantumQecPilot route catalog

Two closed Lean inductive types declare five `W_1` route labels and three
`W_2` route labels. The lists below enumerate those constructors. Their
theorems establish list length, absence of duplicates, and exhaustive
membership relative to the corresponding inductive type. This file does not
check parity with an external plug or establish the physical properties named
by the route labels.
-/

namespace OperatorKO7.Meta.Plugs.QuantumQecPilot

/-- Five declared `W_1` route labels. -/
inductive QuantumQecPilotW1Route
  | SurfaceCodeMinimumWeightPerfectMatching
  | ColorCodeRestrictionLatticeDecoder
  | RepetitionCodeMajorityVote
  | BaconShorSubsystemDecoder
  | ConcatenatedCssThresholdLicensed
  deriving DecidableEq, Repr

/-- Three declared `W_2` route labels. -/
inductive QuantumQecPilotW2Route
  | PostSelectionOnSyndromeHistoryEscape
  | MagicStateDistillationEscape
  | PilotOnlyStage2RecordEmissionEscape
  deriving DecidableEq, Repr

/-- List containing every constructor of `QuantumQecPilotW1Route`. -/
def quantumQecPilotW1Routes : List QuantumQecPilotW1Route :=
  [ .SurfaceCodeMinimumWeightPerfectMatching
  , .ColorCodeRestrictionLatticeDecoder
  , .RepetitionCodeMajorityVote
  , .BaconShorSubsystemDecoder
  , .ConcatenatedCssThresholdLicensed
  ]

/-- List containing every constructor of `QuantumQecPilotW2Route`. -/
def quantumQecPilotW2Routes : List QuantumQecPilotW2Route :=
  [ .PostSelectionOnSyndromeHistoryEscape
  , .MagicStateDistillationEscape
  , .PilotOnlyStage2RecordEmissionEscape
  ]

theorem quantumQecPilotW1Routes_length :
    quantumQecPilotW1Routes.length = 5 := by decide

theorem quantumQecPilotW2Routes_length :
    quantumQecPilotW2Routes.length = 3 := by decide

theorem quantumQecPilotW1Routes_nodup :
    quantumQecPilotW1Routes.Nodup := by decide

theorem quantumQecPilotW2Routes_nodup :
    quantumQecPilotW2Routes.Nodup := by decide

theorem quantumQecPilotW1Routes_complete_exact (r : QuantumQecPilotW1Route) :
    r ∈ quantumQecPilotW1Routes ↔
      r = .SurfaceCodeMinimumWeightPerfectMatching ∨
      r = .ColorCodeRestrictionLatticeDecoder ∨
      r = .RepetitionCodeMajorityVote ∨
      r = .BaconShorSubsystemDecoder ∨
      r = .ConcatenatedCssThresholdLicensed := by
  cases r <;> decide

theorem quantumQecPilotW2Routes_complete_exact (r : QuantumQecPilotW2Route) :
    r ∈ quantumQecPilotW2Routes ↔
      r = .PostSelectionOnSyndromeHistoryEscape ∨
      r = .MagicStateDistillationEscape ∨
      r = .PilotOnlyStage2RecordEmissionEscape := by
  cases r <;> decide

end OperatorKO7.Meta.Plugs.QuantumQecPilot
