import Mathlib
import OperatorKO7.Meta.Plugs.QuantumQecPilot.Routes

/-!
# QuantumQecPilot finite W₁ route correspondence

This module defines a five-constructor obligation type and a total map to the
five W₁ routes imported from `Routes`. It proves catalog membership and that
the declared map is bijective. These results concern the finite Lean types in
this file; they do not establish coverage of all QEC obligations or parity with
an external implementation.
-/

namespace OperatorKO7.Meta.Plugs.QuantumQecPilot

open OperatorKO7.Meta.Plugs.QuantumQecPilot

/-- Five obligation labels used by the finite route correspondence. -/
inductive QuantumQecPilotObligation
  | QecSurfaceCode
  | QecColorCode
  | QecRepetitionCode
  | QecBaconShorCode
  | QecConcatenatedCss
  deriving DecidableEq, Repr

/-- The plug-level exact route carrier for `quantumQecPilot`. -/
abbrev QuantumQecPilotRoute := QuantumQecPilotW1Route

/-- Singleton token for the registered `quantumQecPilot` plug. -/
def QuantumQecPilotPlug : PUnit := PUnit.unit

/-- Total map from the five declared obligation labels to W₁ routes. -/
def quantumQecPilotClassifyW1 : QuantumQecPilotObligation → QuantumQecPilotW1Route
  | .QecSurfaceCode     => .SurfaceCodeMinimumWeightPerfectMatching
  | .QecColorCode       => .ColorCodeRestrictionLatticeDecoder
  | .QecRepetitionCode  => .RepetitionCodeMajorityVote
  | .QecBaconShorCode   => .BaconShorSubsystemDecoder
  | .QecConcatenatedCss => .ConcatenatedCssThresholdLicensed

/-- Classifier surface obtained from `quantumQecPilotClassifyW1`. -/
def plugClassifies (_ : PUnit) : QuantumQecPilotObligation → QuantumQecPilotRoute :=
  quantumQecPilotClassifyW1

/-! ## Catalog membership -/

theorem quantumQecPilotClassifyW1_in_catalog :
    ∀ ob : QuantumQecPilotObligation,
      quantumQecPilotClassifyW1 ob ∈ quantumQecPilotW1Routes := by
  intro ob
  cases ob <;> decide

theorem plugClassifies_in_catalog :
    ∀ ob : QuantumQecPilotObligation,
      plugClassifies QuantumQecPilotPlug ob ∈ quantumQecPilotW1Routes := by
  intro ob
  exact quantumQecPilotClassifyW1_in_catalog ob

/-! ## Functional uniqueness -/

/-- A total function has a unique value at each input. Catalog membership of
that value is proved separately by `quantumQecPilotClassifyW1_in_catalog`. -/
theorem quantumQecPilotRoutesExact :
    ∀ obligation : QuantumQecPilotObligation,
      ∃! route : QuantumQecPilotRoute,
        plugClassifies QuantumQecPilotPlug obligation = route := by
  intro obligation
  exact ⟨plugClassifies QuantumQecPilotPlug obligation, rfl, fun _ h => h.symm⟩

/-! ## Bijectivity corollaries -/

theorem quantumQecPilotClassifyW1_injective :
    Function.Injective quantumQecPilotClassifyW1 := by
  intro a b h; cases a <;> cases b <;> simp_all [quantumQecPilotClassifyW1]

theorem quantumQecPilotClassifyW1_surjective :
    Function.Surjective quantumQecPilotClassifyW1 := by
  intro r; cases r
  all_goals first
    | exact ⟨.QecSurfaceCode, rfl⟩
    | exact ⟨.QecColorCode, rfl⟩
    | exact ⟨.QecRepetitionCode, rfl⟩
    | exact ⟨.QecBaconShorCode, rfl⟩
    | exact ⟨.QecConcatenatedCss, rfl⟩

theorem quantumQecPilotClassifyW1_bijective :
    Function.Bijective quantumQecPilotClassifyW1 :=
  ⟨quantumQecPilotClassifyW1_injective, quantumQecPilotClassifyW1_surjective⟩

/-! ## Catalog completeness corollaries -/

theorem quantumQecPilotW1Routes_fully_classified :
    ∀ r : QuantumQecPilotW1Route,
      ∃ ob : QuantumQecPilotObligation,
        quantumQecPilotClassifyW1 ob = r :=
  quantumQecPilotClassifyW1_surjective

theorem quantumQecPilotW1Routes_catalog_exact :
    quantumQecPilotW1Routes.length = 5
    ∧ ∀ r : QuantumQecPilotW1Route,
        r ∈ quantumQecPilotW1Routes ↔
          r = .SurfaceCodeMinimumWeightPerfectMatching ∨
          r = .ColorCodeRestrictionLatticeDecoder ∨
          r = .RepetitionCodeMajorityVote ∨
          r = .BaconShorSubsystemDecoder ∨
          r = .ConcatenatedCssThresholdLicensed := by
  constructor
  · decide
  · intro r; cases r <;> decide

/-! ## Declaration-name anchor -/

/-- Stable declaration-name string for `quantumQecPilotRoutesExact`. -/
def quantumQecPilot_routes_exact_anchor : String :=
  "OperatorKO7.Meta.Plugs.QuantumQecPilot.RoutesExact.quantumQecPilotRoutesExact"

end OperatorKO7.Meta.Plugs.QuantumQecPilot
