import Mathlib
import OperatorKO7.Meta.Plugs.PharmaUSFda.Routes

/-!
# Five-element PharmaUSFda route classifier

This module defines a total function from five obligation constructors to five route constructors.
It proves catalog membership and bijectivity by finite case analysis. The theorem
`pharmaUSFdaRoutesExact` proves unique equality to the output of that total function; catalog
membership is supplied separately by `plugClassifies_in_catalog`.

The displayed constructor mapping is:

```text
  fda_traditional_nda        →  TraditionalNdaSubstantialEvidence
  fda_accelerated_approval   →  AcceleratedApprovalSurrogate
  fda_breakthrough_therapy   →  BreakthroughTherapyExpedited
  fda_expanded_access        →  ExpandedAccessIndividualPatient
  fda_right_to_try           →  RightToTryEligibleInvestigationalDrug
```

The final string constant names `pharmaUSFdaRoutesExact`; it carries no additional proof.
-/

namespace OperatorKO7.Meta.Plugs.PharmaUSFda

open OperatorKO7.Meta.Plugs.PharmaUSFda

/-- Five regulatory-pathway obligation constructors. -/
inductive PharmaUSFdaObligation
  | FdaTraditionalNda
  | FdaAcceleratedApproval
  | FdaBreakthroughTherapy
  | FdaExpandedAccess
  | FdaRightToTry
  deriving DecidableEq, Repr

/-- Alias for `PharmaUSFdaW1Route`. -/
abbrev PharmaUSFdaRoute := PharmaUSFdaW1Route

/-- Singleton token for the registered `pharmaUSFda` plug. -/
def PharmaUSFdaPlug : PUnit := PUnit.unit

/-- Total function assigning one route constructor to each obligation constructor. -/
def pharmaUSFdaClassifyW1 : PharmaUSFdaObligation → PharmaUSFdaW1Route
  | .FdaTraditionalNda       => .TraditionalNdaSubstantialEvidence
  | .FdaAcceleratedApproval  => .AcceleratedApprovalSurrogate
  | .FdaBreakthroughTherapy  => .BreakthroughTherapyExpedited
  | .FdaExpandedAccess       => .ExpandedAccessIndividualPatient
  | .FdaRightToTry           => .RightToTryEligibleInvestigationalDrug

/-- Compatibility wrapper exposing the total classifier through the registered plug token. -/
def plugClassifies (_ : PUnit) : PharmaUSFdaObligation → PharmaUSFdaRoute :=
  pharmaUSFdaClassifyW1

/-! ## Catalog membership -/

theorem pharmaUSFdaClassifyW1_in_catalog :
    ∀ ob : PharmaUSFdaObligation,
      pharmaUSFdaClassifyW1 ob ∈ pharmaUSFdaW1Routes := by
  intro ob
  cases ob <;> decide

theorem plugClassifies_in_catalog :
    ∀ ob : PharmaUSFdaObligation,
      plugClassifies PharmaUSFdaPlug ob ∈ pharmaUSFdaW1Routes := by
  intro ob
  exact pharmaUSFdaClassifyW1_in_catalog ob

/-! ## Unique output equality -/

/-- Every obligation has a unique route equal to the classifier output. Catalog membership is not a
conjunct of this theorem; it is proved by `plugClassifies_in_catalog`. -/
theorem pharmaUSFdaRoutesExact :
    ∀ obligation : PharmaUSFdaObligation,
      ∃! route : PharmaUSFdaRoute,
        plugClassifies PharmaUSFdaPlug obligation = route := by
  intro obligation
  exact ⟨plugClassifies PharmaUSFdaPlug obligation, rfl, fun _ h => h.symm⟩

/-! ## Bijectivity corollaries -/

theorem pharmaUSFdaClassifyW1_injective :
    Function.Injective pharmaUSFdaClassifyW1 := by
  intro a b h; cases a <;> cases b <;> simp_all [pharmaUSFdaClassifyW1]

theorem pharmaUSFdaClassifyW1_surjective :
    Function.Surjective pharmaUSFdaClassifyW1 := by
  intro r; cases r
  all_goals first
    | exact ⟨.FdaTraditionalNda, rfl⟩
    | exact ⟨.FdaAcceleratedApproval, rfl⟩
    | exact ⟨.FdaBreakthroughTherapy, rfl⟩
    | exact ⟨.FdaExpandedAccess, rfl⟩
    | exact ⟨.FdaRightToTry, rfl⟩

theorem pharmaUSFdaClassifyW1_bijective :
    Function.Bijective pharmaUSFdaClassifyW1 :=
  ⟨pharmaUSFdaClassifyW1_injective, pharmaUSFdaClassifyW1_surjective⟩

/-! ## Catalog completeness corollaries -/

theorem pharmaUSFdaW1Routes_fully_classified :
    ∀ r : PharmaUSFdaW1Route,
      ∃ ob : PharmaUSFdaObligation,
        pharmaUSFdaClassifyW1 ob = r :=
  pharmaUSFdaClassifyW1_surjective

theorem pharmaUSFdaW1Routes_catalog_exact :
    pharmaUSFdaW1Routes.length = 5
    ∧ ∀ r : PharmaUSFdaW1Route,
        r ∈ pharmaUSFdaW1Routes ↔
          r = .TraditionalNdaSubstantialEvidence ∨
          r = .AcceleratedApprovalSurrogate ∨
          r = .BreakthroughTherapyExpedited ∨
          r = .ExpandedAccessIndividualPatient ∨
          r = .RightToTryEligibleInvestigationalDrug := by
  constructor
  · decide
  · intro r; cases r <;> decide

/-! ## Declaration-name string -/

def pharmaUSFda_routes_exact_anchor : String :=
  "OperatorKO7.Meta.Plugs.PharmaUSFda.RoutesExact.pharmaUSFdaRoutesExact"

end OperatorKO7.Meta.Plugs.PharmaUSFda
