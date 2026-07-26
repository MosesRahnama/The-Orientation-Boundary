import Mathlib
import OperatorKO7.Meta.Plugs.LawUSStateCA.Routes

/-!
# LawUSStateCA finite W₁ route correspondence

This module defines a five-constructor obligation type and a total map to the
five W₁ routes imported from `Routes`. It proves catalog membership and that
the declared map is bijective. These results concern the finite Lean types in
this file; they do not prove coverage of every California legal obligation or
correspondence with an external implementation.
-/

namespace OperatorKO7.Meta.Plugs.LawUSStateCA

open OperatorKO7.Meta.Plugs.LawUSStateCA

/-- Five obligation labels used by the finite route correspondence. -/
inductive LawUSStateCAObligation
  | CaAdministrativeLaw
  | CaEvidenceCode
  | CaCivilProcedure
  | CaConstitutionalLaw
  | CaPenalCode
  deriving DecidableEq, Repr

/-- Alias for the W₁ route type imported from `Routes`. -/
abbrev LawUSStateCARoute := LawUSStateCAW1Route

/-- Singleton token for the registered `lawUSStateCA` plug. -/
def LawUSStateCAPlug : PUnit := PUnit.unit

/-- Total map from the five declared obligation labels to W₁ routes. -/
def lawUSStateCAClassifyW1 : LawUSStateCAObligation → LawUSStateCAW1Route
  | .CaAdministrativeLaw  => .ChevronStepOneCalifornia
  | .CaEvidenceCode       => .AuerDeferenceCalifornia
  | .CaCivilProcedure     => .SkidmoreDeferenceCalifornia
  | .CaConstitutionalLaw  => .SlidingScaleBalancingCa
  | .CaPenalCode          => .LenityRuleCalifornia

/-- Classifier surface obtained from `lawUSStateCAClassifyW1`. -/
def plugClassifies (_ : PUnit) : LawUSStateCAObligation → LawUSStateCARoute :=
  lawUSStateCAClassifyW1

/-! ## Catalog membership -/

/-- Every classified route lives in the `lawUSStateCAW1Routes` list
(the W₁ catalog). Ensures the classification function stays inside
the declared catalog. -/
theorem lawUSStateCAClassifyW1_in_catalog :
    ∀ ob : LawUSStateCAObligation,
      lawUSStateCAClassifyW1 ob ∈ lawUSStateCAW1Routes := by
  intro ob
  cases ob <;> decide

theorem plugClassifies_in_catalog :
    ∀ ob : LawUSStateCAObligation,
      plugClassifies LawUSStateCAPlug ob ∈ lawUSStateCAW1Routes := by
  intro ob
  exact lawUSStateCAClassifyW1_in_catalog ob

/-! ## Functional uniqueness -/

/-- A total function has a unique value at each input. Catalog membership of
that value is proved separately by `lawUSStateCAClassifyW1_in_catalog`. -/
theorem lawUSStateCARoutesExact :
    ∀ obligation : LawUSStateCAObligation,
      ∃! route : LawUSStateCARoute,
        plugClassifies LawUSStateCAPlug obligation = route := by
  intro obligation
  exact ⟨plugClassifies LawUSStateCAPlug obligation, rfl, fun _ h => h.symm⟩


/-! ## Bijectivity corollaries -/

/-- The classification is injective: distinct obligation types map to
distinct W₁ routes. Five distinct obligations map to five distinct
routes; the catalog is exactly saturated. -/
theorem lawUSStateCAClassifyW1_injective :
    Function.Injective lawUSStateCAClassifyW1 := by
  intro a b h; cases a <;> cases b <;> simp_all [lawUSStateCAClassifyW1]

/-- The classification is surjective onto the W₁ route type: every W₁
route is the image of some obligation. Together with injectivity this
gives a bijection between the two five-element types. -/
theorem lawUSStateCAClassifyW1_surjective :
    Function.Surjective lawUSStateCAClassifyW1 := by
  intro r; cases r
  all_goals first
    | exact ⟨.CaAdministrativeLaw, rfl⟩
    | exact ⟨.CaEvidenceCode, rfl⟩
    | exact ⟨.CaCivilProcedure, rfl⟩
    | exact ⟨.CaConstitutionalLaw, rfl⟩
    | exact ⟨.CaPenalCode, rfl⟩

/-- The classification is bijective. -/
theorem lawUSStateCAClassifyW1_bijective :
    Function.Bijective lawUSStateCAClassifyW1 :=
  ⟨lawUSStateCAClassifyW1_injective, lawUSStateCAClassifyW1_surjective⟩

/-! ## Catalog completeness corollaries -/

/-- Every constructor of the finite W₁ route type is the image of one of the
five declared obligation labels. -/
theorem lawUSStateCAW1Routes_fully_classified :
    ∀ r : LawUSStateCAW1Route,
      ∃ ob : LawUSStateCAObligation,
        lawUSStateCAClassifyW1 ob = r := by
  intro r
  exact lawUSStateCAClassifyW1_surjective r

/-- The W₁ route catalog has no unclassifiable members: the
classification function saturates the catalog exactly. -/
theorem lawUSStateCAW1Routes_catalog_exact :
    lawUSStateCAW1Routes.length = 5
    ∧ ∀ r : LawUSStateCAW1Route,
        r ∈ lawUSStateCAW1Routes ↔
          r = .AuerDeferenceCalifornia ∨
          r = .ChevronStepOneCalifornia ∨
          r = .SkidmoreDeferenceCalifornia ∨
          r = .SlidingScaleBalancingCa ∨
          r = .LenityRuleCalifornia := by
  constructor
  · decide
  · intro r; cases r <;> decide

/-! ## Declaration-name anchor -/

/-- Stable declaration-name string for `lawUSStateCARoutesExact`. -/
def lawUSStateCA_routes_exact_anchor : String :=
  "OperatorKO7.Meta.Plugs.LawUSStateCA.RoutesExact.lawUSStateCARoutesExact"

end OperatorKO7.Meta.Plugs.LawUSStateCA
