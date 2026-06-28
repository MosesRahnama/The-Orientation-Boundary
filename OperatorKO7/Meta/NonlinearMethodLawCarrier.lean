import OperatorKO7.Meta.ConstructionMethodClassification

/-!
# Nonlinear Method-Law Carrier

This module packages the conservative method-law carrier used for the
unconstrained nonlinear row. It does not claim a universal first-order method
grammar. It records the direct W0 witness already present in the artifact and
the imported-whole W1 licensed-escape witness already present in the
construction-method layer.
-/

namespace OperatorKO7.NonlinearMethodLawCarrier

open OperatorKO7.Trace
open OperatorKO7.BenchmarkedPRCFamily
open OperatorKO7.ConstructionMethodClassification

/-- Relation type tracked by the nonlinear method-law carrier. -/
abbrev NonlinearRelation := Trace → Trace → Prop

/-- The small method-law vocabulary currently attached to the nonlinear carrier. -/
inductive NonlinearMethodLaw where
  | directWholeTerm
  | importedWholeLicensedEscape
  deriving DecidableEq, Repr

/-- Route projection carried by each nonlinear method law. -/
def nonlinearMethodLawRoute : NonlinearMethodLaw → ConstructionRoute
  | .directWholeTerm => .W0
  | .importedWholeLicensedEscape => .W1

/-- Exact route projection for each nonlinear method law. -/
theorem nonlinearMethodLawRoute_exact (law : NonlinearMethodLaw) :
    nonlinearMethodLawRoute law =
      match law with
      | .directWholeTerm => .W0
      | .importedWholeLicensedEscape => .W1 := by
  cases law <;> rfl

/-- Licensed-escape payload carried by the imported-whole nonlinear method law. -/
def NonlinearMethodLawLicensedEscape : NonlinearMethodLaw → Prop
  | .directWholeTerm => False
  | .importedWholeLicensedEscape =>
      PermittedW1Import .importedWholeWitness
        ∧ importedWhole_w1_success.route = .W1
        ∧ HasImportedWholeWitness fullDuplicating
        ∧ ¬ HasDirectWitness fullDuplicating

/-- Carrier object pairing a nonlinear relation with a theorem-backed method law. -/
structure NonlinearMethodLawCarrier where
  relation : NonlinearRelation
  methodLaw : NonlinearMethodLaw
  admits :
    relation = Step ∧
      match methodLaw with
      | .directWholeTerm => HasDirectWitness fullLinear
      | .importedWholeLicensedEscape =>
          NonlinearMethodLawLicensedEscape .importedWholeLicensedEscape

/-- The direct W0 method law is backed by the existing whole-term witness. -/
theorem directWholeTerm_supported :
    HasDirectWitness fullLinear :=
  fullLinear_has_direct_witness

/-- The imported-whole W1 method law is backed by the existing licensed escape. -/
theorem importedWholeLicensedEscape_supported :
    NonlinearMethodLawLicensedEscape .importedWholeLicensedEscape := by
  exact ⟨importedWhole_w1_success_requires_imported_whole,
    importedWhole_w1_success.route_is_w1,
    importedWhole_w1_success_separates_from_w0.2.1,
    importedWhole_w1_success_separates_from_w0.2.2⟩

/-- Canonical direct nonlinear method-law carrier. -/
def directWholeTermCarrier : NonlinearMethodLawCarrier where
  relation := Step
  methodLaw := .directWholeTerm
  admits := ⟨rfl, directWholeTerm_supported⟩

/-- Canonical imported-whole nonlinear licensed-escape carrier. -/
def importedWholeLicensedEscapeCarrier : NonlinearMethodLawCarrier where
  relation := Step
  methodLaw := .importedWholeLicensedEscape
  admits := ⟨rfl, importedWholeLicensedEscape_supported⟩

/-- Every nonlinear method-law carrier is anchored to the Step relation. -/
theorem nonlinearMethodLawCarrier_relation_eq_step
    (carrier : NonlinearMethodLawCarrier) :
    carrier.relation = Step :=
  carrier.admits.1

/-- The direct whole-term law is the only W0 law in the current carrier. -/
theorem directWholeTerm_is_w0 :
    nonlinearMethodLawRoute .directWholeTerm = .W0 :=
  rfl

/-- The imported-whole law is a W1 licensed escape, not a W0 law. -/
theorem importedWholeLicensedEscape_is_w1 :
    nonlinearMethodLawRoute .importedWholeLicensedEscape = .W1 :=
  rfl

/-- Licensed-escape predicate for a relation at a specific route. -/
def relation_has_licensed_escape
    (R : NonlinearRelation) (route : ConstructionRoute) : Prop :=
  ∃ carrier : NonlinearMethodLawCarrier,
    carrier.relation = R
      ∧ nonlinearMethodLawRoute carrier.methodLaw = route
      ∧ route ≠ .W0
      ∧ NonlinearMethodLawLicensedEscape carrier.methodLaw

/-- Direct first-order method predicate for a relation without a licensed escape. -/
def relation_has_direct_first_order_method
    (R : NonlinearRelation) (law : NonlinearMethodLaw) : Prop :=
  ∃ carrier : NonlinearMethodLawCarrier,
    carrier.relation = R
      ∧ carrier.methodLaw = law
      ∧ nonlinearMethodLawRoute law = .W0

/-- Boundary proposition carried by the unsupported arbitrary nonlinear relation row. -/
abbrev unsupported_arbitrary_relation_boundary
    (R : NonlinearRelation) : Prop :=
  (∃ route : ConstructionRoute,
      route ≠ .W0 ∧ relation_has_licensed_escape R route)
    ∨ (¬ ∃ law : NonlinearMethodLaw,
        relation_has_direct_first_order_method R law)

/-- The canonical imported-whole carrier projects a W1 licensed escape for Step. -/
theorem importedWholeLicensedEscapeCarrier_projects_escape :
    relation_has_licensed_escape Step .W1 := by
  refine ⟨importedWholeLicensedEscapeCarrier, rfl, rfl, by decide, ?_⟩
  exact importedWholeLicensedEscape_supported

/-- Classical existence dichotomy for the nonlinear method-law carrier. -/
theorem unsupported_arbitrary_relation_dichotomy
    (R : NonlinearRelation) :
    (∃ carrier : NonlinearMethodLawCarrier, carrier.relation = R)
      ∨ (¬ ∃ carrier : NonlinearMethodLawCarrier, carrier.relation = R) := by
  classical
  exact em _

/-- Every nonlinear relation is either licensed via a non-W0 route or carries no direct W0 method in the current carrier. -/
theorem unsupported_arbitrary_relation_no_first_order_method_or_licensed_escape
    (R : NonlinearRelation) :
  unsupported_arbitrary_relation_boundary R := by
  classical
  by_cases hR : R = Step
  · left
    subst hR
    exact ⟨.W1, by decide, importedWholeLicensedEscapeCarrier_projects_escape⟩
  · right
    intro hdirect
    rcases hdirect with ⟨law, carrier, hrel, _, _⟩
    have hstep : carrier.relation = Step :=
      nonlinearMethodLawCarrier_relation_eq_step carrier
    have : R = Step := by
      calc
        R = carrier.relation := hrel.symm
        _ = Step := hstep
    exact hR this

end OperatorKO7.NonlinearMethodLawCarrier
