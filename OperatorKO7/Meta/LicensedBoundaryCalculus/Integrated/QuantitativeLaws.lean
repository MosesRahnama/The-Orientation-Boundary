import OperatorKO7.Meta.LicensedBoundaryCalculus.Integrated.Composition
import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.StructuralComposition
import OperatorKO7.Meta.LicensedBoundaryCalculus.Accounting.AdditiveValuation

/-!
# Integrated quantitative composition laws

This module combines domain and edge decompositions, finite fiber and coverage
bounds, ledger addition, and typed-resource additivity. Every composition
theorem receives an explicit `CompositeSemanticCapability` argument.

## Audit slots

Relation: composable integrated partial licensed morphisms.
Closure: finite structural counts, trace append, and vector valuation.
Trust: kernel-only, with classical finite enumeration.
Scope: structural and accounting laws for inputs carrying the explicit
composition capability required by `Composition`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace IntegratedBoundaryTransaction

open PartialLicensedReductionMorphism

universe u v w d a d₁ a₁ d₂ a₂

/-- Integrated composition laws conditional on the supplied
`CompositeSemanticCapability`. -/
theorem quantitative_composition_universal
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CompositeSemanticCapability
      first.morphism second.morphism Defect Action) :
    undefinedStateCount (comp first second semantic).morphism =
        undefinedStateCount first.morphism +
          downstreamUndefinedStateCount first.morphism second.morphism ∧
      rejectedEdgeCount (comp first second semantic).morphism =
        rejectedEdgeCount first.morphism +
          downstreamRejectedEdgeCount first.morphism second.morphism ∧
      maximumFiberCardinality (comp first second semantic).morphism ≤
        maximumFiberCardinality first.morphism *
          maximumFiberCardinality second.morphism ∧
      targetCoverageGap second.morphism ≤
        targetCoverageGap (comp first second semantic).morphism ∧
      (comp first second semantic).ledger = first.ledger + second.ledger := by
  change
    undefinedStateCount
          (PartialLicensedReductionMorphism.comp first.morphism second.morphism) =
        undefinedStateCount first.morphism +
          downstreamUndefinedStateCount first.morphism second.morphism ∧
      rejectedEdgeCount
          (PartialLicensedReductionMorphism.comp first.morphism second.morphism) =
        rejectedEdgeCount first.morphism +
          downstreamRejectedEdgeCount first.morphism second.morphism ∧
      maximumFiberCardinality
          (PartialLicensedReductionMorphism.comp first.morphism second.morphism) ≤
        maximumFiberCardinality first.morphism *
          maximumFiberCardinality second.morphism ∧
      targetCoverageGap second.morphism ≤
        targetCoverageGap
          (PartialLicensedReductionMorphism.comp first.morphism second.morphism) ∧
      (comp first second semantic).ledger = first.ledger + second.ledger
  rcases structural_composition_universal first.morphism second.morphism with
    ⟨hDomain, hEdge, hFiber, hCoverage⟩
  exact ⟨hDomain, hEdge, hFiber, hCoverage, comp_ledger first second semantic⟩

/-- Exact pointwise defect formulas and ledger addition in one theorem. -/
theorem quantitative_composition_pointwise
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CompositeSemanticCapability
      first.morphism second.morphism Defect Action) :
    (forall x,
      ¬ (comp first second semantic).morphism.domain x ↔
        ¬ first.morphism.domain x ∨
          exists hx : first.morphism.domain x,
            ¬ second.morphism.domain (first.morphism.map ⟨x, hx⟩)) ∧
    (forall x y,
      ¬ (comp first second semantic).morphism.admitted x y ↔
        ¬ first.morphism.admitted x y ∨
          exists hF : first.morphism.admitted x y,
            ¬ second.morphism.admitted
              (first.morphism.map
                ⟨x, first.morphism.admitted_source_domain hF⟩)
              (first.morphism.map
                ⟨y, first.morphism.admitted_target_domain hF⟩)) ∧
    (comp first second semantic).ledger = first.ledger + second.ledger := by
  change
    (forall x,
      ¬ (PartialLicensedReductionMorphism.comp
          first.morphism second.morphism).domain x ↔
        ¬ first.morphism.domain x ∨
          exists hx : first.morphism.domain x,
            ¬ second.morphism.domain (first.morphism.map ⟨x, hx⟩)) ∧
    (forall x y,
      ¬ (PartialLicensedReductionMorphism.comp
          first.morphism second.morphism).admitted x y ↔
        ¬ first.morphism.admitted x y ∨
          exists hF : first.morphism.admitted x y,
            ¬ second.morphism.admitted
              (first.morphism.map
                ⟨x, first.morphism.admitted_source_domain hF⟩)
              (first.morphism.map
                ⟨y, first.morphism.admitted_target_domain hF⟩)) ∧
    (comp first second semantic).ledger = first.ledger + second.ledger
  exact
    ⟨comp_not_domain_iff first.morphism second.morphism,
      comp_not_admitted_iff first.morphism second.morphism,
      comp_ledger first second semantic⟩

/-- Every additive valuation respects a composition equipped with the supplied
`CompositeSemanticCapability`. -/
theorem resourceVector_composition_universal
    {A : ARS.{u}} {B : ARS.{v}} {C : ARS.{w}}
    [Fintype A.Carrier] [Fintype B.Carrier] [Fintype C.Carrier]
    {Defect₁ : Type d₁} {Action₁ : Type a₁}
    [DecidableEq Defect₁] [Fintype Action₁] [DecidableEq Action₁]
    {Defect₂ : Type d₂} {Action₂ : Type a₂}
    [DecidableEq Defect₂] [Fintype Action₂] [DecidableEq Action₂]
    {Defect : Type d} {Action : Type a}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (valuation : AdditiveValuation)
    (first : IntegratedBoundaryTransaction A B Defect₁ Action₁)
    (second : IntegratedBoundaryTransaction B C Defect₂ Action₂)
    (semantic : CompositeSemanticCapability
      first.morphism second.morphism Defect Action) :
    valuation.evaluate (comp first second semantic).ledger =
      valuation.evaluate first.ledger + valuation.evaluate second.ledger := by
  rw [comp_ledger first second semantic, valuation.evaluate_add]

#check @quantitative_composition_universal
#check @quantitative_composition_pointwise
#check @resourceVector_composition_universal
#print axioms quantitative_composition_universal
#print axioms quantitative_composition_pointwise
#print axioms resourceVector_composition_universal

end IntegratedBoundaryTransaction
end OperatorKO7.Meta.LicensedBoundaryCalculus
