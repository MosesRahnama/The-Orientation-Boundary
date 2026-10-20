import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.DefectAdequacy

/-!
# Repair semantics

A repair certificate supplies action-indexed subrelations, preservation of a
named protected relation, and both directions of the correspondence between
`closes` membership and resolution for represented defects. `PeakResolved`
holds when the two source edges and failure of joinability do not coexist; it
therefore covers branch removal and joinability of surviving endpoints.

## Formal scope

Relation: scoped relation and action-indexed repaired subrelations.
Closure: absence of the represented non-joinable peak after repair.
Trust: kernel-only.
Scope: source-local represented defects and protected one-step semantics.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v w

/-- A source-local peak has been resolved in `relation` when the two source
edges do not both survive as a non-joinable pair.  This includes both licensed
branch removal and repairs that preserve both branches but make them join. -/
def PeakResolved {X : Type u}
    (relation : X → X → Prop) (source left right : X) : Prop :=
  ¬ (relation source left ∧ relation source right ∧
    ¬ Joinable relation left right)

/-- Concrete semantics of the repair actions in one semantic model. -/
structure RepairSemantics
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type v} {Action : Type w}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (data : SemanticConstructionData A Defect Action)
    (defects : DefectAdequacy data) where
  repairedRelation : Action → A.Carrier → A.Carrier → Prop
  protectedRelation : A.Carrier → A.Carrier → Prop
  protected_sub_scope : ∀ {x y}, protectedRelation x y →
    data.scope.relation x y
  repaired_sub_scope : ∀ a {x y}, repairedRelation a x y →
    data.scope.relation x y
  preserves_protected : ∀ a {x y}, protectedRelation x y →
    repairedRelation a x y
  closes_sound : ∀ a d, d ∈ data.defects → d ∈ data.closes a →
    PeakResolved (repairedRelation a) data.scope.source
      (defects.endpoints d).1 (defects.endpoints d).2
  closes_complete : ∀ a d, d ∈ data.defects →
    PeakResolved (repairedRelation a) data.scope.source
      (defects.endpoints d).1 (defects.endpoints d).2 →
    d ∈ data.closes a

namespace RepairSemantics

variable {A : ARS.{u}} [Fintype A.Carrier]
variable {Defect : Type v} {Action : Type w}
variable [DecidableEq Defect] [Fintype Action] [DecidableEq Action]

/-- For a represented defect, `closes` membership is equivalent to `PeakResolved` after the action. -/
theorem closes_iff_resolved
    {data : SemanticConstructionData A Defect Action}
    {defects : DefectAdequacy data}
    (repairs : RepairSemantics data defects)
    (a : Action) (d : Defect) (hd : d ∈ data.defects) :
    d ∈ data.closes a ↔
      PeakResolved (repairs.repairedRelation a) data.scope.source
        (defects.endpoints d).1 (defects.endpoints d).2 :=
  ⟨repairs.closes_sound a d hd, repairs.closes_complete a d hd⟩

omit [Fintype A.Carrier] in
/-- Joinability of surviving endpoints is sufficient to resolve a peak. -/
theorem peakResolved_of_joinable
    {relation : A.Carrier → A.Carrier → Prop}
    {source left right : A.Carrier}
    (h : Joinable relation left right) :
    PeakResolved relation source left right := by
  intro hpeak
  exact hpeak.2.2 h

omit [Fintype A.Carrier] in
/-- Removing the left branch is sufficient to resolve a peak. -/
theorem peakResolved_of_not_left
    {relation : A.Carrier → A.Carrier → Prop}
    {source left right : A.Carrier}
    (h : ¬ relation source left) :
    PeakResolved relation source left right := by
  intro hpeak
  exact h hpeak.1

omit [Fintype A.Carrier] in
/-- Removing the right branch is sufficient to resolve a peak. -/
theorem peakResolved_of_not_right
    {relation : A.Carrier → A.Carrier → Prop}
    {source left right : A.Carrier}
    (h : ¬ relation source right) :
    PeakResolved relation source left right := by
  intro hpeak
  exact h hpeak.2.1

/-- Every protected edge survives every certified repair. -/
theorem protected_survives
    {data : SemanticConstructionData A Defect Action}
    {defects : DefectAdequacy data}
    (repairs : RepairSemantics data defects)
    (a : Action) {x y : A.Carrier}
    (h : repairs.protectedRelation x y) :
    repairs.repairedRelation a x y :=
  repairs.preserves_protected a h

#check @closes_iff_resolved
#check @peakResolved_of_joinable
#check @peakResolved_of_not_left
#check @peakResolved_of_not_right
#check @protected_survives
#print axioms closes_iff_resolved
#print axioms peakResolved_of_joinable
#print axioms peakResolved_of_not_left
#print axioms peakResolved_of_not_right
#print axioms protected_survives

end RepairSemantics
end OperatorKO7.Meta.LicensedBoundaryCalculus
