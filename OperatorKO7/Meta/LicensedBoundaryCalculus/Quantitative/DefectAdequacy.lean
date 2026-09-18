import OperatorKO7.Meta.LicensedBoundaryCalculus.Quantitative.SemanticProfile

/-!
# Relation-derived defect adequacy

A local defect is an actual non-joinable peak in the relation stored by a
semantic scope.  A finite defect vocabulary is adequate only when every listed
defect denotes such a peak, every actual peak is represented up to branch
exchange, and duplicate representatives are excluded.

## Audit slots

Relation: `SemanticScope.relation` at its named source.
Closure: reflexive-transitive joinability from the quantitative core.
Trust: kernel-only; finite membership uses classical decidability.
Scope: source-local peaks, not arbitrary contextual critical pairs.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v w

/-- A source-local peak whose two branches fail to join. -/
structure ActualLocalDefect {A : ARS.{u}} (scope : SemanticScope A) where
  left : A.Carrier
  right : A.Carrier
  source_to_left : scope.relation scope.source left
  source_to_right : scope.relation scope.source right
  branches_not_joinable : ¬ Joinable scope.relation left right

/-- Two ordered endpoint pairs represent the same unoriented peak. -/
def SameDefectEndpoints {X : Type u} (p q : X × X) : Prop :=
  p = q ∨ p = (q.2, q.1)

namespace SameDefectEndpoints

theorem refl {X : Type u} (p : X × X) : SameDefectEndpoints p p :=
  Or.inl rfl

theorem symm {X : Type u} {p q : X × X}
    (h : SameDefectEndpoints p q) : SameDefectEndpoints q p := by
  rcases h with h | h
  · exact Or.inl h.symm
  · right
    cases p
    cases q
    simp_all

end SameDefectEndpoints

/-- A finite defect vocabulary represents all and only actual local defects. -/
structure DefectAdequacy
    {A : ARS.{u}} [Fintype A.Carrier]
    {Defect : Type v} {Action : Type w}
    [DecidableEq Defect] [Fintype Action] [DecidableEq Action]
    (data : SemanticConstructionData A Defect Action) where
  endpoints : Defect → A.Carrier × A.Carrier
  sound : ∀ d, d ∈ data.defects →
    ∃ actual : ActualLocalDefect data.scope,
      endpoints d = (actual.left, actual.right)
  complete : ∀ actual : ActualLocalDefect data.scope,
    ∃ d, d ∈ data.defects ∧
      SameDefectEndpoints (endpoints d) (actual.left, actual.right)
  irredundant : ∀ d₁ d₂,
    d₁ ∈ data.defects → d₂ ∈ data.defects →
      SameDefectEndpoints (endpoints d₁) (endpoints d₂) → d₁ = d₂

namespace DefectAdequacy

variable {A : ARS.{u}} [Fintype A.Carrier]
variable {Defect : Type v} {Action : Type w}
variable [DecidableEq Defect] [Fintype Action] [DecidableEq Action]

/-- Every represented defect is backed by a relation-derived peak. -/
theorem represented_is_actual
    {data : SemanticConstructionData A Defect Action}
    (certificate : DefectAdequacy data) {d : Defect}
    (hd : d ∈ data.defects) :
    ∃ actual : ActualLocalDefect data.scope,
      certificate.endpoints d = (actual.left, actual.right) :=
  certificate.sound d hd

/-- An empty certified defect set forces source-local confluence of one-step
peaks: every pair of immediate reducts is joinable. -/
theorem empty_defects_immediate_peaks_joinable
    {data : SemanticConstructionData A Defect Action}
    (certificate : DefectAdequacy data) (hempty : data.defects = ∅)
    {left right : A.Carrier}
    (hleft : data.scope.relation data.scope.source left)
    (hright : data.scope.relation data.scope.source right) :
    Joinable data.scope.relation left right := by
  by_contra hnot
  let actual : ActualLocalDefect data.scope :=
    { left := left
      right := right
      source_to_left := hleft
      source_to_right := hright
      branches_not_joinable := hnot }
  rcases certificate.complete actual with ⟨d, hd, _⟩
  rw [hempty] at hd
  simp at hd

#check @represented_is_actual
#check @empty_defects_immediate_peaks_joinable
#print axioms represented_is_actual
#print axioms empty_defects_immediate_peaks_joinable

end DefectAdequacy
end OperatorKO7.Meta.LicensedBoundaryCalculus
