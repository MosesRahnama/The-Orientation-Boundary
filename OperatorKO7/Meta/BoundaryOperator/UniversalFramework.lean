import OperatorKO7.Meta.BoundaryOperator

/-!
This module defines carrier maps preserving a BoundaryOperator domain and commuting with its
partial map. Identity and composition satisfy the displayed local morphism laws. The result is a
lightweight algebra of BoundaryMorphism values.
















-/

set_option linter.dupNamespace false

namespace OperatorKO7.Meta.BoundaryOperator.UniversalFramework

/-- Data record whose requirements are the fields displayed below.

-/
structure BoundaryMorphism {X Y X' Y' : Type*}
    (B : BoundaryOperator X Y) (B' : BoundaryOperator X' Y') where
  fX : X → X'
  fY : Y → Y'
  domain_preserve : ∀ x, B.domain x → B'.domain (fX x)
  apply_commute : ∀ (x : X) (h : B.domain x),
    fY (B.apply x h) = B'.apply (fX x) (domain_preserve x h)

namespace BoundaryMorphism

/-- Field requirements are given by the displayed type.
-/
@[ext] theorem hom_ext {X Y X' Y' : Type*}
    {B : BoundaryOperator X Y} {B' : BoundaryOperator X' Y'}
    {φ ψ : BoundaryMorphism B B'} (hX : φ.fX = ψ.fX) (hY : φ.fY = ψ.fY) : φ = ψ := by
  cases φ; cases ψ; cases hX; cases hY; rfl

/-- Definition with formal content given by the displayed type and body. -/
def id {X Y : Type*} (B : BoundaryOperator X Y) : BoundaryMorphism B B where
  fX := fun x => x
  fY := fun y => y
  domain_preserve := fun _ h => h
  apply_commute := fun _ _ => rfl

/-- Definition with formal content given by the displayed type and body. -/
def comp {X Y X' Y' X'' Y'' : Type*}
    {B : BoundaryOperator X Y} {B' : BoundaryOperator X' Y'}
    {B'' : BoundaryOperator X'' Y''}
    (φ : BoundaryMorphism B B') (ψ : BoundaryMorphism B' B'') :
    BoundaryMorphism B B'' where
  fX := fun x => ψ.fX (φ.fX x)
  fY := fun y => ψ.fY (φ.fY y)
  domain_preserve := fun x h => ψ.domain_preserve (φ.fX x) (φ.domain_preserve x h)
  apply_commute := fun x h => by
    rw [φ.apply_commute x h, ψ.apply_commute (φ.fX x) (φ.domain_preserve x h)]

/-- The displayed proposition follows from the stated hypotheses. -/
theorem id_comp {X Y X' Y' : Type*}
    {B : BoundaryOperator X Y} {B' : BoundaryOperator X' Y'}
    (φ : BoundaryMorphism B B') : (id B).comp φ = φ := by
  ext <;> rfl

/-- The displayed proposition follows from the stated hypotheses. -/
theorem comp_id {X Y X' Y' : Type*}
    {B : BoundaryOperator X Y} {B' : BoundaryOperator X' Y'}
    (φ : BoundaryMorphism B B') : φ.comp (id B') = φ := by
  ext <;> rfl

/-- The displayed proposition follows from the stated hypotheses. -/
theorem comp_assoc {X Y X' Y' X'' Y'' X''' Y''' : Type*}
    {B : BoundaryOperator X Y} {B' : BoundaryOperator X' Y'}
    {B'' : BoundaryOperator X'' Y''} {B''' : BoundaryOperator X''' Y'''}
    (φ : BoundaryMorphism B B') (ψ : BoundaryMorphism B' B'')
    (χ : BoundaryMorphism B'' B''') :
    (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) := by
  ext <;> rfl

end BoundaryMorphism

/-- Definition with formal content given by the displayed type and body.
-/
noncomputable def toyEndomorphism :
    BoundaryMorphism toyBoundaryOperator toyBoundaryOperator :=
  BoundaryMorphism.id toyBoundaryOperator

/-- Definition with formal content given by the displayed type and body. -/
def universal_framework_anchor : String :=
  "OperatorKO7.Meta.BoundaryOperator.UniversalFramework.BoundaryMorphism.comp_assoc"

end OperatorKO7.Meta.BoundaryOperator.UniversalFramework
