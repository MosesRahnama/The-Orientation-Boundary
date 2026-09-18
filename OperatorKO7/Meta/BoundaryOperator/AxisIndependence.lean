import OperatorKO7.Meta.LicensedBoundaryCalculus.OrientationFace
import OperatorKO7.Meta.LicensedBoundaryCalculus.DistinctionFace

/-!
# Axis independence for the boundary operator

Orientation and distinction are represented as different morphism defects.
Orientation can collapse states while admitting every source edge.  Distinction
can reject a raw edge while using the identity state map.

## Audit slots

Relation: licensed morphisms between abstract reduction systems.
Closure: root one-step defects only.
Trust: kernel-only; the witnesses are the Bool projection and KO7 eqW branch.
Scope: axis separation, not a scalar ranking of the axes.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryOperator

open OperatorKO7.Meta.LicensedBoundaryCalculus

universe u v

/-- A morphism has state collapse when two distinct source states map to one
target state. -/
def HasStateCollapse {A : ARS.{u}} {B : ARS.{v}}
    (F : LicensedReductionMorphism A B) : Prop :=
  exists x y : A.Carrier, Not (x = y) /\ F.map x = F.map y

/-- A morphism has edge rejection when a raw source edge is outside the admitted
subrelation. -/
def HasRejectedEdge {A : ARS.{u}} {B : ARS.{v}}
    (F : LicensedReductionMorphism A B) : Prop :=
  exists x y : A.Carrier, A.step x y /\ ¬ F.admitted x y

/-- The Bool orientation fixture has state collapse. -/
theorem orientation_fixture_has_stateCollapse :
    HasStateCollapse
      (OrientationFace.boolOrientationFace_fixture.toMorphism) :=
  OrientationFace.boolOrientationFace_collapses_states

/-- The Bool orientation fixture rejects no source edge. -/
theorem orientation_fixture_no_rejectedEdge :
    ¬ HasRejectedEdge
      (OrientationFace.boolOrientationFace_fixture.toMorphism) := by
  intro h
  rcases h with ⟨x, y, hraw, hreject⟩
  exact hreject hraw

/-- The KO7 distinction fixture has no state collapse, since its map is identity. -/
theorem distinction_fixture_no_stateCollapse :
    ¬ HasStateCollapse
      (DistinctionFace.ko7DistinctionFace_fixture.toMorphism) := by
  intro h
  rcases h with ⟨x, y, hne, hmap⟩
  exact hne hmap

/-- The KO7 distinction fixture rejects the diagonal `eqW` branch. -/
theorem distinction_fixture_has_rejectedEdge :
    HasRejectedEdge
      (DistinctionFace.ko7DistinctionFace_fixture.toMorphism) :=
  DistinctionFace.ko7DistinctionFace_rejects_diagonal_branch

/-- The two axes are independent at the morphism-defect level. -/
theorem orientation_distinction_axis_independent :
    HasStateCollapse
        (OrientationFace.boolOrientationFace_fixture.toMorphism) /\
      ¬ HasRejectedEdge
        (OrientationFace.boolOrientationFace_fixture.toMorphism) /\
      ¬ HasStateCollapse
        (DistinctionFace.ko7DistinctionFace_fixture.toMorphism) /\
      HasRejectedEdge
        (DistinctionFace.ko7DistinctionFace_fixture.toMorphism) := by
  exact
    ⟨orientation_fixture_has_stateCollapse,
      orientation_fixture_no_rejectedEdge,
      distinction_fixture_no_stateCollapse,
      distinction_fixture_has_rejectedEdge⟩

#check HasStateCollapse
#check HasRejectedEdge
#check orientation_fixture_has_stateCollapse
#check orientation_fixture_no_rejectedEdge
#check distinction_fixture_no_stateCollapse
#check distinction_fixture_has_rejectedEdge
#check orientation_distinction_axis_independent
#print axioms orientation_fixture_has_stateCollapse
#print axioms orientation_fixture_no_rejectedEdge
#print axioms distinction_fixture_no_stateCollapse
#print axioms distinction_fixture_has_rejectedEdge
#print axioms orientation_distinction_axis_independent

end OperatorKO7.Meta.BoundaryOperator
