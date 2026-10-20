import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Pointed

/-!
# Category-theoretic universal property of `Fork3`

This file wraps the bespoke pointed-fork morphisms in Mathlib's `Category` and
proves that `fork3Pointed` is an initial object. The category is exactly the one
declared in `Pointed.lean`: morphisms preserve all three marks and every edge.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open CategoryTheory

universe u

/-- Identity pointed-fork morphism. -/
def PointedForkHom.id (A : PointedFork.{u}) : PointedForkHom A A where
  toFun := fun x => x
  map_source := rfl
  map_equal := rfl
  map_different := rfl
  map_rel := fun h => h

/-- Composition of pointed-fork morphisms, in diagrammatic order. -/
def PointedForkHom.comp {A B C : PointedFork.{u}}
    (f : PointedForkHom A B) (g : PointedForkHom B C) : PointedForkHom A C where
  toFun := fun x => g.toFun (f.toFun x)
  map_source := by rw [f.map_source, g.map_source]
  map_equal := by rw [f.map_equal, g.map_equal]
  map_different := by rw [f.map_different, g.map_different]
  map_rel := fun h => g.map_rel (f.map_rel h)

instance : Category (PointedFork.{u}) where
  Hom A B := PointedForkHom A B
  id A := PointedForkHom.id A
  comp f g := PointedForkHom.comp f g
  id_comp := by
    intro A B f
    apply PointedForkHom.ext
    funext x
    rfl
  comp_id := by
    intro A B f
    apply PointedForkHom.ext
    funext x
    rfl
  assoc := by
    intro A B C D f g h
    apply PointedForkHom.ext
    rfl

/-- Roadmap-stable explicit name for the already installed category instance.
This is a definition naming the instance, not a second competing instance. -/
def PointedFork.instCategory : Category (PointedFork.{u}) := inferInstance

/-- The category-level universal property at the actual universe of the concrete
three-state carrier. -/
def fork3_isInitial :
    CategoryTheory.Limits.IsInitial (fork3Pointed : PointedFork.{0}) :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom
    (fun B => canonicalHom B)
    (fun B f => hom_unique B f)

/-- Every universe-0 target receives the canonical categorical morphism from `Fork3`. -/
theorem fork3_initial_hom_nonempty (B : PointedFork.{0}) :
    Nonempty ((fork3Pointed : PointedFork.{0}) ⟶ B) :=
  ⟨canonicalHom B⟩

/-- The categorical and bespoke universe-0 initiality statements are simultaneously inhabited. -/
theorem fork3_initiality_bundle :
    PointedForkInitial (fork3Pointed : PointedFork.{0}) ∧
      Nonempty (CategoryTheory.Limits.IsInitial (fork3Pointed : PointedFork.{0})) :=
  ⟨fork3_initial_bespoke, ⟨fork3_isInitial⟩⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
