import OperatorKO7.Meta.DistinctionBoundary.MinimalFork.Cardinality

/-!
# Pointed nonjoinable forks and the canonical map

Objects carry a source, two marked one-step verdicts, and a proof that the
verdicts do not join. Morphisms preserve all three marks and every relation edge.
The canonical map from `Fork3` is forced by the marks and is injective by the
nonjoinability theorem rather than by an extra morphism field.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.DistinctionBoundary.MinimalFork

open OperatorKO7.Meta.DistinctionBoundary.Quantitative

universe u v w

/-- A marked one-step fork whose marked verdicts are nonjoinable. -/
structure PointedFork where
  Carrier : Type u
  R : Carrier → Carrier → Prop
  source : Carrier
  equal : Carrier
  different : Carrier
  toEqual : R source equal
  toDifferent : R source different
  verdicts_unjoinable : ¬ Joinable R equal different

/-- A morphism of pointed forks preserves all marks and every declared edge. -/
@[ext] structure PointedForkHom (A : PointedFork.{u}) (B : PointedFork.{v}) where
  toFun : A.Carrier → B.Carrier
  map_source : toFun A.source = B.source
  map_equal : toFun A.equal = B.equal
  map_different : toFun A.different = B.different
  map_rel : ∀ {x y}, A.R x y → B.R (toFun x) (toFun y)

instance (A : PointedFork.{u}) (B : PointedFork.{v}) : CoeFun (PointedForkHom A B)
    (fun _ => A.Carrier → B.Carrier) :=
  ⟨PointedForkHom.toFun⟩

/-- The canonical pointed-fork object carried by `Fork3`. -/
def fork3Pointed : PointedFork where
  Carrier := Fork3
  R := Fork3Step
  source := .source
  equal := .equal
  different := .different
  toEqual := Fork3Step.toEqual
  toDifferent := Fork3Step.toDifferent
  verdicts_unjoinable := fork3_verdicts_unjoinable

/-- The mark-forced map from `Fork3` into any pointed fork. -/
def canonicalHom (B : PointedFork.{v}) : PointedForkHom fork3Pointed B where
  toFun
    | .source => B.source
    | .equal => B.equal
    | .different => B.different
  map_source := rfl
  map_equal := rfl
  map_different := rfl
  map_rel := by
    intro x y h
    cases h with
    | toEqual => exact B.toEqual
    | toDifferent => exact B.toDifferent

/-- Every pointed-fork morphism from `Fork3` is the canonical map. -/
theorem hom_unique (B : PointedFork.{v}) (f : PointedForkHom fork3Pointed B) :
    f = canonicalHom B := by
  apply PointedForkHom.ext
  funext x
  cases x with
  | source => exact f.map_source
  | equal => exact f.map_equal
  | different => exact f.map_different

/-- Roadmap-stable uniqueness alias. -/
theorem pointedFork_hom_unique (B : PointedFork.{v})
    (f : PointedForkHom fork3Pointed B) : f = canonicalHom B :=
  hom_unique B f

/-- The canonical map into every pointed nonjoinable fork is injective. -/
theorem canonicalHom_injective (B : PointedFork.{v}) :
    Function.Injective (canonicalHom B).toFun := by
  rcases nonjoinable_peak_has_three_distinct_states
      B.toEqual B.toDifferent B.verdicts_unjoinable with
    ⟨hse, hsd, hed⟩
  intro x y hxy
  cases x <;> cases y <;> simp [canonicalHom] at hxy ⊢
  · exact False.elim (hse hxy)
  · exact False.elim (hsd hxy)
  · exact False.elim (hse hxy.symm)
  · exact False.elim (hed hxy)
  · exact False.elim (hsd hxy.symm)
  · exact False.elim (hed hxy.symm)

/-- Bespoke, universe-polymorphic initiality: every target has a morphism and all
such morphisms are equal. This theorem is independent of Mathlib category syntax. -/
def PointedForkInitial (I : PointedFork.{u}) : Prop :=
  ∀ B : PointedFork.{u},
    Nonempty (PointedForkHom I B) ∧
      ∀ f g : PointedForkHom I B, f = g

/-- `Fork3` is initial in the declared category of marked nonjoinable forks. -/
theorem fork3_initial_bespoke : PointedForkInitial fork3Pointed := by
  intro B
  exact ⟨⟨canonicalHom B⟩, fun f g => (hom_unique B f).trans (hom_unique B g).symm⟩

/-- A concrete nontrivial pointed-fork target: `Fork3` itself, at its actual universe. -/
theorem pointedFork_nonempty : Nonempty PointedFork.{0} :=
  ⟨fork3Pointed⟩

end OperatorKO7.Meta.DistinctionBoundary.MinimalFork
