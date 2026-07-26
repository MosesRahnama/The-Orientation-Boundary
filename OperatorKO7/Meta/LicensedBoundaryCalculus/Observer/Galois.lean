import Mathlib

/-!
# Observer image-preimage Galois connection

For an arbitrary function, direct image and inverse image satisfy the stated
set-inclusion adjunction. Equality after inverse-image of direct image for all
source sets is equivalent to injectivity. Equality after direct image of
inverse image for all target sets is equivalent to surjectivity.

## Formal scope

Relation: set inclusion under direct and inverse image.
Closure: powerset order under the two set maps.
Trust: kernel-only; set extensionality uses baseline propositional extensionality.
Scope: set inclusion and equality characterizations for an arbitrary function.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.LicensedBoundaryCalculus
namespace ObserverAbstraction

universe u v

variable {X : Type u} {Y : Type v}

/-- Direct-image abstraction. -/
def alpha (f : X -> Y) (S : Set X) : Set Y :=
  f '' S

/-- Inverse-image concretization. -/
def gamma (f : X -> Y) (T : Set Y) : Set X :=
  f ⁻¹' T

/-- Direct image is contained in a target set exactly when the source set is contained in its
inverse image. -/
theorem alpha_subset_iff_subset_gamma
    (f : X -> Y) (S : Set X) (T : Set Y) :
    alpha f S ⊆ T <-> S ⊆ gamma f T := by
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h y ⟨x, hx, rfl⟩
    exact h hx

/-- Every source set is contained in its abstract-then-concrete closure. -/
theorem subset_gamma_alpha (f : X -> Y) (S : Set X) :
    S ⊆ gamma f (alpha f S) :=
  (alpha_subset_iff_subset_gamma f S (alpha f S)).1 Set.Subset.rfl

/-- Direct image after inverse image is contained in the original target set. -/
theorem alpha_gamma_subset (f : X -> Y) (T : Set Y) :
    alpha f (gamma f T) ⊆ T :=
  (alpha_subset_iff_subset_gamma f (gamma f T) T).2 Set.Subset.rfl

/-- Equality after inverse-image of direct image for all source sets is equivalent to injectivity. -/
theorem gamma_alpha_eq_all_iff_injective (f : X -> Y) :
    (forall S : Set X, gamma f (alpha f S) = S) <-> Function.Injective f := by
  constructor
  · intro hExact x y hxy
    have hy : y ∈ gamma f (alpha f ({x} : Set X)) := by
      exact ⟨x, Set.mem_singleton x, hxy⟩
    have : y ∈ ({x} : Set X) := by
      simpa [hExact ({x} : Set X)] using hy
    exact (Set.mem_singleton_iff.mp this).symm
  · intro hinj S
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, hEq⟩
      have hyx : y = x := hinj hEq
      simpa [hyx] using hy
    · exact subset_gamma_alpha f S

/-- Equality after direct image of inverse image for all target sets is equivalent to surjectivity. -/
theorem alpha_gamma_eq_all_iff_surjective (f : X -> Y) :
    (forall T : Set Y, alpha f (gamma f T) = T) <-> Function.Surjective f := by
  constructor
  · intro hExact y
    have hy : y ∈ alpha f (gamma f ({y} : Set Y)) := by
      rw [hExact ({y} : Set Y)]
      exact Set.mem_singleton y
    rcases hy with ⟨x, _, hxy⟩
    exact ⟨x, hxy⟩
  · intro hsurj T
    apply Set.Subset.antisymm
    · exact alpha_gamma_subset f T
    · intro y hy
      rcases hsurj y with ⟨x, rfl⟩
      exact ⟨x, hy, rfl⟩

#check @alpha_subset_iff_subset_gamma
#check @subset_gamma_alpha
#check @alpha_gamma_subset
#check @gamma_alpha_eq_all_iff_injective
#check @alpha_gamma_eq_all_iff_surjective
#print axioms alpha_subset_iff_subset_gamma
#print axioms subset_gamma_alpha
#print axioms alpha_gamma_subset
#print axioms gamma_alpha_eq_all_iff_injective
#print axioms alpha_gamma_eq_all_iff_surjective

end ObserverAbstraction
end OperatorKO7.Meta.LicensedBoundaryCalculus
