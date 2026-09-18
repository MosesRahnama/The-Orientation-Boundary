import OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade
import OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance

set_option autoImplicit false

/-!
# Product and quotient computation rules for licensing data

This module supplies the W3 product/quotient computation surface without
promoting any analogy beyond the theorem actually proved.

* `ProductStep` is the asynchronous product of two dynamics.
* Its reflexive-transitive closure is exactly componentwise reachability.
* Persistent licenses compose and decompose over that product.
* The role-erasure quotient exposes the existing noninjective-discriminator
  obstruction as the typed negative computation rule.
* The licensed pair subrelation recovers the already-proved `Box ↔ D1p`
  equivalence.
-/

namespace OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient

open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense
open OperatorKO7.Meta.DistinctionBoundary.DynamicDiagonalGrade
open OperatorKO7.Meta.DistinctionBoundary.RoleErasureInstance
open OperatorKO7.Meta.DistinctionBoundary.ObserverExpressivity

universe u v

variable {A : Type u} {B : Type v}

/-- Asynchronous product dynamics: exactly one component moves at a time. -/
inductive ProductStep (R : A → A → Prop) (S : B → B → Prop) :
    A × B → A × B → Prop
  | left {a a' : A} {b : B} : R a a' → ProductStep R S (a, b) (a', b)
  | right {a : A} {b b' : B} : S b b' → ProductStep R S (a, b) (a, b')

/-- Lift a left-factor reduction path into the product. -/
theorem productStep_star_left {R : A → A → Prop} {S : B → B → Prop}
    {a a' : A} {b : B} (h : Relation.ReflTransGen R a a') :
    Relation.ReflTransGen (ProductStep R S) (a, b) (a', b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (ProductStep.left hstep)

/-- Lift a right-factor reduction path into the product. -/
theorem productStep_star_right {R : A → A → Prop} {S : B → B → Prop}
    {a : A} {b b' : B} (h : Relation.ReflTransGen S b b') :
    Relation.ReflTransGen (ProductStep R S) (a, b) (a, b') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.tail ih (ProductStep.right hstep)

/-- Every product path projects to a path in each factor. -/
theorem productStep_star_components {R : A → A → Prop} {S : B → B → Prop}
    {p q : A × B} (h : Relation.ReflTransGen (ProductStep R S) p q) :
    Relation.ReflTransGen R p.1 q.1 ∧ Relation.ReflTransGen S p.2 q.2 := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      cases hstep with
      | left hL => exact ⟨Relation.ReflTransGen.tail ih.1 hL, ih.2⟩
      | right hR => exact ⟨ih.1, Relation.ReflTransGen.tail ih.2 hR⟩

/-- Product reachability is exactly componentwise reachability. -/
theorem productStep_star_iff {R : A → A → Prop} {S : B → B → Prop}
    {a a' : A} {b b' : B} :
    Relation.ReflTransGen (ProductStep R S) (a, b) (a', b') ↔
      Relation.ReflTransGen R a a' ∧ Relation.ReflTransGen S b b' := by
  constructor
  · intro h
    simpa using productStep_star_components h
  · rintro ⟨ha, hb⟩
    exact Relation.ReflTransGen.trans
      (productStep_star_left (S := S) (b := b) ha)
      (productStep_star_right (R := R) (a := a') hb)

/-- Persistent licenses compute componentwise over asynchronous products. -/
theorem box_product_iff {A B : Type} {R : A → A → Prop} {S : B → B → Prop}
    {P : A → Prop} {Q : B → Prop} (a : A) (b : B) :
    Box (ProductStep R S) (fun p : A × B => P p.1 ∧ Q p.2) (a, b) ↔
      Box R P a ∧ Box S Q b := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · refine ⟨h.holds.1, ?_⟩
      intro a' ha'
      exact (h.persists (a', b) (productStep_star_left (S := S) ha')).1
    · refine ⟨h.holds.2, ?_⟩
      intro b' hb'
      exact (h.persists (a, b') (productStep_star_right (R := R) hb')).2
  · rintro ⟨hP, hQ⟩
    refine ⟨⟨hP.holds, hQ.holds⟩, ?_⟩
    intro p hp
    have hc := productStep_star_components hp
    exact ⟨hP.persists p.1 hc.1, hQ.persists p.2 hc.2⟩

/-- Typed quotient obstruction: role erasure recovers the existing theorem that
no operation natural under the noninjective role-collapse map can be a complete
disequality discriminator at the active collapse point. -/
theorem roleErasure_quotient_no_discriminator {Y : Type*} (y₀ y : Y)
    (t : Occ Y → Occ Y → Occ Y) (hnat : NaturalUnder roleCollapse t) :
    ¬ IsDiscriminator ((y₀, Role.active) : Occ Y) t :=
  no_roleBlind_discriminator y₀ y t hnat

/-- The licensed pair subrelation computes to persistent distinction exactly:
the generic `Box` license on independently lifted dynamics is D1p. -/
theorem licensedPairSubrelation_box_iff_d1p
    {α β : Type} {R : α → α → Prop} (q : α → β) (x y : α) :
    Box (PairLift R) (fun p : α × α => q p.1 ≠ q p.2) (x, y) ↔
      D1p R q x y :=
  box_pairLift_separation_iff q x y

#check ProductStep
#check productStep_star_left
#check productStep_star_right
#check productStep_star_components
#check productStep_star_iff
#check box_product_iff
#check roleErasure_quotient_no_discriminator
#check licensedPairSubrelation_box_iff_d1p
#print axioms productStep_star_left
#print axioms productStep_star_right
#print axioms productStep_star_components
#print axioms productStep_star_iff
#print axioms box_product_iff
#print axioms roleErasure_quotient_no_discriminator
#print axioms licensedPairSubrelation_box_iff_d1p

end OperatorKO7.Meta.LicensedBoundaryCalculus.LicensingProductQuotient
