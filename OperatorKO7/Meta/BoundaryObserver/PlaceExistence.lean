import OperatorKO7.Meta.BoundaryObserver.PlaceCoordinates
import Mathlib.Data.Set.Card

set_option autoImplicit false

/-!
# Existence of place coordinates

The carrier is PlaceCoordinates.PlaceCoord on the original observer.
The condition concerns attained records and permits an empty source.
Kernel status: direct check with 0 errors and 0 warnings, then a fresh named build, 2026-10-17.
-/

namespace OperatorKO7.Meta.BoundaryObserver.PlaceExistence

/-- The E2 goal states the exact existence criterion for finite attained classes. -/
def PlaceExistenceGoal {X Q : Type*} (q : X → Q) (n : ℕ) : Prop :=
  (∀ y ∈ Set.range q, (q ⁻¹' {y}).Finite) →
    ((PlaceCoordinates.PlaceCoord q n).Nonempty ↔
      ∀ y ∈ Set.range q, (q ⁻¹' {y}).ncard = n)

/-!
## Unit 1: cardinality forced by a place coordinate

The membership premise and the attained-record premise are ORIGINAL_FINAL_ASSUMPTION.
The finite codomain and its cardinality are INDEPENDENTLY_PROVED in pinned Mathlib.
-/

/-- A place coordinate gives each attained class exactly n elements and proves it finite. -/
theorem placeCoord_fiber_cardinality {X Q : Type*} {q : X → Q} {n : ℕ}
    {p : X → Fin n} (hp : p ∈ PlaceCoordinates.PlaceCoord q n)
    (y : Q) (hy : y ∈ Set.range q) :
    (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard = n := by
  have hbij : Set.BijOn p (q ⁻¹' {y}) (Set.univ : Set (Fin n)) := hp y hy
  refine ⟨(Set.BijOn.finite_iff_finite hbij).2 Set.finite_univ, ?_⟩
  have hcard : (q ⁻¹' {y}).ncard = (Set.univ : Set (Fin n)).ncard :=
    Set.ncard_congr (s := q ⁻¹' {y}) (t := (Set.univ : Set (Fin n)))
      (fun x _ => p x)
      (fun _ _ => trivial)
      (fun _ _ ha hb he => hbij.injOn ha hb he)
      (fun b hb => by
        obtain ⟨a, ha, hab⟩ := hbij.surjOn hb
        exact ⟨a, ha, hab⟩)
  exact hcard.trans ((Set.ncard_univ (Fin n)).trans (Nat.card_fin n))

/-- The same cardinality result uses nonemptiness of the actual class as its premise. -/
theorem placeCoord_nonempty_fiber_cardinality {X Q : Type*} {q : X → Q} {n : ℕ}
    {p : X → Fin n} (hp : p ∈ PlaceCoordinates.PlaceCoord q n)
    (y : Q) (hy : (q ⁻¹' {y}).Nonempty) :
    (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard = n := by
  obtain ⟨x, hx⟩ := hy
  exact placeCoord_fiber_cardinality hp y ⟨x, hx⟩

/-- The constant observer on Fin n has a place coordinate, including at n = 0. -/
theorem placeCoord_const_nonempty (n : ℕ) :
    (PlaceCoordinates.PlaceCoord (fun _ : Fin n => ()) n).Nonempty :=
  ⟨id, PlaceCoordinates.placeCoord_const_id n⟩

/- The first unit supplies the cardinality direction. The next unit constructs a coordinate. -/

/-!
## Unit 2: construction and the exact existence criterion

The finite-class and equal-cardinality premises are ORIGINAL_FINAL_ASSUMPTION.
The injective coordinate is INDEPENDENTLY_PROVED in PlaceCoordinates.
Finite surjectivity follows from the equal-cardinality theorem in pinned Mathlib.
The empty-source and zero-value cases require no nonempty-source premise.
-/

/-- Finite attained classes of size n admit a place coordinate with n values. -/
theorem placeCoord_nonempty_of_fiber_cardinality {X Q : Type*}
    (q : X → Q) (n : ℕ)
    (hfin : ∀ y ∈ Set.range q, (q ⁻¹' {y}).Finite)
    (hcard : ∀ y ∈ Set.range q, (q ⁻¹' {y}).ncard = n) :
    (PlaceCoordinates.PlaceCoord q n).Nonempty := by
  classical
  have hbounded : ∀ y : Q, (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard ≤ n := by
    intro y
    by_cases hy : y ∈ Set.range q
    · exact ⟨hfin y hy, (hcard y hy).le⟩
    · have hempty : q ⁻¹' {y} = (∅ : Set X) := by
        ext x
        constructor
        · intro hx
          exact hy ⟨x, hx⟩
        · intro hx
          exact False.elim hx
      rw [hempty, Set.ncard_empty]
      exact ⟨Set.finite_empty, Nat.zero_le n⟩
  obtain ⟨p, hp⟩ :=
    (PlaceCoordinates.exists_place_coordinate_iff q n).2 hbounded
  refine ⟨p, ?_⟩
  intro y hy
  have hinj : Set.InjOn p (q ⁻¹' {y}) := by
    intro a ha b hb hab
    apply hp
    have ha' : q a = y := ha
    have hb' : q b = y := hb
    exact Prod.ext (ha'.trans hb'.symm) hab
  refine ⟨?_, hinj, ?_⟩
  · intro _ _
    trivial
  · intro k hk
    have hcod : (Set.univ : Set (Fin n)).ncard = n :=
      (Set.ncard_univ (Fin n)).trans (Nat.card_fin n)
    have hle : (Set.univ : Set (Fin n)).ncard ≤ (q ⁻¹' {y}).ncard :=
      (hcod.trans (hcard y hy).symm).le
    obtain ⟨x, hx, hkx⟩ :=
      Set.surj_on_of_inj_on_of_ncard_le
        (s := q ⁻¹' {y}) (t := (Set.univ : Set (Fin n)))
        (fun x _ => p x)
        (fun _ _ => trivial)
        (fun _ _ ha hb he => hinj ha hb he)
        hle Set.finite_univ k hk
    exact ⟨x, hx, hkx.symm⟩

/-- The E2 goal holds on the original observer and on every finite attained class. -/
theorem placeExistenceGoal {X Q : Type*} (q : X → Q) (n : ℕ) :
    PlaceExistenceGoal q n := by
  intro hfin
  constructor
  · rintro ⟨p, hp⟩ y hy
    exact (placeCoord_fiber_cardinality hp y hy).2
  · intro hcard
    exact placeCoord_nonempty_of_fiber_cardinality q n hfin hcard

/-- The criterion also characterizes existence directly by the nonempty fibers. -/
theorem placeCoord_nonempty_iff_finite_fiber_cardinality
    {X Q : Type*} (q : X → Q) (n : ℕ) :
    (PlaceCoordinates.PlaceCoord q n).Nonempty ↔
      ∀ y : Q, (q ⁻¹' {y}).Nonempty →
        (q ⁻¹' {y}).Finite ∧ (q ⁻¹' {y}).ncard = n := by
  constructor
  · rintro ⟨p, hp⟩ y hy
    exact placeCoord_nonempty_fiber_cardinality hp y hy
  · intro h
    apply placeCoord_nonempty_of_fiber_cardinality q n
    · rintro y ⟨x, hx⟩
      exact (h y ⟨x, hx⟩).1
    · rintro y ⟨x, hx⟩
      exact (h y ⟨x, hx⟩).2

/-- An empty source admits a place coordinate for every number of values. -/
theorem placeCoord_nonempty_of_isEmpty {X Q : Type*} [IsEmpty X]
    (q : X → Q) (n : ℕ) :
    (PlaceCoordinates.PlaceCoord q n).Nonempty := by
  refine ⟨fun x => isEmptyElim x, ?_⟩
  rintro _ ⟨x, _⟩
  exact isEmptyElim x

/-- A place coordinate with zero values exists exactly when the source is empty. -/
theorem placeCoord_zero_nonempty_iff {X Q : Type*} (q : X → Q) :
    (PlaceCoordinates.PlaceCoord q 0).Nonempty ↔ IsEmpty X := by
  constructor
  · rintro ⟨p, _⟩
    exact ⟨fun x => Fin.elim0 (p x)⟩
  · intro hX
    letI : IsEmpty X := hX
    exact placeCoord_nonempty_of_isEmpty q 0

end OperatorKO7.Meta.BoundaryObserver.PlaceExistence
