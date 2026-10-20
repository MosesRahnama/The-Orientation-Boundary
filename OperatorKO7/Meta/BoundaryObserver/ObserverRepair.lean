import OperatorKO7.Meta.LicensedBoundaryCalculus.BoundaryCompletion
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# All maximal stable repairs

A repair may remove transitions and initially admissible states. It never adds either.
The order retains both coordinates. The classification is valid on arbitrary universe-zero types;
only the deletion counts require finiteness. This is not a theorem that equal costs imply equal repairs.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryObserver.ObserverRepair

open OperatorKO7.Meta.LicensedBoundaryCalculus
open OperatorKO7.Meta.DistinctionBoundary.PersistentLicense

/-- No stable repair retains strictly more transitions or states without losing either. -/
def MaximalRepair {X : Type} (R : X → X → Prop) (P : X → Prop) (A : RepairSystem X) : Prop :=
  IsStableRepair R P A ∧
    ∀ B, IsStableRepair R P B → A ≤ B → B ≤ A

/-- Every stable candidate lies below the greatest invariant predicate for its own dynamics. -/
theorem stable_pred_le_box {X : Type} (R : X → X → Prop) (P : X → Prop)
    (A : RepairSystem X) (hA : IsStableRepair R P A) : PredicateLE A.pred (Box A.rel P) := by
  intro x hx
  exact box_greatest (fun y hy => hA.2.1 y hy)
    (preserves_to_forwardInvariant hA.2.2) hx

/-- Maximality forces the relation coordinate to retain every edge safe for its predicate. -/
theorem maximal_rel_saturated {X : Type} (R : X → X → Prop) (P : X → Prop)
    (A : RepairSystem X) (hA : MaximalRepair R P A) : A.rel = SafeRel R A.pred := by
  let B : RepairSystem X := ⟨SafeRel R A.pred, A.pred⟩
  have hB : IsStableRepair R P B :=
    ⟨safeRel_subset R A.pred, hA.1.2.1, safeRel_preserves R A.pred⟩
  have hAB : A ≤ B := ⟨safeRel_greatest hA.1.1 hA.1.2.2, fun _ h => h⟩
  have hBA := hA.2 B hB hAB
  funext x y
  exact propext ⟨fun h => hAB.1 x y h, fun h => hBA.1 x y h⟩

/-- Maximality forces the state coordinate to retain every state persistently safe for its relation. -/
theorem maximal_pred_saturated {X : Type} (R : X → X → Prop) (P : X → Prop)
    (A : RepairSystem X) (hA : MaximalRepair R P A) : A.pred = Box A.rel P := by
  let B : RepairSystem X := ⟨A.rel, Box A.rel P⟩
  have hB : IsStableRepair R P B := by
    refine ⟨hA.1.1, fun _ h => h.holds, ?_⟩
    intro x y hxy hx
    exact box_forwardInvariant hx (Relation.ReflTransGen.single hxy)
  have hAB : A ≤ B := ⟨fun _ _ h => h, stable_pred_le_box R P A hA.1⟩
  have hBA := hA.2 B hB hAB
  funext x
  exact propext ⟨fun h => hAB.2 x h, fun h => hBA.2 x h⟩

/-- Simultaneous saturation is also sufficient, not only a necessary local condition. -/
theorem saturated_is_maximal {X : Type} (R : X → X → Prop) (P : X → Prop)
    (A : RepairSystem X) (hA : IsStableRepair R P A)
    (hrel : A.rel = SafeRel R A.pred) (hpred : A.pred = Box A.rel P) :
    MaximalRepair R P A := by
  refine ⟨hA, ?_⟩
  intro B hB hAB
  have hpredBA : PredicateLE B.pred A.pred := by
    intro x hx
    rw [hpred]
    apply box_greatest (fun y hy => hB.2.1 y hy) _ hx
    apply preserves_to_forwardInvariant
    intro y z hyz hy
    exact hB.2.2 y z (hAB.1 y z hyz) hy
  refine ⟨?_, hpredBA⟩
  intro x y hxy
  rw [hrel]
  exact ⟨hB.1 x y hxy, fun hx => hpredBA y (hB.2.2 x y hxy (hAB.2 x hx))⟩

/-- Complete characterization of the stable-repair frontier. -/
theorem maximal_iff_saturated {X : Type} (R : X → X → Prop) (P : X → Prop)
    (A : RepairSystem X) :
    MaximalRepair R P A ↔ IsStableRepair R P A ∧
      A.rel = SafeRel R A.pred ∧ A.pred = Box A.rel P := by
  constructor
  · intro h
    exact ⟨h.1, maximal_rel_saturated R P A h, maximal_pred_saturated R P A h⟩
  · rintro ⟨hs, hr, hp⟩
    exact saturated_is_maximal R P A hs hr hp

/-- Both previously constructed endpoints are globally maximal in the two-coordinate order. -/
theorem endpoint_repairs_maximal {X : Type} (R : X → X → Prop) (P : X → Prop) :
    MaximalRepair R P (dynamicsRepair R P) ∧ MaximalRepair R P (predicateRepair R P) := by
  constructor
  · apply saturated_is_maximal R P _ (dynamicsRepair_stable R P)
    · rfl
    · exact (box_safeRel_eq R P).symm
  · apply saturated_is_maximal R P _ (predicateRepair_stable R P)
    · exact (safeRel_box_eq R P).symm
    · rfl

/-- Distinct maximal repairs never dominate each other. -/
theorem maximal_repairs_antichain {X : Type} (R : X → X → Prop) (P : X → Prop)
    (A B : RepairSystem X) (hA : MaximalRepair R P A) (hB : MaximalRepair R P B)
    (hle : A ≤ B) : A = B := by
  exact le_antisymm hle (hA.2 B hB.1 hle)

noncomputable def stateCount {X : Type} [Fintype X] (P : X → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter P).card

noncomputable def edgeCount {X : Type} [Fintype X] (R : X → X → Prop) : ℕ :=
  stateCount (fun p : X × X => R p.1 p.2)

/-- Separate costs count deleted transitions and deleted admissible states. -/
noncomputable def deletionCost {X : Type} [Fintype X]
    (R : X → X → Prop) (P : X → Prop) (A : RepairSystem X) : ℕ × ℕ :=
  (edgeCount R - edgeCount A.rel, stateCount P - stateCount A.pred)

theorem stateCount_mono {X : Type} [Fintype X] {P Q : X → Prop}
    (h : PredicateLE P Q) : stateCount P ≤ stateCount Q := by
  classical
  apply Finset.card_le_card
  intro x hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩

theorem deletionCost_antitone {X : Type} [Fintype X]
    (R : X → X → Prop) (P : X → Prop) (A B : RepairSystem X) (h : A ≤ B) :
    (deletionCost R P B).1 ≤ (deletionCost R P A).1 ∧
      (deletionCost R P B).2 ≤ (deletionCost R P A).2 := by
  have he : edgeCount A.rel ≤ edgeCount B.rel :=
    stateCount_mono (fun xy hxy => h.1 xy.1 xy.2 hxy)
  have hp := stateCount_mono h.2
  dsimp [deletionCost]
  omega

/-- The frontier contains incomparable repairs on one concrete boundary-crossing system. -/
theorem crossing_has_distinct_maximal_repairs :
    MaximalRepair failureFixtureStep failureFixturePredicate
      (dynamicsRepair failureFixtureStep failureFixturePredicate) ∧
    MaximalRepair failureFixtureStep failureFixturePredicate
      (predicateRepair failureFixtureStep failureFixturePredicate) ∧
    dynamicsRepair failureFixtureStep failureFixturePredicate ≠
      predicateRepair failureFixtureStep failureFixturePredicate := by
  refine ⟨(endpoint_repairs_maximal _ _).1, (endpoint_repairs_maximal _ _).2, ?_⟩
  intro he
  exact fixture_endpoint_repairs_incomparable.2 (le_of_eq he)


/-! ## Exact existence of a greatest repair

Greatestness compares with every stable repair, without an extra comparability premise.
-/

/-- A stable repair that retains both coordinates of every stable candidate. -/
def GreatestRepair {X : Type*} (R : X → X → Prop) (P : X → Prop)
    (A : RepairSystem X) : Prop :=
  IsStableRepair R P A ∧ ∀ B, IsStableRepair R P B → B ≤ A

/-- The two independent stable candidates force a greatest repair to retain the raw pair. -/
theorem greatestRepair_eq_raw {X : Type*} (R : X → X → Prop) (P : X → Prop)
    (A : RepairSystem X) (hA : GreatestRepair R P A) : A = ⟨R, P⟩ := by
  apply le_antisymm
  · exact ⟨hA.1.1, hA.1.2.1⟩
  · have hEdges : IsStableRepair R P (⟨R, fun _ => False⟩ : RepairSystem X) := by
      refine ⟨fun _ _ h => h, fun _ h => h.elim, ?_⟩
      exact fun _ _ _ h => h.elim
    have hStates : IsStableRepair R P (⟨fun _ _ => False, P⟩ : RepairSystem X) := by
      refine ⟨fun _ _ h => h.elim, fun _ h => h, ?_⟩
      exact fun _ _ h _ => h.elim
    exact ⟨(hA.2 _ hEdges).1, (hA.2 _ hStates).2⟩

/-- Greatestness specifies the repair itself and the exact preservation condition. -/
theorem greatestRepair_iff_eq_raw_and_preserves {X : Type*}
    (R : X → X → Prop) (P : X → Prop) (A : RepairSystem X) :
    GreatestRepair R P A ↔ A = ⟨R, P⟩ ∧ Preserves R P := by
  constructor
  · intro h
    have he := greatestRepair_eq_raw R P A h
    refine ⟨he, ?_⟩
    have hp := h.1.2.2
    simpa only [he] using hp
  · rintro ⟨rfl, hp⟩
    exact ⟨⟨fun _ _ h => h, fun _ h => h, hp⟩, fun _ h => ⟨h.1, h.2.1⟩⟩

/-- A greatest stable repair exists exactly when no repair was needed for preservation. -/
theorem exists_greatestRepair_iff_preserves {X : Type*}
    (R : X → X → Prop) (P : X → Prop) :
    (∃ A, GreatestRepair R P A) ↔ Preserves R P := by
  constructor
  · rintro ⟨A, hA⟩
    exact ((greatestRepair_iff_eq_raw_and_preserves R P A).mp hA).2
  · intro hp
    exact ⟨⟨R, P⟩, (greatestRepair_iff_eq_raw_and_preserves R P _).mpr ⟨rfl, hp⟩⟩

/-- A single genuine boundary crossing excludes a greatest stable repair. -/
theorem boundaryEdge_no_greatestRepair {X : Type*} {R : X → X → Prop} {P : X → Prop}
    {x y : X} (h : BoundaryEdge R P x y) : ¬ ∃ A, GreatestRepair R P A := by
  rw [exists_greatestRepair_iff_preserves]
  intro hp
  exact h.2.2 (hp x y h.1 h.2.1)

/-- The existing crossing fixture realizes the nonexistence branch. -/
theorem crossing_no_greatestRepair :
    ¬ ∃ A, GreatestRepair failureFixtureStep failureFixturePredicate A :=
  boundaryEdge_no_greatestRepair
    (R := failureFixtureStep) (P := failureFixturePredicate)
    (x := FailureFixtureState.safe) (y := FailureFixtureState.failed)
    ⟨⟨rfl, rfl⟩, rfl, by intro h; cases h⟩

/-- A universally permitted system realizes the existence branch on every carrier. -/
theorem universal_relation_total_predicate_greatest {X : Type*} :
    GreatestRepair (fun _ _ : X => True) (fun _ : X => True)
      ⟨fun _ _ => True, fun _ => True⟩ := by
  apply (greatestRepair_iff_eq_raw_and_preserves _ _ _).mpr
  exact ⟨rfl, fun _ _ _ _ => trivial⟩

#check @GreatestRepair
#check @greatestRepair_eq_raw
#check @greatestRepair_iff_eq_raw_and_preserves
#check @exists_greatestRepair_iff_preserves
#check @boundaryEdge_no_greatestRepair
#check @crossing_no_greatestRepair
#check @universal_relation_total_predicate_greatest

#print axioms GreatestRepair
#print axioms greatestRepair_eq_raw
#print axioms greatestRepair_iff_eq_raw_and_preserves
#print axioms exists_greatestRepair_iff_preserves
#print axioms boundaryEdge_no_greatestRepair
#print axioms crossing_no_greatestRepair
#print axioms universal_relation_total_predicate_greatest

end OperatorKO7.Meta.BoundaryObserver.ObserverRepair
